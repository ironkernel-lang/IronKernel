namespace IronKernel

/// Runtime operations shared by dynamically and statically generated code.
module RuntimeDispatch =

    open System
    open System.IO
    open System.Runtime.CompilerServices
    open System.Text.Json
    open System.Threading
    open Ast
    open Errors
    open Eval
    open SymbolTable

    let appNamed env cont name (operands: LispVal[]) : ThrowsError<LispVal> =
        match getVar env name with
        | Choice1Of2 error -> throwError error
        | Choice2Of2 combiner -> operate env cont combiner (Array.toList operands)

    /// Monomorphic inline cache for a compiled `(name operand ...)` call site.
    ///
    /// The cache is valid while the invoking environment is the same instance,
    /// every frame scanned during the original resolution still holds the same
    /// number of bindings (frames only gain bindings, so an unchanged count
    /// proves no new definition shadows the resolved cell), and the resolved
    /// cell's version is unchanged (redefinition bumps it). Any mismatch falls
    /// back to full resolution and refills the cache.
    ///
    /// When the cached combiner is an applicative over an ordinary combiner and
    /// every operand is a variable or a self-evaluating value, arguments are
    /// evaluated eagerly instead of through the CPS argument chain: evaluating
    /// a variable or literal cannot capture a continuation, so the shortcut is
    /// unobservable. Operatives and unknown shapes keep raw-operand dispatch.
    type NamedCallSite(name: string, operands: LispVal list) =
        let simpleOperands =
            operands
            |> List.forall (function
                | List (_ :: _) -> false
                | _ -> true)

        let mutable cachedEnv : LispVal = Nil
        let mutable cachedPath : SymbolTable.VisitedFrame[] = null
        let mutable cachedCell : BindingCell = Unchecked.defaultof<BindingCell>
        let mutable cachedVersion = 0L
        let mutable cachedCombiner : LispVal = Nil
        let mutable eagerUnderlying : LispVal voption = ValueNone
        let debugGate = obj ()
        let mutable debugEntryCount = 0
        let mutable debugRefillCount = 0
        let mutable debugExitCount = 0

        let objectId (value: obj) =
            if isNull value then 0 else RuntimeHelpers.GetHashCode(value)

        let debugLog hypothesisId location message (data: obj) =
            let payload =
                JsonSerializer.Serialize(
                    {| hypothesisId = hypothesisId
                       location = location
                       message = message
                       data = data
                       timestamp = DateTimeOffset.UtcNow.ToUnixTimeMilliseconds() |})
            lock debugGate (fun () -> File.AppendAllText("/opt/cursor/logs/debug.log", payload + "\n"))

        let classifyEager combiner =
            if not simpleOperands then ValueNone
            else
                match combiner with
                | Applicative underlying ->
                    match underlying with
                    | PrimitiveOperative _
                    | CompiledCombiner _
                    | Operative _
                    | ContractedCombiner _ -> ValueSome underlying
                    | _ -> ValueNone
                | _ -> ValueNone

        let cacheValid env =
            let initialCachedEnv = cachedEnv
            let envMatched = obj.ReferenceEquals(env, initialCachedEnv)
            let valid =
                envMatched
                && cachedCell.state.version = cachedVersion
                && (let mutable consistent = true
                    let mutable index = 0
                    while consistent && index < cachedPath.Length do
                        let entry = cachedPath.[index]
                        consistent <- entry.frame.bindings.Count = entry.bindingCount
                        index <- index + 1
                    consistent)
            // #region agent log
            if envMatched && not (obj.ReferenceEquals(initialCachedEnv, cachedEnv)) then
                debugLog "D" "RuntimeDispatch.fs:cacheValid" "cache environment changed during validation"
                    (box {| threadId = Environment.CurrentManagedThreadId
                            invokeEnvId = objectId env
                            initialCachedEnvId = objectId initialCachedEnv
                            finalCachedEnvId = objectId cachedEnv
                            valid = valid |})
            // #endregion
            valid

        let rec evaluateSimpleOperands env evaluated remaining =
            match remaining with
            | [] -> Choice2Of2(List.rev evaluated)
            | Atom variable :: rest ->
                match getVar env variable with
                | Choice2Of2 value -> evaluateSimpleOperands env (value :: evaluated) rest
                | Choice1Of2 error -> Choice1Of2 error
            | value :: rest -> evaluateSimpleOperands env (value :: evaluated) rest

        let dispatch env cont =
            let dispatchCachedEnv = cachedEnv
            let dispatchCachedCell = cachedCell
            let dispatchEager = eagerUnderlying
            // #region agent log
            if not (obj.ReferenceEquals(env, dispatchCachedEnv)) then
                debugLog "B" "RuntimeDispatch.fs:dispatch" "dispatch cache belongs to another environment"
                    (box {| threadId = Environment.CurrentManagedThreadId
                            invokeEnvId = objectId env
                            cachedEnvId = objectId dispatchCachedEnv
                            cachedCellId = if isNull (box dispatchCachedCell) then -1L else dispatchCachedCell.id
                            eagerId =
                                match dispatchEager with
                                | ValueSome underlying -> objectId underlying
                                | ValueNone -> 0 |})
            // #endregion
            match dispatchEager with
            | ValueSome underlying ->
                match evaluateSimpleOperands env [] operands with
                | Choice1Of2 error -> throwError error
                | Choice2Of2 args -> operate env cont underlying args
            | ValueNone -> operate env cont cachedCombiner operands

        member _.Invoke(env: LispVal, cont: LispVal) : ThrowsError<LispVal> =
            // #region agent log
            if Interlocked.Increment(&debugEntryCount) <= 16 then
                debugLog "A" "RuntimeDispatch.fs:Invoke:entry" "named call-site invocation entered"
                    (box {| threadId = Environment.CurrentManagedThreadId
                            name = name
                            invokeEnvId = objectId env
                            cachedEnvId = objectId cachedEnv
                            hasCachedPath = not (isNull cachedPath) |})
            // #endregion
            let result =
                if not (isNull cachedPath) && cacheValid env then
                    dispatch env cont
                else
                    match SymbolTable.resolveBindingCellWithPath env name with
                    | ValueNone -> throwError (UnboundVar("Getting an unbound variable", name))
                    | ValueSome(cell, visitedPath) ->
                        let state = cell.state
                        // #region agent log
                        if Interlocked.Increment(&debugRefillCount) <= 16 then
                            debugLog "A" "RuntimeDispatch.fs:Invoke:resolved" "cache refill resolved invocation binding"
                                (box {| threadId = Environment.CurrentManagedThreadId
                                        invokeEnvId = objectId env
                                        resolvedCellId = cell.id
                                        resolvedValueId = objectId state.value
                                        resolvedEagerId =
                                            match classifyEager state.value with
                                            | ValueSome underlying -> objectId underlying
                                            | ValueNone -> 0
                                        pathLength = visitedPath.Length |})
                        // #endregion
                        cachedEnv <- env
                        cachedPath <- visitedPath
                        cachedCell <- cell
                        cachedVersion <- state.version
                        cachedCombiner <- state.value
                        eagerUnderlying <- classifyEager state.value
                        // #region agent log
                        if not (obj.ReferenceEquals(env, cachedEnv)) || not (obj.ReferenceEquals(cell, cachedCell)) then
                            debugLog "B" "RuntimeDispatch.fs:Invoke:published" "cache refill was overwritten before dispatch"
                                (box {| threadId = Environment.CurrentManagedThreadId
                                        invokeEnvId = objectId env
                                        resolvedCellId = cell.id
                                        cachedEnvId = objectId cachedEnv
                                        cachedCellId = if isNull (box cachedCell) then -1L else cachedCell.id |})
                        // #endregion
                        dispatch env cont
            // #region agent log
            if Interlocked.Increment(&debugExitCount) <= 16 then
                debugLog "C" "RuntimeDispatch.fs:Invoke:exit" "named call-site invocation exited"
                    (box {| threadId = Environment.CurrentManagedThreadId
                            invokeEnvId = objectId env
                            resultKind =
                                match result with
                                | Choice1Of2 _ -> "error"
                                | Choice2Of2 (Obj (:? int)) -> "int"
                                | Choice2Of2 _ -> "other" |})
            // #endregion
            result

    type GeneratedFunc = Func<LispVal, LispVal, ThrowsError<LispVal>>

    let runOperate env cont (operator: GeneratedFunc) (operands: LispVal[]) =
        match operator.Invoke(env, newContinuation env) with
        | Choice1Of2 error -> throwError error
        | Choice2Of2 combiner -> operate env cont combiner (Array.toList operands)

    let runIf env cont (condition: GeneratedFunc) (consequent: GeneratedFunc) (alternative: GeneratedFunc) =
        match condition.Invoke(env, newContinuation env) with
        | Choice2Of2 (Bool true) -> consequent.Invoke(env, cont)
        | Choice2Of2 (Bool false) -> alternative.Invoke(env, cont)
        | Choice2Of2 found -> throwError (TypeMismatch("bool", found))
        | Choice1Of2 error -> throwError error

    let runDefine env cont name (rhs: GeneratedFunc) =
        match rhs.Invoke(env, newContinuation env) with
        | Choice1Of2 error -> throwError error
        | Choice2Of2 value ->
            match defineVar env name value with
            | Choice1Of2 error -> throwError error
            | Choice2Of2 _ -> continueEval env cont Inert

    let runSequence env cont (forms: GeneratedFunc[]) =
        let mutable index = 0
        let mutable result = Choice2Of2 Inert
        let mutable running = true
        while index < forms.Length && running do
            let nextCont = if index = forms.Length - 1 then cont else newContinuation env
            result <- forms.[index].Invoke(env, nextCont)
            running <- match result with Choice2Of2 _ -> true | Choice1Of2 _ -> false
            index <- index + 1
        if forms.Length = 0 then continueEval env cont Inert else result

    let runGuard env cont name expectedIdentity (specialized: GeneratedFunc) (fallback: GeneratedFunc) =
        if bindingHasPrimitiveIdentity env name expectedIdentity then specialized.Invoke(env, cont)
        else fallback.Invoke(env, cont)

    let runLocated env cont span sourceLine (body: GeneratedFunc) =
        match body.Invoke(env, cont) with
        | Choice1Of2 (LocatedError _ as error) -> throwError error
        | Choice1Of2 error -> throwError (LocatedError(span, sourceLine, error))
        | Choice2Of2 value -> Choice2Of2 value