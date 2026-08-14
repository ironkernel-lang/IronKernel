namespace IronKernel

/// Runtime operations shared by dynamically and statically generated code.
module RuntimeDispatch =

    open System
    open System.Threading
    open Ast
    open Errors
    open Eval
    open SymbolTable

    let appNamed env cont name (operands: LispVal[]) : ThrowsError<LispVal> =
        match getVar env name with
        | Choice1Of2 error -> throwError error
        | Choice2Of2 combiner -> operate env cont combiner (Array.toList operands)

    /// One call site's resolved binding, immutable once constructed so that it can
    /// be published to other threads with a single reference write.
    [<Sealed; AllowNullLiteral>]
    type ResolvedCallSite
        (
            env: LispVal,
            path: SymbolTable.VisitedFrame[],
            cell: BindingCell,
            version: int64,
            combiner: LispVal,
            eagerUnderlying: LispVal voption
        ) =
        member _.Env = env
        member _.Path = path
        member _.Cell = cell
        member _.Version = version
        member _.Combiner = combiner
        member _.EagerUnderlying = eagerUnderlying

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

        /// The whole cache is one immutable snapshot behind a single reference so
        /// that a refill can never be observed half-applied. Publishing the parts
        /// separately let one caller validate its own environment and then
        /// dispatch a combiner another caller had already stored, invoking the
        /// wrong binding.
        let mutable cache : ResolvedCallSite = null

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

        let cacheValid (resolved: ResolvedCallSite) env =
            obj.ReferenceEquals(env, resolved.Env)
            && resolved.Cell.state.version = resolved.Version
            && (let path = resolved.Path
                let mutable consistent = true
                let mutable index = 0
                while consistent && index < path.Length do
                    let entry = path.[index]
                    consistent <- entry.frame.bindings.Count = entry.bindingCount
                    index <- index + 1
                consistent)

        let rec evaluateSimpleOperands env evaluated remaining =
            match remaining with
            | [] -> Choice2Of2(List.rev evaluated)
            | Atom variable :: rest ->
                match getVar env variable with
                | Choice2Of2 value -> evaluateSimpleOperands env (value :: evaluated) rest
                | Choice1Of2 error -> Choice1Of2 error
            | value :: rest -> evaluateSimpleOperands env (value :: evaluated) rest

        let dispatch (resolved: ResolvedCallSite) env cont =
            match resolved.EagerUnderlying with
            | ValueSome underlying ->
                match evaluateSimpleOperands env [] operands with
                | Choice1Of2 error -> throwError error
                | Choice2Of2 args -> operate env cont underlying args
            | ValueNone -> operate env cont resolved.Combiner operands

        member _.Invoke(env: LispVal, cont: LispVal) : ThrowsError<LispVal> =
            let cached = Volatile.Read(&cache)
            if not (isNull cached) && cacheValid cached env then
                dispatch cached env cont
            else
                match SymbolTable.resolveBindingCellWithPath env name with
                | ValueNone -> throwError (UnboundVar("Getting an unbound variable", name))
                | ValueSome(cell, visitedPath) ->
                    let state = cell.state
                    let resolved =
                        ResolvedCallSite(
                            env,
                            visitedPath,
                            cell,
                            state.version,
                            state.value,
                            classifyEager state.value)
                    Volatile.Write(&cache, resolved)
                    dispatch resolved env cont

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