namespace IronKernel

/// Runtime operations shared by dynamically and statically generated code.
module RuntimeDispatch =

    open System
    open System.Threading
    open Ast
    open Errors
    open Eval
    open SymbolTable

    /// Generated code returns `Step` so it runs inside the caller's trampoline
    /// instead of starting a nested one. Nesting would cost CLR stack on every
    /// Kernel tail call, trap escaping continuations behind a collapsed result,
    /// and turn `Await` into a blocking wait. See ADR 0004.
    /// A name that resolves to nothing may still be CLR call sugar. The interpreter
    /// has always tried the binding first and the rewrite second; since ADR 0008
    /// step 2 the compiled paths do the same, instead of the analyzer deciding it
    /// from the environment it happened to compile against.
    let private operateNamed env cont name operands =
        match getVar env name with
        | Choice2Of2 combiner -> bounceOperate env cont combiner operands
        | Choice1Of2 error ->
            match ClrSugar.tryRewrite name operands with
            | Some rewritten -> bounceEval env cont rewritten
            | None -> signal cont error

    let appNamed env cont name (operands: LispVal[]) : Step =
        operateNamed env cont name (Array.toList operands)

    /// One call site's resolved binding, immutable once constructed so that it can
    /// be published to other threads with a single reference write.
    [<Sealed; AllowNullLiteral>]
    type ResolvedCallSite
        (
            resolution: SymbolTable.ChainResolution,
            version: int64,
            combiner: LispVal,
            eagerUnderlying: LispVal voption
        ) =
        member _.Resolution = resolution
        member _.Version = version
        member _.Combiner = combiner
        member _.EagerUnderlying = eagerUnderlying

    /// Monomorphic inline cache for a compiled `(name operand ...)` call site.
    ///
    /// The cache is valid while resolving the name from the invoking environment
    /// would still reach the same frame -- every nearer frame still lacks the name
    /// and the owning frame is the same object -- and the resolved cell's version is
    /// unchanged (redefinition bumps it). Any mismatch falls back to full resolution
    /// and refills the cache.
    ///
    /// Validating the chain rather than the environment's identity is what makes the
    /// cache usable inside a procedure body, where application binds parameters in a
    /// fresh frame and no two calls ever share an environment instance. Chains that
    /// are not a simple single-parent walk are dispatched without caching.
    ///
    /// When the cached combiner is an applicative over an ordinary combiner and
    /// every operand is a variable or a self-evaluating value, arguments are
    /// evaluated eagerly instead of through the CPS argument chain: evaluating
    /// a variable or literal cannot capture a continuation, so the shortcut is
    /// unobservable. Operatives and unknown shapes keep raw-operand dispatch.
    type NamedCallSite(name: string, operands: LispVal list) =
        let simpleOperands =
            operands
            // A pair is a combination that would need evaluating, whatever its shape.
            // Asking through the list pattern walked each operand's whole structure.
            |> List.forall (function
                | Pair _ -> false
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
            resolved.Resolution.cell.state.version = resolved.Version
            && SymbolTable.chainResolutionHolds env name resolved.Resolution

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
                | Choice1Of2 error -> signal cont error
                | Choice2Of2 args -> bounceOperate env cont underlying args
            | ValueNone -> bounceOperate env cont resolved.Combiner operands

        member _.Invoke(env: LispVal, cont: LispVal) : Step =
            let cached = Volatile.Read(&cache)
            if not (isNull cached) && cacheValid cached env then
                dispatch cached env cont
            else
                match SymbolTable.tryResolveAlongChain env name with
                | ValueSome resolution ->
                    let state = resolution.cell.state
                    let resolved =
                        ResolvedCallSite(
                            resolution,
                            state.version,
                            state.value,
                            classifyEager state.value)
                    Volatile.Write(&cache, resolved)
                    dispatch resolved env cont
                // Not a simple chain: dispatch without caching rather than storing a
                // snapshot that could never be revalidated.
                | ValueNone -> operateNamed env cont name operands

    type GeneratedFunc = Func<LispVal, LispVal, Step>

    /// Sub-evaluations that must produce a *value* before the caller can proceed
    /// resume through `makeCPS` rather than collapsing a nested trampoline. The
    /// continuation handed to the callback is the caller's own, so the final form
    /// of each construct stays in tail position.
    let runOperate env cont (operator: GeneratedFunc) (operands: LispVal[]) =
        operator.Invoke(
            env,
            makeCPS env cont (fun e c combiner _ ->
                bounceOperate e c combiner (Array.toList operands)))

    let runIf env cont (condition: GeneratedFunc) (consequent: GeneratedFunc) (alternative: GeneratedFunc) =
        condition.Invoke(
            env,
            makeCPS env cont (fun e c value _ ->
                match value with
                | Bool true -> consequent.Invoke(e, c)
                | Bool false -> alternative.Invoke(e, c)
                | found -> signal c (TypeMismatch("bool", found))))

    let runDefine env cont name (rhs: GeneratedFunc) =
        rhs.Invoke(
            env,
            makeCPS env cont (fun e c value _ ->
                match defineVar e name value with
                | Choice1Of2 error -> signal c error
                | Choice2Of2 _ -> bounceContinue e c Inert))

    let runSequence env cont (forms: GeneratedFunc[]) =
        if forms.Length = 0 then bounceContinue env cont Inert
        else
            let rec step index e c =
                if index = forms.Length - 1 then forms.[index].Invoke(e, c)
                else forms.[index].Invoke(e, makeCPS e c (fun se sc _ _ -> step (index + 1) se sc))
            step 0 env cont

    let runGuard env cont name expectedIdentity (specialized: GeneratedFunc) (fallback: GeneratedFunc) =
        if bindingHasPrimitiveIdentity env name expectedIdentity then specialized.Invoke(env, cont)
        else fallback.Invoke(env, cont)

    /// Attaches a source span to an error raised *while this form is evaluating*.
    ///
    /// Errors short-circuit the trampoline as `Done`, bypassing continuations, so
    /// the span has to be applied by inspecting the step chain rather than by a
    /// continuation frame. The chain a compiled form returns also covers whatever
    /// runs after it, because CPS hands the form the caller's own continuation.
    /// Attributing all of that to this span would make an operator's span swallow
    /// errors from the operands evaluated after it. Interpreting collapsed each
    /// sub-evaluation against a fresh continuation, which bounded the span
    /// naturally; `reached` restores that boundary by recording when control
    /// passes out of the form to `cont`.
    ///
    /// Each case rebuilds one layer and returns immediately, so the trampoline
    /// keeps its constant stack. An already-located error keeps its inner span.
    let runLocated env cont span sourceLine (body: GeneratedFunc) =
        let mutable reached = false
        let boundary =
            makeCPS env cont (fun e c value _ ->
                reached <- true
                bounceContinue e c value)
        let rec locate step =
            match step with
            | Done (Choice1Of2 (LocatedError _)) -> step
            | Done (Choice1Of2 error) ->
                if reached then step
                else Done(throwError (LocatedError(span, sourceLine, error)))
            | Done (Choice2Of2 _) -> step
            | More next -> More(fun () -> locate (next ()))
            | Await request ->
                Await
                    { register = request.register
                      resume = fun outcome -> locate (request.resume outcome) }
        locate (body.Invoke(env, boundary))