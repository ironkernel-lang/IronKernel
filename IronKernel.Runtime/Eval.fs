namespace IronKernel

module Eval =
    
    open System.Threading
    open System.Threading.Tasks
    open Choice
    open Ast
    open Errors
    open SymbolTable
    open Capabilities
    open Contracts
    open ClrSugar

    /// Compiles an operative body to a list of compiled forms, one per body form.
    /// Installed by the tool: ADR 0002 keeps the compiler out of
    /// `IronKernel.Runtime`, so artifacts published without it simply keep
    /// interpreting bodies. Takes the operative's closure environment and its body.
    let mutable private bodyCompiler
        : (LispVal -> LispVal list -> (LispVal -> LispVal -> Step) list) option = None

    let configureBodyCompiler compile = bodyCompiler <- Some compile

    let inline ok (x: LispVal) : Step = Done (returnM x)
    let inline fail (e: LispError) : Step = Done (throwError e)
    let inline ofResult (r: ThrowsError<LispVal>) : Step = Done r

    let rec runAsync (step: Step) : Task<ThrowsError<LispVal>> =
        let mutable current = step
        let mutable running = true
        while running do
            match current with
            | More next -> current <- next ()
            | Done _
            | Await _ -> running <- false
        match current with
        | Done result -> Task.FromResult result
        | Await request ->
            let completion =
                TaskCompletionSource<ThrowsError<LispVal>>(
                    TaskCreationOptions.RunContinuationsAsynchronously)
            try
                request.register (fun outcome -> completion.TrySetResult(outcome) |> ignore)
            with ex ->
                completion.TrySetResult(throwError (ClrException ex)) |> ignore
            task {
                let! outcome = completion.Task.ConfigureAwait(false)
                return! runAsync (request.resume outcome)
            }
        | More _ -> failwith "unreachable trampoline state"

    let run (step: Step) : ThrowsError<LispVal> =
        runAsync step |> fun pending -> pending.GetAwaiter().GetResult()

    let private appendContinuationRecord left right =
        let traversed = System.Collections.Generic.List<ContinuationRecord * ContinuationType>()
        let mutable current = left
        let mutable appendable = true
        let mutable searching = true

        while searching do
            match current.nextCont with
            | None -> searching <- false
            | Some (Continuation(next, None, continuationType)) ->
                traversed.Add(current, continuationType)
                current <- next
            | Some _ ->
                appendable <- false
                searching <- false

        if not appendable then left
        else
            let mutable combined =
                { current with nextCont = Some (Continuation(right, None, Full)) }
            for index = traversed.Count - 1 downto 0 do
                let record, continuationType = traversed.[index]
                combined <-
                    { record with
                        nextCont = Some (Continuation(combined, None, continuationType)) }
            combined

    let findPrompt tag continuation =
        let records = System.Collections.Generic.List<ContinuationRecord>()
        let mutable currentContinuation = continuation
        let mutable matchingFrame = None
        let mutable searching = true

        while searching do
            match currentContinuation with
            | Continuation(current, Some frame, _) ->
                records.Add(current)
                if frame.tag = tag then
                    matchingFrame <- Some frame
                    searching <- false
                else
                    currentContinuation <- frame.parentCont
            | _ -> searching <- false

        match matchingFrame with
        | None -> None
        | Some frame ->
            let mutable combined = records.[records.Count - 1]
            for index = records.Count - 2 downto 0 do
                combined <- appendContinuationRecord records.[index] combined
            Some(combined, frame)

    /// The nearest keyed dynamic binding for `key`, looking outward from `continuation`
    /// (R-1RK 10.1.1). The chain is walked the way the evaluator walks it -- along
    /// `nextCont`, then into the metacontinuation's parent when a segment runs out --
    /// so a binding is visible for precisely the dynamic extent of the binder's call.
    let findDynamicBinding key continuation =
        let mutable current = continuation
        let mutable found = None
        let mutable searching = true
        while searching do
            match current with
            | Continuation (record, metaCont, ct) ->
                match record.currentCont with
                | Some (DynamicBinding(bindingKey, value)) when bindingKey = key ->
                    found <- Some value
                    searching <- false
                | _ ->
                    match record.nextCont with
                    | Some (Continuation (next, None, _)) ->
                        current <- Continuation (next, metaCont, ct)
                    | _ ->
                        match metaCont with
                        | Some frame -> current <- frame.parentCont
                        | None -> searching <- false
            | _ -> searching <- false
        found

    /// The records a continuation would return through, innermost first. R-1RK 7.1
    /// fixes a continuation's ancestors at the moment it is created, and this chain is
    /// exactly that set: walked the way the evaluator walks it, along nextCont and then
    /// into the metacontinuation's parent when a segment runs out.
    let continuationAncestry continuation =
        let records = System.Collections.Generic.List<ContinuationRecord>()
        let mutable current = continuation
        let mutable walking = true
        while walking do
            match current with
            | Continuation (record, metaCont, ct) ->
                records.Add record
                match record.nextCont with
                | Some (Continuation (next, None, _)) ->
                    current <- Continuation (next, metaCont, ct)
                | _ ->
                    match metaCont with
                    | Some frame -> current <- frame.parentCont
                    | None -> walking <- false
            | _ -> walking <- false
        List.ofSeq records

    /// Whether `record` is an ancestor of the continuation whose ancestry is `chain`,
    /// which is R-1RK 7.1's "the continuation is within the dynamic extent of record".
    /// Records are compared by identity: two continuations are the same continuation
    /// only if they are the same object.
    let withinExtent (chain: ContinuationRecord list) (record: ContinuationRecord) =
        chain |> List.exists (fun candidate -> obj.ReferenceEquals(candidate, record))

    let promptContinuation env parent tag handler =
        Continuation(
            { closure = env
              currentCont = None
              nextCont = None
              args = None },
            Some
                { parentCont = parent
                  tag = tag
                  handler = handler },
            Full)

    let rec continueEvalStep env cont value : Step =
        match env, cont with
        | Environment _, Continuation _ -> continueEvalValidStep env cont value
        | (Environment _), found -> fail (TypeMismatch("continuation", found))
        | found, _ -> fail (TypeMismatch("environment", found))

    and private continueEvalValidStep env cont value : Step =
        match cont with
        | Continuation ({ currentCont = None; nextCont = None }, None, _) ->
            ok value
        | Continuation ({ closure = e; currentCont = None; nextCont = None }, Some frame, _) ->
            More (fun () -> continueEvalStep e frame.parentCont value)
        | Continuation ({ closure = e; currentCont = None; nextCont = Some (Continuation (cr, None, _)) }, metaCont, ct) ->
            More (fun () -> continueEvalStep e (Continuation (cr, metaCont, ct)) value)
        | Continuation ({ closure = e; currentCont = Some (NativeCode { cont = f; args = args }); nextCont = Some (Continuation (ncr, None, _)) }, metaCont, ct) ->
            More (fun () -> f e (Continuation (ncr, metaCont, ct)) value args)
        | Continuation ({ closure = e; currentCont = Some (KernelCode cBody); nextCont = nextCont }, metaCont, ct) ->
            match cBody with
            | [] -> finishDeferredBody e nextCont metaCont ct value
            | p :: tail ->
                More (fun () ->
                    evalStep e
                        (Continuation ({ closure = e; currentCont = Some (KernelCode tail); nextCont = nextCont; args = None }, metaCont, ct))
                        p)
        // Same rule as KernelCode: the head form runs against a continuation holding
        // the remaining forms, so the final form inherits `nextCont` and stays in
        // tail position.
        | Continuation ({ closure = e; currentCont = Some (CompiledCode forms); nextCont = nextCont }, metaCont, ct) ->
            match forms with
            | [] -> finishDeferredBody e nextCont metaCont ct value
            | form :: tail ->
                More (fun () ->
                    form
                        e
                        (Continuation ({ closure = e; currentCont = Some (CompiledCode tail); nextCont = nextCont; args = None }, metaCont, ct)))
        // A keyed dynamic binding (R-1RK 10.1.1) holds no code. Returning through it
        // is what ends the binder's dynamic extent, so it simply hands the value
        // outward exactly as an exhausted body does.
        | Continuation ({ closure = e; currentCont = Some (DynamicBinding _); nextCont = nextCont }, metaCont, ct) ->
            finishDeferredBody e nextCont metaCont ct value
        // R-1RK 7.2.4: "in the absence of abnormal passing, the inner and outer
        // continuations each have the same behavior as continuation". Guards only
        // affect abnormal passes, so a normal receipt here is a pass-through.
        | Continuation ({ closure = e; currentCont = Some (GuardBarrier _); nextCont = nextCont }, metaCont, ct) ->
            finishDeferredBody e nextCont metaCont ct value
        | _ -> fail (TypeMismatch ("continuation", cont))

    /// A deferred body ran out of forms: hand the value to whatever follows.
    and private finishDeferredBody e nextCont metaCont ct value : Step =
        match nextCont with
        | Some (Continuation (cr, None, _)) ->
            More (fun () -> continueEvalStep e (Continuation (cr, metaCont, ct)) value)
        | None ->
            match metaCont with
            | Some frame -> More (fun () -> continueEvalStep e frame.parentCont value)
            | None -> ok value
        | Some _ ->
            fail (Default "Internal Error: metacontinuation in wrong position")

    and evalStep env cont value : Step =
        match env, cont with
        | Environment _, Continuation _ -> evalValidStep env cont value
        | (Environment _), found -> fail (TypeMismatch("continuation", found))
        | found, _ -> fail (TypeMismatch("environment", found))

    and private evalValidStep env cont value : Step =
        match value with
        | Atom id ->
            match getVar env id with
            | Choice2Of2 r -> More (fun () -> continueEvalStep env cont r)
            | Choice1Of2 e -> fail e
        // One walk of the operand chain, not two. Matching `List (Atom name :: args)`
        // and then `List (op :: args)` materialised the operands twice for every
        // combination whose operator is not a symbol, and once for every one that is.
        | Pair cell ->
            match cell.cdr with
            | List args ->
                match cell.car with
                | Atom name ->
                    match getVar' env name with
                    | Some r -> More (fun () -> operateStep env cont r args)
                    | None ->
                        match tryRewrite name args with
                        | Some rewritten -> More (fun () -> evalStep env cont rewritten)
                        | None -> fail (UnboundVar("Getting an unbound variable", name))
                | op ->
                    let cps e v a _ =
                        operateStep e v a args
                    More (fun () -> evalStep env (makeCPS env cont cps) op)
            // An improper combination is not a combination; it evaluates to itself,
            // which is what falling past both list patterns used to do.
            | _ -> More (fun () -> continueEvalStep env cont value)
        | z ->
            More (fun () -> continueEvalStep env cont z)

    and evalArgsExStep _env cont args f : Step =
        let rec evaluateRemaining e c func evaluatedRev = function
            | [] -> operateStep e c func (List.rev evaluatedRev)
            | expression :: remaining ->
                let collect nextEnv nextCont value _ =
                    evaluateRemaining nextEnv nextCont func (value :: evaluatedRev) remaining
                More (fun () -> evalStep e (makeCPS e c collect) expression)

        let evaluateArguments e c func =
            match args with
            | [] -> operateStep e c func []
            | [expression] ->
                let collect nextEnv nextCont value _ =
                    operateStep nextEnv nextCont func [value]
                More (fun () -> evalStep e (makeCPS e c collect) expression)
            | [firstExpression; secondExpression] ->
                let collectFirst nextEnv nextCont firstValue _ =
                    let collectSecond finalEnv finalCont secondValue _ =
                        operateStep finalEnv finalCont func [firstValue; secondValue]
                    More (fun () ->
                        evalStep
                            nextEnv
                            (makeCPS nextEnv nextCont collectSecond)
                            secondExpression)
                More (fun () -> evalStep e (makeCPS e c collectFirst) firstExpression)
            | _ -> evaluateRemaining e c func [] args

        let prepare e c func _ =
            evaluateArguments e c func

        match f with
        | Atom _
        | List (_ :: _) -> More (fun () -> evalStep _env (makeCPS _env cont prepare) f)
        | _ -> evaluateArguments _env cont f

    and operateStep _env cont (func: LispVal) (args: LispVal list) : Step =
        match _env, cont with
        | Environment _, Continuation (cpr, metaCont, ct) ->
            operateValidStep _env cont cpr metaCont ct func args
        | (Environment _), found -> fail (TypeMismatch("continuation", found))
        | found, _ -> fail (TypeMismatch("environment", found))

    and private operateValidStep _env cont cpr metaCont ct (func: LispVal) (args: LispVal list) : Step =
        match func with
        | PrimitiveOperative primitive -> primitive.invoke _env cont args
        | CompiledCombiner f -> f _env cont args
        | ContractedCombiner contracted ->
            match validateArguments contracted.contract args with
            | Some error -> fail error
            | None when contracted.contract.result = AnyShape ->
                More (fun () -> operateStep _env cont contracted.combiner args)
            | None ->
                let validate e c value _ =
                    match validateResult contracted.contract value with
                    | Some error -> fail error
                    | None -> More (fun () -> continueEvalStep e c value)
                More (fun () ->
                    operateStep
                        _env
                        (makeCPS _env cont validate)
                        contracted.combiner
                        args)
        | IOFunc (requiredCapability, f) ->
            if not (has requiredCapability _env) then
                fail (CapabilityDenied(sprintf "I/O requires %A" requiredCapability))
            else
                match evalArgs _env (newContinuation _env) args with
                | Choice1Of2 e -> fail e
                // The result has to be handed to `cont`, not returned as `Done`.
                // `Done` ends the trampoline, which was harmless while every combiner
                // ran inside its own nested `run`, but since compiled code shares one
                // trampoline (ADR 0004) it discards the rest of the computation: the
                // value of `(define p (open-output-file f))` became the value of the
                // whole form and the binding never happened.
                | Choice2Of2 q ->
                    match f q with
                    | Choice1Of2 error -> fail error
                    | Choice2Of2 value -> More (fun () -> continueEvalStep _env cont value)
        | Applicative f -> evalArgsExStep _env cont args f
        | Continuation (cr, capturedPrompt, ct') ->
            match args with
            | [] -> fail (NumArgs (1, []))
            | [a] ->
                match ct' with
                | Full -> More (fun () -> evalStep _env func a)
                | Delimited ->
                    let prompt =
                        match capturedPrompt with
                        | Some frame -> Some { frame with parentCont = cont }
                        | None ->
                            Some
                                { parentCont = cont
                                  tag = None
                                  handler = None }
                    More (fun () -> evalStep _env (Continuation (cr, prompt, Full)) a)
            | _ -> fail (NumArgs (1, args))
        | Resumption resumption ->
            match args with
            | [argument] when Interlocked.Exchange(&resumption.consumed, 1) = 0 ->
                // Resume is a non-local exit from the handler: reinstall the
                // delimited body under its captured prompt, then continue to
                // that prompt's parent. Returning through the handler cont
                // would let trailing handler forms replace the prompt result.
                let resumeCont =
                    match resumption.continuation with
                    | Continuation(_, Some frame, _) -> frame.parentCont
                    | _ -> cont
                More (fun () -> operateStep _env resumeCont resumption.continuation [argument])
            | [_] -> fail (Default "resumption has already been consumed")
            | _ -> fail (NumArgs(1, args))
        | Operative operative ->
            let prms = operative.prms
            let envarg = operative.envarg
            let body = operative.body
            let closure = operative.closure
            let evalBody env =
                let continuationAfterBody =
                    match cpr with
                    // The caller has no forms left to run, so this call is in tail
                    // position: inherit its continuation instead of stacking a frame
                    // on it. A compiled caller reports an exhausted body the same way,
                    // and missing that case would grow the continuation on every tail
                    // call out of compiled code.
                    | { currentCont = Some (KernelCode []); nextCont = nextCont }
                    | { currentCont = Some (CompiledCode []); nextCont = nextCont } -> nextCont
                    | _ -> Some (Continuation (cpr, None, Full))
                // Compile the body on first application and memoise it. Compiling a
                // form costs less than interpreting it once, so there is nothing to
                // gain from a hotness heuristic. A compiler failure falls back to
                // interpretation rather than failing the call.
                let deferredBody =
                    match operative.compiledBody with
                    | Some forms -> CompiledCode forms
                    | None ->
                        match bodyCompiler with
                        | None -> KernelCode body
                        | Some compile ->
                            match (try Some(compile closure body) with _ -> None) with
                            | Some forms ->
                                operative.compiledBody <- Some forms
                                CompiledCode forms
                            | None -> KernelCode body
                More (fun () ->
                    continueEvalStep env
                        (Continuation ({ closure = env; currentCont = Some deferredBody; nextCont = continuationAfterBody; args = None }, metaCont, ct))
                        Nil)

            let newEnv = newEnv [closure]
            match bind newEnv (newContinuation _env) prms (ofList args) with
            | Choice1Of2 error -> fail error
            | Choice2Of2 _ ->
                match defineVar newEnv envarg _env with
                | Choice1Of2 error -> fail error
                | Choice2Of2 _ -> evalBody newEnv
        // The empty list is spelled `List []` everywhere a Kernel program can observe
        // it. Returning the bare `Nil` case here made a value that was neither `null?`
        // nor `eqv?` to itself, because the predicates and the equivalence walk only
        // know the `List` spelling. ADR 0005 phase 1 removes the duplicate case; until
        // then the producers normalise.
        | Inert -> More (fun () -> continueEvalStep _env cont (ofList []))
        | _ -> fail (BadSpecialForm ("Expecting a combiner, got ", func))

    and bindStep env cont lf rf : Step =
        let mutable pending = [lf, rf]
        let mutable bindingError = None

        while bindingError.IsNone && not pending.IsEmpty do
            let formal, value = pending.Head
            pending <- pending.Tail
            match formal with
            | Atom var ->
                match defineVar env var value with
                | Choice1Of2 error -> bindingError <- Some error
                | Choice2Of2 _ -> ()
            // A parameter tree and its value are walked cell by cell. Proper and
            // improper trees need no separate cases: a dotted formal is just a pair
            // whose cdr is a symbol, and the `Atom` case above binds it. Matching
            // through the list patterns instead destructured *and rebuilt* the rest of
            // both chains on every iteration, which made binding quadratic in the
            // number of parameters, on every operative call.
            | Nil ->
                match value with
                | Nil -> ()
                | badForm -> bindingError <- Some(BadSpecialForm("invalid arguments", badForm))
            | Pair formalCell ->
                match value with
                | Pair valueCell ->
                    pending <-
                        (formalCell.car, valueCell.car)
                        :: (formalCell.cdr, valueCell.cdr)
                        :: pending
                | badForm -> bindingError <- Some(BadSpecialForm("invalid arguments", badForm))
            | badForm -> bindingError <- Some(BadSpecialForm("invalid arguments", badForm))

        match bindingError with
        | Some error -> fail error
        | None -> More(fun () -> continueEvalStep env cont Inert)

    and resumeEvaluatedStep env cont (resumption: ResumptionRecord) argument : Step =
        if Interlocked.Exchange(&resumption.consumed, 1) <> 0 then
            fail (Default "resumption has already been consumed")
        else
            match resumption.continuation with
            | Continuation(continuationRecord, Some frame, _) ->
                More(fun () ->
                    continueEvalStep
                        env
                        (Continuation(continuationRecord, Some frame, Full))
                        argument)
            | Continuation(continuationRecord, None, _) ->
                let prompt =
                    Some
                        { parentCont = cont
                          tag = None
                          handler = None }
                More(fun () ->
                    continueEvalStep
                        env
                        (Continuation(continuationRecord, prompt, Full))
                        argument)
            | found -> fail (TypeMismatch("continuation", found))

    and evalArgs _env cont args =
        sequence (List.map (fun a -> run (evalStep _env cont a)) args) []

    /// Public API — single trampoline entry.
    and continueEval env cont value = run (continueEvalStep env cont value)
    and eval env cont value = run (evalStep env cont value)
    and operate env cont func args = run (operateStep env cont func args)
    and bind env cont lf rf = run (bindStep env cont lf rf)

    /// Schedule continue/eval without nesting trampolines (for primitives).
    let bounceContinue env cont value = More (fun () -> continueEvalStep env cont value)
    let bounceEval env cont value = More (fun () -> evalStep env cont value)
    let bounceOperate env cont func args = More (fun () -> operateStep env cont func args)
    let bounceBind env cont lf rf = More (fun () -> bindStep env cont lf rf)

    let evalAsync env cont value = runAsync (evalStep env cont value)
