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
            | [] ->
                match nextCont with
                | Some (Continuation (cr, None, _)) ->
                    More (fun () -> continueEvalStep e (Continuation (cr, metaCont, ct)) value)
                | None ->
                    match metaCont with
                    | Some frame -> More (fun () -> continueEvalStep e frame.parentCont value)
                    | None -> ok value
                | Some _ ->
                    fail (Default "Internal Error: metacontinuation in wrong position")
            | p :: tail ->
                More (fun () ->
                    evalStep e
                        (Continuation ({ closure = e; currentCont = Some (KernelCode tail); nextCont = nextCont; args = None }, metaCont, ct))
                        p)
        | _ -> fail (TypeMismatch ("continuation", cont))

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
        | List (Atom name :: args) ->
            match getVar' env name with
            | Some r -> More (fun () -> operateStep env cont r args)
            | None ->
                match tryRewrite name args with
                | Some rewritten -> More (fun () -> evalStep env cont rewritten)
                | None -> fail (UnboundVar("Getting an unbound variable", name))
        | List (op :: args) ->
            let cps e v a _ =
                operateStep e v a args
            More (fun () -> evalStep env (makeCPS env cont cps) op)
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
                | Choice2Of2 q -> ofResult (f q)
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
        | Operative { prms = prms; envarg = envarg; body = body; closure = closure } ->
            let evalBody env =
                match cpr with
                | { currentCont = Some (KernelCode cBody); nextCont = nextCont } ->
                    match cBody with
                    | [] ->
                        More (fun () ->
                            continueEvalStep env
                                (Continuation ({ closure = env; currentCont = Some (KernelCode body); nextCont = nextCont; args = None }, metaCont, ct))
                                Nil)
                    | _ ->
                        More (fun () ->
                            continueEvalStep env
                                (Continuation ({ closure = env; currentCont = Some (KernelCode body); nextCont = Some (Continuation (cpr, None, Full)); args = None }, metaCont, ct))
                                Nil)
                | _ ->
                    More (fun () ->
                        continueEvalStep env
                            (Continuation ({ closure = env; currentCont = Some (KernelCode body); nextCont = Some (Continuation (cpr, None, Full)); args = None }, metaCont, ct))
                            Nil)

            let newEnv = newEnv [closure]
            match bind newEnv (newContinuation _env) prms (List args) with
            | Choice1Of2 error -> fail error
            | Choice2Of2 _ ->
                match defineVar newEnv envarg _env with
                | Choice1Of2 error -> fail error
                | Choice2Of2 _ -> evalBody newEnv
        | Inert -> More (fun () -> continueEvalStep _env cont Nil)
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
            | List [] ->
                match value with
                | List [] -> ()
                | badForm -> bindingError <- Some(BadSpecialForm("invalid arguments", badForm))
            | List (head :: tail) ->
                match value with
                | List (valueHead :: valueTail) ->
                    pending <- (head, valueHead) :: (List tail, List valueTail) :: pending
                | badForm -> bindingError <- Some(BadSpecialForm("invalid arguments", badForm))
            | DottedList ([], rest) ->
                match value with
                | DottedList ([], valueRest) -> pending <- (rest, valueRest) :: pending
                | _ -> pending <- (rest, value) :: pending
            | DottedList (head :: tail, rest) ->
                match value with
                | List (valueHead :: valueTail) ->
                    pending <-
                        (head, valueHead) :: (DottedList(tail, rest), List valueTail) :: pending
                | DottedList (valueHead :: valueTail, valueRest) ->
                    pending <-
                        (head, valueHead)
                        :: (DottedList(tail, rest), DottedList(valueTail, valueRest))
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
