namespace IronKernel

    open System
    open System.IO
    open System.Threading
    open System.Threading.Tasks
    open Choice
    open Errors
    open Ast
    open SymbolTable
    open Interop
    open Eval
    open Capabilities
    open Contracts
    open IronKernel.Generated

    module Runtime = 

        type SourceServices = {
            parseExpression : string -> ThrowsError<LispVal>
            parseExpressions : string -> string -> ThrowsError<LispVal list>
        }

        let mutable private sourceServices : SourceServices option = None

        let configureSourceServices services =
            sourceServices <- Some services

        let private requireSourceServices () =
            match sourceServices with
            | Some services -> returnM services
            | None -> throwError (Default "Source parsing services are unavailable in this runtime")
        
        let cast<'T> (o:obj) = 
            let typ = typeof<'T>
            let found = o.GetType()
            try 
                returnM (o :?> 'T)
            with | :? InvalidCastException  -> throwError(ClrTypeMismatch(typ.Name,found.Name))

        let numericBinOp env cont (op: LispVal -> LispVal -> ThrowsError<LispVal>) prms : Step = 
            match prms with 
            | [a;b] ->
                match op a b with
                | Choice2Of2 result -> bounceContinue env cont result
                | Choice1Of2 error -> fail error
            | _ -> fail (NumArgs(2,prms))

        let numBoolBinop env cont (op: LispVal -> LispVal -> ThrowsError<LispVal>) prms : Step = 
            match prms with 
            | [a;b] ->
                match op a b with
                | Choice2Of2 result -> bounceContinue env cont result
                | Choice1Of2 error -> fail error
            | _ -> fail (NumArgs(2,prms))

        let car env cont = function
            | [List (x::_)] -> bounceContinue env cont x
            | [DottedList (x::_,_)] -> bounceContinue env cont x
            | [badArg] -> fail (TypeMismatch("pair",badArg))
            | badArgList -> fail (NumArgs(1,badArgList))

        let cdr env cont = function 
            | [List(_::xs)] -> bounceContinue env cont (List xs)
            | [DottedList([_],x)] -> bounceContinue env cont x
            | [DottedList(_::xs,x)] -> bounceContinue env cont (DottedList(xs, x))
            | [badArg] -> fail (TypeMismatch("pair",badArg))
            | badArgList -> fail (NumArgs(1,badArgList))

        let cons env cont = function
            | [x; List []] -> bounceContinue env cont (List[x])
            | [x; List(xs)] -> bounceContinue env cont (List(x::xs))
            | [x;DottedList(xs,xlast)] -> bounceContinue env cont (DottedList(x::xs,xlast))
            | [x1;x2] -> bounceContinue env cont (DottedList([x1],x2))
            | badArgList -> fail (NumArgs(2,badArgList))

        let private eqvValue left right =
            let pending = System.Collections.Generic.Stack<LispVal * LispVal>()
            pending.Push(left, right)
            let mutable equal = true

            let pushLists leftValues rightValues =
                let rec loop leftRemaining rightRemaining =
                    match leftRemaining, rightRemaining with
                    | [], [] -> ()
                    | leftValue :: leftTail, rightValue :: rightTail ->
                        pending.Push(leftValue, rightValue)
                        loop leftTail rightTail
                    | _ -> equal <- false
                loop leftValues rightValues

            while equal && pending.Count > 0 do
                match pending.Pop() with
                | Inert, Inert -> ()
                | Obj arg1, Obj arg2 -> equal <- arg1.Equals(arg2)
                | Bool arg1, Bool arg2 -> equal <- arg1 = arg2
                | Atom arg1, Atom arg2 -> equal <- arg1 = arg2
                | PromptTag arg1, PromptTag arg2 -> equal <- arg1 = arg2
                | DottedList (xs, x), DottedList (ys, y) ->
                    pending.Push(x, y)
                    pushLists xs ys
                | List xs, List ys -> pushLists xs ys
                | _ -> equal <- false

            equal

        let eqv' = function
            | [left; right] -> returnM (Bool(eqvValue left right))
            | badArgList -> throwError (NumArgs(2,badArgList))

        let eqv env cont parms =
            match eqv' parms with
            | Choice1Of2 e -> fail e
            | Choice2Of2 q -> bounceContinue env cont q

        open System.IO

        let tryLoad filename = 
            try
                returnM (File.ReadAllText filename :> obj |> Ast.Obj) 
            with _ -> throwError (Default("File not found: '" + filename + "'"))

        let makePort mode = function
            | [Obj filename] ->
                either {
                    let! fname = cast filename
                    let port = File.Open(fname, FileMode.OpenOrCreate, mode)
                    return Port port
                }
            | [found] -> throwError(TypeMismatch("string", found))
            | bad -> throwError(NumArgs(1, bad))
            
        let closePort = function
            | [Port port] ->
                try port.Close(); Bool true with _ -> Bool false
                |> returnM
            | [found] -> throwError(TypeMismatch("port", found))
            | bad -> throwError(NumArgs(1, bad))

        let readContents = function
            | [Obj filename] ->
                either {
                    let! path = cast filename
                    let contents = File.ReadAllText path
                    return makeObj contents
                }
            | [found] -> throwError(TypeMismatch("string", found))
            | bad -> throwError(NumArgs(1, bad))

        let load filename =
            match tryLoad filename with
            | Choice2Of2 (Obj contents) ->
                match requireSourceServices () with
                | Choice1Of2 error -> throwError error
                | Choice2Of2 services -> services.parseExpressions filename (string contents)
            | Choice2Of2 found -> throwError(TypeMismatch("string", found))
            | Choice1Of2 error -> throwError error

        let readAll = function
            | [Obj filename] ->
                either {
                    let! path = cast filename
                    let! expressions = load path
                    return List expressions
                }
            | [found] -> throwError(TypeMismatch("string", found))
            | bad -> throwError(NumArgs(1, bad))

        let writeProc = function
                | [ob] -> Console.Out.Write(showVal ob);returnM (Bool true)
                | [ob; Port port] -> use writer = new StreamWriter(port)
                                     writer.Write(showVal ob)
                                     returnM (Bool true)
                | bad -> throwError (NumArgs(1, bad))

        let readProc port =
               let parseReader (reader:TextReader) =
                   match requireSourceServices () with
                   | Choice1Of2 error -> throwError error
                   | Choice2Of2 services -> reader.ReadLine() |> services.parseExpression
               match port with
                | [Port p]  -> use s = new StreamReader(p) in parseReader s
                | [] -> parseReader Console.In
                | bad -> throwError (NumArgs(1, bad))
          
        let ioPrimitives : (string * (LispVal list -> ThrowsError<LispVal>)) list =
            [
                    ("open-input-file", makePort FileAccess.Read);
                    ("open-output-file", makePort FileAccess.Write);
                    ("close-input-port", closePort);
                    ("close-output-port", closePort);
                    ("read", readProc);
                    ("write", writeProc);
                    ("read-contents", readContents);
                    ("read-all", readAll) ]

        let isNull env cont = function 
            | [List[]]   -> bounceContinue env cont <| Bool(true) 
            | _          -> bounceContinue env cont <| Bool(false)

        let isEnvironment env cont = function 
            | [Environment _ ]   -> bounceContinue env cont <| Bool(true) 
            | _          -> bounceContinue env cont <| Bool(false)

        let isVector env cont = function 
            | [Vector _ ]   -> bounceContinue env cont <| Bool(true) 
            | _          -> bounceContinue env cont <| Bool(false)

        let isPair env cont = function 
            | [DottedList _]    -> bounceContinue env cont <| Bool(true) 
            | [List (_::_) ]    -> bounceContinue env cont <| Bool(true) 
            | _                 -> bounceContinue env cont <| Bool(false)

        let isZero env cont = function 
            |[Obj x] -> match x with 
                        | :? byte -> bounceContinue env cont <| Bool(byte (0) = (x :?> byte)) 
                        | :? int -> bounceContinue env cont <| Bool(0 = (x :?> int)) 
                        | :? int64 -> bounceContinue env cont <| Bool((x :?> int64) = 0L) 
                        | :? float32 -> bounceContinue env cont <| Bool((x :?> float32) = 0.0f) 
                        | :? float -> bounceContinue env cont <| Bool((x :?> float) = 0.0) 
                        | _ -> bounceContinue env cont <| Bool(false)
            |_ -> bounceContinue env cont <| Bool(false)
        
        open Arithmetic

        let wrap env cont = function
            | [combiner] ->
                let withEagerMode contracted =
                    { contracted with
                        contract =
                            { contracted.contract with
                                mode = EvaluatedArguments } }
                let wrapped =
                    match combiner with
                    | ContractedCombiner contracted ->
                        Applicative(ContractedCombiner(withEagerMode contracted))
                    | Applicative (ContractedCombiner contracted) ->
                        // Already applicative-contracted; avoid nesting Applicative.
                        Applicative(ContractedCombiner(withEagerMode contracted))
                    | _ -> Applicative combiner
                bounceContinue env cont wrapped
            | bad -> fail(NumArgs(1, bad))

        let unwrap env cont = function
            | Applicative (ContractedCombiner contracted) :: _ ->
                bounceContinue
                    env
                    cont
                    (ContractedCombiner
                        { contracted with
                            contract =
                                { contracted.contract with
                                    mode = RawOperands } })
            | Applicative c :: _ -> bounceContinue env cont c
            | a :: _ -> fail (TypeMismatch("applicative",a))
            | [] -> fail (NumArgs(1, []))

        let evaluate _ cont = function 
            | (a::b::_) -> bounceEval a cont b 
            | badArgList -> fail (NumArgs(2, badArgList))

        let makeEnvironment env cont parents =
            let parentCapabilities =
                parents
                |> List.choose (function
                    | Environment record -> Some record.capabilities
                    | _ -> None)
            let capabilities =
                Capabilities.intersect (ofEnvironment env :: parentCapabilities)
            // Inherit CLR opens/aliases from the creating env and declared parents.
            bounceContinue
                env
                cont
                (newEnvWithClr capabilities parents (env :: parents))
    
        let if_then_else env cont args = 
            match args with
            | cond::b::c::_ ->
                let cps e cn r _ =
                     match r with
                        |Bool(true) -> bounceEval e cn b 
                        |Bool(false) -> bounceEval e cn c
                        |found -> fail (TypeMismatch("bool",found))
                bounceEval env (makeCPS env cont cps) cond
            |_ -> fail (NumArgs(3,args))

        let loadAndEval env cont = function
            | _ when not (has SourceLoading env) ->
                fail (CapabilityDenied "source loading requires SourceLoading")
            | [Obj(filename)] ->
                match cast filename with
                | Choice1Of2 e -> fail e
                | Choice2Of2 fname ->
                    match load fname with
                    | Choice1Of2 e -> fail e
                    | Choice2Of2 lisp ->
                        match sequence (List.map (eval env cont) lisp) [] with
                        | Choice1Of2 e -> fail e
                        | Choice2Of2 _ -> bounceContinue env cont Inert
            | badform -> fail (NumArgs(1, badform))

        let vau _env cont xs = 
            match xs with
            | prms :: Atom e :: body   -> bounceContinue _env cont (Operative{ prms = prms; envarg = e; body = body; closure = _env} ) 
            | _ -> fail (Default("invalid arguments"))

        let define env cont xs = 
            match xs with 
            | [ l; r ] ->
                let cps e c result _ = bounceBind e c l result
                bounceEval env (makeCPS env cont cps) r 
            | badForm -> fail (BadSpecialForm("invalid arguments",List(badForm)))

        let rec private parseContractShape = function
            | Atom "any" -> Some AnyShape
            | Atom "number" -> Some NumberShape
            | Atom "integer" -> Some IntegerShape
            | Atom "string" -> Some StringShape
            | Atom "boolean" -> Some BooleanShape
            | Atom "atom" -> Some AtomShape
            | Atom "list" -> Some ListShape
            | Atom "prompt-tag" -> Some PromptTagShape
            | Atom "resumption" -> Some ResumptionShape
            | Atom "datetime" -> Some DateTimeShape
            | Atom "timespan" -> Some TimeSpanShape
            // A non-empty list of shapes is a union: (number datetime) matches either.
            | List (_ :: _ as shapes) ->
                let parsed = shapes |> List.map parseContractShape
                if parsed |> List.forall Option.isSome then
                    Some(OneOfShape(parsed |> List.choose id))
                else None
            | _ -> None

        let attachContract env cont = function
            | [ Atom name;
                Atom modeName;
                List operandSpecs;
                resultSpec;
                Atom effectName;
                Bool inlineable ] ->
                let mode =
                    match modeName with
                    | "operative" -> Some RawOperands
                    | "applicative" -> Some EvaluatedArguments
                    | _ -> None
                let effect =
                    match effectName with
                    | "pure" -> Some Pure
                    | "effectful" -> Some Effectful
                    | _ -> None
                let operands = operandSpecs |> List.map parseContractShape
                match mode, effect, parseContractShape resultSpec, getVar env name with
                | Some mode, Some effect, Some result, Choice2Of2 value
                    when List.forall Option.isSome operands ->
                    let contract =
                        { name = name
                          mode = mode
                          operands = operands |> List.choose id
                          result = result
                          effect = effect
                          inlineable = inlineable
                          trust = Asserted }
                    match Contracts.attach contract value with
                    | Some contracted ->
                        match defineVar env name contracted with
                        | Choice1Of2 error -> fail error
                        | Choice2Of2 _ -> bounceContinue env cont Inert
                    | None ->
                        fail (ContractViolation(name + " contract mode does not match its combiner"))
                | _, _, _, Choice1Of2 error -> fail error
                | _ -> fail (ContractViolation("invalid contract specification for " + name))
            | bad -> fail (NumArgs(6, bad))

        let contractOf env cont = function
            | [value] ->
                match tryGetContract value with
                | None -> bounceContinue env cont (Bool false)
                | Some contract ->
                    let mode =
                        match contract.mode with
                        | RawOperands -> Atom "operative"
                        | EvaluatedArguments -> Atom "applicative"
                    let effect =
                        match contract.effect with
                        | Pure -> Atom "pure"
                        | Effectful -> Atom "effectful"
                    let trust =
                        match contract.trust with
                        | Certified -> Atom "certified"
                        | Asserted -> Atom "asserted"
                    bounceContinue
                        env
                        cont
                        (List
                            [ mode
                              List(List.map shapeValue contract.operands)
                              shapeValue contract.result
                              effect
                              Bool contract.inlineable
                              trust ])
            | bad -> fail (NumArgs(1, bad))

        let reset env cont = function
            | [body] ->
                bounceEval env (promptContinuation env cont None None) body
            | [tagExpression; body] ->
                let install e c tag _ =
                    match tag with
                    | PromptTag id ->
                        bounceEval e (promptContinuation e c (Some id) None) body
                    | found -> fail (TypeMismatch("prompt-tag", found))
                bounceEval env (makeCPS env cont install) tagExpression
            | badform -> fail (NumArgs(1,badform))

        let prompt env cont = function
            | [tagExpression; handlerExpression; body] ->
                let captureTag e c tag _ =
                    match tag with
                    | PromptTag id ->
                        let captureHandler handlerEnv handlerCont handler _ =
                            match handler with
                            | Applicative _ ->
                                bounceEval
                                    handlerEnv
                                    (promptContinuation
                                        handlerEnv
                                        handlerCont
                                        (Some id)
                                        (Some handler))
                                    body
                            | found -> fail (TypeMismatch("applicative handler", found))
                        bounceEval e (makeCPS e c captureHandler) handlerExpression
                    | found -> fail (TypeMismatch("prompt-tag", found))
                bounceEval env (makeCPS env cont captureTag) tagExpression
            | badform -> fail (NumArgs(3, badform))
         
        let primitiveOperatives : (string * (LispVal -> LispVal -> LispVal list -> Step)) list =
            [
                  ("vau"    , vau);
                  ("define" , define);
                  ("if"     , if_then_else);
                  ("."      , dot) ;
                  ("new" , new_object);
                  (".get", dot_get);
                  (".set", dot_set);
                  ("clr-open", clr_open);
                  ("clr-alias", clr_alias);
                  ("clr-type", clr_type);
                  ("reset", reset);
                  ("prompt", prompt);
                  ("contract", attachContract);
                  ]
        
        let callcc env cont  = function 
            | [func] -> 
                match func with 
                | Continuation _    -> bounceContinue env func cont 
                | Applicative f     -> bounceOperate env cont f [cont]
                | badForm -> fail (TypeMismatch("continuation",badForm))
            | badForm -> fail (NumArgs(1,badForm))

        let private captureShift env cont tag f =
            match findPrompt tag cont with
            | Some (continuationRecord, frame) ->
                let captured =
                    Continuation(continuationRecord, Some frame, Delimited)
                let handlerCont =
                    promptContinuation env frame.parentCont frame.tag frame.handler
                bounceOperate env handlerCont f [captured]
            | None ->
                let description =
                    match tag with
                    | None -> "untagged prompt"
                    | Some _ -> "matching tagged prompt"
                fail (Default("shift requires a " + description))

        let shift env cont = function
            | [Applicative f] -> captureShift env cont None f
            | [PromptTag tag; Applicative f] ->
                captureShift env cont (Some tag) f
            | bad -> fail (NumArgs(1, bad))

        let makePromptTag env cont = function
            | [] -> bounceContinue env cont (PromptTag(Guid.NewGuid()))
            | bad -> fail (NumArgs(0, bad))

        let perform env cont = function
            | [PromptTag tag; value] ->
                match findPrompt (Some tag) cont with
                | Some (continuationRecord, ({ handler = Some handler } as frame)) ->
                    let captured =
                        Continuation(continuationRecord, Some frame, Delimited)
                    let record =
                        { continuation = captured
                          consumed = 0 }
                    let resumption = Resumption record
                    // Abort (handler return without resume) must invalidate the
                    // one-shot resumption so a stored handle cannot restart later.
                    // Successful resume bypasses this continuation and delivers
                    // the delimited body's result straight to frame.parentCont.
                    let invalidateOnAbort e c result _ =
                        Interlocked.Exchange(&record.consumed, 1) |> ignore
                        bounceContinue e c result
                    bounceOperate
                        env
                        (makeCPS env frame.parentCont invalidateOnAbort)
                        handler
                        [value; resumption]
                | Some _ -> fail (Default "matching prompt has no effect handler")
                | None -> fail (Default "perform requires a matching tagged handler")
            | [found; _] -> fail (TypeMismatch("prompt-tag", found))
            | bad -> fail (NumArgs(2, bad))

        let resume env cont = function
            | [Resumption resumption; value] ->
                resumeEvaluatedStep env cont resumption value
            | [found; _] -> fail (TypeMismatch("resumption", found))
            | bad -> fail (NumArgs(2, bad))

        let private taskOutcome (completed: Task) =
            try
                completed.GetAwaiter().GetResult()
                let taskType = completed.GetType()
                if taskType.IsGenericType
                   && taskType.GetGenericTypeDefinition() = typedefof<Task<_>> then
                    match taskType.GetProperty("Result").GetValue(completed) with
                    | null -> returnM Inert
                    | :? LispVal as value -> returnM value
                    | other -> returnM (Obj other)
                else
                    returnM Inert
            with
            | :? OperationCanceledException as error -> throwError (ClrException error)
            | error -> throwError (ClrException error)

        let awaitTask env cont = function
            | _ when not (has HostAsync env) ->
                fail (CapabilityDenied "await-task requires HostAsync")
            | [Obj (:? Task as pending)] ->
                Await
                    { register =
                        fun complete ->
                            pending.ContinueWith(
                                (fun completed -> complete (taskOutcome completed)),
                                CancellationToken.None,
                                TaskContinuationOptions.ExecuteSynchronously,
                                TaskScheduler.Default)
                            |> ignore
                      resume =
                        function
                        | Choice1Of2 error -> fail error
                        | Choice2Of2 value -> bounceContinue env cont value }
            | [found] -> fail (TypeMismatch("Task", found))
            | bad -> fail (NumArgs(1, bad))

        let taskDelay env cont = function
            | _ when not (has HostAsync env) ->
                fail (CapabilityDenied "task-delay requires HostAsync")
            | [Obj (:? int as milliseconds); value] when milliseconds >= 0 ->
                let pending =
                    task {
                        do! Task.Delay(milliseconds)
                        return value
                    }
                bounceContinue env cont (Obj(pending :> obj))
            | [found; _] -> fail (TypeMismatch("non-negative int", found))
            | bad -> fail (NumArgs(2, bad))

        let plus env cont args = numericBinOp env cont opAdd args
        let minus env cont args = numericBinOp env cont opMinus args
        let times env cont args = numericBinOp env cont opMultiply args
        let divide env cont args = numericBinOp env cont opDivide args
        let lessThan env cont args = numBoolBinop env cont opLessThan args
        let lessThanOrEqual env cont args = numBoolBinop env cont opLessThanOrEqual args
        let greaterThan env cont args = numBoolBinop env cont opGreaterThan args
        let greaterThanOrEqual env cont args = numBoolBinop env cont opGreaterThanOrEqual args

        let vector env cont args =
            Vector(List.toArray args) |> bounceContinue env cont

        let vector_set env cont args =
            match args with 
            | [Vector arr; Obj pos'; value] when typeof<int> = pos'.GetType() ->
                arr.[pos' :?> int] <- value
                bounceContinue env cont Inert
            | [_; pos; _] -> fail (TypeMismatch("vector/int", pos))
            | _ -> fail (NumArgs(3, args))

        let vector_ref env cont args =
            match args with 
            | [Vector arr; Obj pos'] when typeof<int> = pos'.GetType() ->
                arr.[pos' :?> int] |> bounceContinue env cont
            | [_; pos] -> fail (TypeMismatch("vector/int", pos))
            | _ -> fail (NumArgs(2, args))

        let make_vector env cont args =
            match args with
            | [Obj size'; v] when typeof<int> = size'.GetType() ->
                Vector(Array.create (size' :?> int) v) |> bounceContinue env cont
            | [size; _] -> fail (TypeMismatch("int", size))
            | _ -> fail (NumArgs(2, args))

        let make_encapsulation_type env cont = function
            | [] ->
                let tag = Guid.NewGuid()
                let primitive f =
                    PrimitiveOperative { identity = None; invoke = f }
                let encapsulator =
                    Applicative(
                        primitive (fun e c -> function
                            | [value] -> bounceContinue e c (Encapsulation { tag = tag; value = value })
                            | bad -> fail(NumArgs(1, bad))))
                let predicate =
                    Applicative(
                        primitive (fun e c -> function
                            | [Encapsulation encapsulation] ->
                                bounceContinue e c (Bool(tag.Equals(encapsulation.tag)))
                            | [_] -> bounceContinue e c (Bool false)
                            | bad -> fail(NumArgs(1, bad))))
                let decapsulator =
                    Applicative(
                        primitive (fun e c -> function
                            | [Encapsulation encapsulation] when tag.Equals(encapsulation.tag) ->
                                bounceContinue e c encapsulation.value
                            | [_] -> fail(Default "encapsulation type mismatch")
                            | bad -> fail(NumArgs(1, bad))))

                List [encapsulator; predicate; decapsulator] |> bounceContinue env cont
            | bad -> fail(NumArgs(0, bad))

        let primitiveApplicatives : (string * (LispVal -> LispVal -> LispVal list -> Step)) list =
            [
                  ("eval", evaluate);
                  ("wrap", wrap);
                  ("unwrap", unwrap);
                  ("load", loadAndEval);
                  ("call/cc", callcc);
                  ("+", plus);
                  ("-", minus);
                  ("*", times);
                  ("/", divide);
                  ("<", lessThan);
                  ("<=",lessThanOrEqual);
                  (">",greaterThan);
                  ("car", car);
                  ("cdr", cdr);
                  ("cons", cons);
                  ("eq?", eqv);
                  ("eqv?", eqv);
                  ("null?", isNull);
                  ("pair?", isPair) ;
                  ("zero?", isZero);
                  ("environment?", isEnvironment)
                  ("make-environment", makeEnvironment);
                  ("print", print);
                  ("printf", printf');
                  ("show", show);
                  ("contract-of", contractOf);
                  ("shift", shift);
                  ("make-prompt-tag", makePromptTag);
                  ("perform", perform);
                  ("resume", resume);
                  ("await-task", awaitTask);
                  ("task-delay", taskDelay);
                  ("vector", vector);
                  ("vector?", isVector);
                  ("make-vector", make_vector);
                  ("vector-ref", vector_ref);
                  ("vector-set!", vector_set);
                  ("make-encapsulation-type", make_encapsulation_type);
                  ("clr-opens", clr_opens);
                  ]

        /// Fresh environment containing only primitive operators (safe for isolated tests).
        let makePrimitiveBindingsForProfile profile =
            let capabilities = forProfile profile
            let operativeIdentity = function
                | "if" -> Some PrimitiveIf
                | "define" -> Some PrimitiveDefine
                | _ -> None
            let makeOperative (name, func) =
                name,
                PrimitiveOperative
                    { identity = operativeIdentity name
                      invoke = func }
            let makeApplicative (name, func) =
                let applicative =
                    Applicative(
                        PrimitiveOperative
                            { identity = None
                              invoke = func })
                let contract =
                    match name with
                    // `+` also accepts DateTime + TimeSpan and `-` DateTime - DateTime.
                    // Results stay AnyShape: a non-any result wraps every dynamic call
                    // in a validation continuation, which these hot paths avoid.
                    | "+" ->
                        Some(
                            certifiedApplicative
                                name
                                [ OneOfShape [NumberShape; DateTimeShape]
                                  OneOfShape [NumberShape; TimeSpanShape] ]
                                AnyShape)
                    | "-" ->
                        Some(
                            certifiedApplicative
                                name
                                [ OneOfShape [NumberShape; DateTimeShape]
                                  OneOfShape [NumberShape; DateTimeShape] ]
                                AnyShape)
                    | "*" | "/" ->
                        Some(certifiedApplicative name [NumberShape; NumberShape] NumberShape)
                    | "<" | "<=" | ">" ->
                        Some(certifiedApplicative name [NumberShape; NumberShape] BooleanShape)
                    | _ -> None
                let value =
                    match contract with
                    | Some contract ->
                        Contracts.attach contract applicative
                        |> Option.defaultValue applicative
                    | None -> applicative
                name, value
            let rawInteropOperatives =
                Set.ofList
                    [ "."
                      "new"
                      ".get"
                      ".set"
                      "clr-open"
                      "clr-alias"
                      "clr-type" ]
            let rawInteropApplicatives = Set.ofList [ "clr-opens" ]
            let asyncNames = Set.ofList [ "await-task"; "task-delay" ]
            let operatives =
                primitiveOperatives
                |> List.filter (fun (name, _) ->
                    not (Set.contains name rawInteropOperatives)
                    || Set.contains RawClrInterop capabilities)
                |> List.map makeOperative
            let applicatives =
                primitiveApplicatives
                |> List.filter (fun (name, _) ->
                    (name <> "load" || Set.contains SourceLoading capabilities)
                    && (not (Set.contains name (Set.ofList ["print"; "printf"; "show"]))
                        || Set.contains HostIO capabilities)
                    && (not (Set.contains name asyncNames)
                        || Set.contains HostAsync capabilities)
                    && (not (Set.contains name rawInteropApplicatives)
                        || Set.contains RawClrInterop capabilities))
                |> List.map makeApplicative
            let io =
                if Set.contains HostIO capabilities then
                    ioPrimitives
                    |> List.map (fun (name, func) -> name, IOFunc(HostIO, func))
                else []
            let generated =
                if Set.contains (GeneratedClr "safe") capabilities then
                    SafeBindings.bindings
                else []
            io @ operatives @ applicatives @ generated
            |> bindVars (newEnvWithCapabilities capabilities [])

        let makePrimitiveBindings () =
            makePrimitiveBindingsForProfile Unrestricted

        /// Shared bootstrap environment (REPL / CLI). Prefer `makePrimitiveBindings` in tests.
        let primitiveBindings = makePrimitiveBindings ()
