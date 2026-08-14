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

        /// File operations are guarded so that an I/O failure -- a missing file, a
        /// locked file, a permissions error -- becomes a Kernel error. Left unguarded
        /// the CLR exception escapes the evaluator and faults the process, taking the
        /// REPL or script host with it, as division by zero used to.
        let private guardIO description work =
            try work () with
            | :? IOException as ex -> throwError (Default(description + ": " + ex.Message))
            | :? UnauthorizedAccessException as ex ->
                throwError (Default(description + ": " + ex.Message))
            | :? ArgumentException as ex -> throwError (Default(description + ": " + ex.Message))
            | :? NotSupportedException as ex -> throwError (Default(description + ": " + ex.Message))

        let makePort mode = function
            | [Obj filename] ->
                either {
                    let! fname = cast filename
                    return! guardIO "open file" (fun () ->
                        returnM (Port(File.Open(fname, FileMode.OpenOrCreate, mode))))
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
                    return! guardIO "read file" (fun () -> returnM (makeObj (File.ReadAllText path)))
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
                | [ob; Port port] ->
                    guardIO "write" (fun () ->
                        use writer = new StreamWriter(port)
                        writer.Write(showVal ob)
                        returnM (Bool true))
                | bad -> throwError (NumArgs(1, bad))

        let readProc port =
               let parseReader (reader:TextReader) =
                   match requireSourceServices () with
                   | Choice1Of2 error -> throwError error
                   | Choice2Of2 services -> reader.ReadLine() |> services.parseExpression
               match port with
                | [Port p] -> guardIO "read" (fun () -> use s = new StreamReader(p) in parseReader s)
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

        /// R-1RK 12.5.1. `number?` and `integer?` are type predicates, so a
        /// non-number argument yields false rather than an error; `finite?` requires
        /// numbers, so a non-number is an error. All three are variadic and true for
        /// an empty argument list.
        let private isNumberValue (value: obj) =
            match value with
            | :? byte | :? int | :? int64 | :? float32 | :? float -> true
            | :? Numerics.Complex -> true
            | _ -> false

        let private isIntegerValue (value: obj) =
            match value with
            | :? byte | :? int | :? int64 -> true
            | :? float32 as f -> not (Single.IsNaN f) && not (Single.IsInfinity f) && Math.Floor(float f) = float f
            | :? float as d -> not (Double.IsNaN d) && not (Double.IsInfinity d) && Math.Floor d = d
            // R-1RK 12.5.1: a complex is an integer iff its real part is an integer and
            // its imaginary part is zero.
            | :? Numerics.Complex as c ->
                c.Imaginary = 0.0 && not (Double.IsNaN c.Real) && not (Double.IsInfinity c.Real)
                && Math.Floor c.Real = c.Real
            | _ -> false

        let private isFiniteValue (value: obj) =
            match value with
            | :? byte | :? int | :? int64 -> Some true
            | :? float32 as f -> Some(not (Single.IsNaN f) && not (Single.IsInfinity f))
            | :? float as d -> Some(not (Double.IsNaN d) && not (Double.IsInfinity d))
            // R-1RK 12.5.1: a complex is finite iff its components all are.
            | :? Numerics.Complex as c ->
                Some(
                    not (Double.IsNaN c.Real) && not (Double.IsInfinity c.Real)
                    && not (Double.IsNaN c.Imaginary) && not (Double.IsInfinity c.Imaginary))
            | _ -> None

        let isNumber env cont args =
            let rec loop = function
                | [] -> bounceContinue env cont (Bool true)
                | Obj value :: rest when isNumberValue value -> loop rest
                | _ -> bounceContinue env cont (Bool false)
            loop args

        let isInteger env cont args =
            let rec loop = function
                | [] -> bounceContinue env cont (Bool true)
                | Obj value :: rest when isIntegerValue value -> loop rest
                | _ -> bounceContinue env cont (Bool false)
            loop args

        let isFinite env cont args =
            let rec loop = function
                | [] -> bounceContinue env cont (Bool true)
                | Obj value :: rest ->
                    match isFiniteValue value with
                    | Some true -> loop rest
                    | Some false -> bounceContinue env cont (Bool false)
                    | None -> fail (TypeMismatch("number", Obj value))
                | found :: _ -> fail (TypeMismatch("number", found))
            loop args

        /// Signals an error from Kernel code. Not a feature of the report's required
        /// modules -- R-1RK routes errors through error-continuation (7.2.7), which
        /// IronKernel does not implement -- but permitted as an extension (1.3.2) and
        /// needed so the standard library can report its own failures.
        let raiseError _ cont args =
            ignore cont
            match args with
            | [Obj message] -> fail (Default(string message))
            | [] -> fail (Default "error")
            | values -> fail (Default(String.Join(" ", values |> List.map showVal)))

        /// R-1RK 12.5.7: (zero? . numbers), true when every argument is zero. A
        /// non-number is an error rather than false: zero? is not a type predicate.
        let isZero env cont args =
            let rec loop = function
                | [] -> bounceContinue env cont (Bool true)
                | Obj value :: rest when isNumberValue value ->
                    let isZeroValue =
                        match value with
                        | :? byte as x -> x = 0uy
                        | :? int as x -> x = 0
                        | :? int64 as x -> x = 0L
                        | :? float32 as x -> x = 0.0f
                        | :? float as x -> x = 0.0
                        // R-1RK 12.5.7: a complex is zero when all its components are.
                        | :? Numerics.Complex as c -> c = Numerics.Complex.Zero
                        | _ -> false
                    if isZeroValue then loop rest else bounceContinue env cont (Bool false)
                | found :: _ -> fail (TypeMismatch("number", found))
            loop args
        
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

        /// R-1RK 4.8.3: (eval expression environment).
        let evaluate _ cont = function
            | (expression::environment::_) -> bounceEval environment cont expression
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
                        // Each loaded form gets a fresh continuation. Passing the
                        // caller's `cont` ran the rest of the caller's computation once
                        // per loaded form, and then `bounceContinue` ran it again, so a
                        // nested (load f) evaluated its enclosing form twice.
                        let evaluateForm form = eval env (newContinuation env) form
                        match sequence (List.map evaluateForm lisp) [] with
                        | Choice1Of2 e -> fail e
                        | Choice2Of2 _ -> bounceContinue env cont Inert
            | badform -> fail (NumArgs(1, badform))

        let vau _env cont xs = 
            match xs with
            | prms :: Atom e :: body   -> bounceContinue _env cont (Operative{ prms = prms; envarg = e; body = body; closure = _env; compiledBody = None} ) 
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
                          trust = Asserted
                          minimumOperands = None }
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

        /// R-1RK 12.5.4 / 12.5.5: (+ . numbers) and (* . numbers) are variadic, with
        /// the empty sum zero and the empty product one. Folding left keeps the CLR
        /// extensions working -- (+ date timespan) is still a DateTime -- because each
        /// step is the same binary operation as before.
        let private foldNumeric op identity env cont args =
            match args with
            | [] -> bounceContinue env cont (Obj identity)
            | first :: rest ->
                let rec loop acc = function
                    | [] -> bounceContinue env cont acc
                    | next :: remaining ->
                        match op acc next with
                        | Choice2Of2 result -> loop result remaining
                        | Choice1Of2 error -> fail error
                loop first rest

        /// The binary case is matched directly. Two arguments is overwhelmingly the
        /// common shape, and routing it through the fold costs a closure and a list
        /// traversal on the hottest path in the language.
        let inline private binaryOrFold op identity env cont args =
            match args with
            | [a; b] ->
                match op a b with
                | Choice2Of2 result -> bounceContinue env cont result
                | Choice1Of2 error -> fail error
            | _ -> foldNumeric op identity env cont args

        let plus env cont args = binaryOrFold opAdd (box 0) env cont args
        let times env cont args = binaryOrFold opMultiply (box 1) env cont args

        /// R-1RK 12.5.6: (- number . numbers) needs at least two arguments. The report
        /// declines to give `-` a unary meaning, so that negation is not silently
        /// spelled the same way as subtraction.
        let minus env cont args =
            match args with
            | [_; _] -> binaryOrFold opMinus (box 0) env cont args
            | _ :: _ :: _ -> foldNumeric opMinus (box 0) env cont args
            | _ -> fail (NumArgs(2, args))
        /// R-1RK 12.8.2: (/ number . numbers) divides number by the *product* of the
        /// rest, so (/ 24 2 3) is 4, not (24/2)/3 computed stepwise -- which agrees
        /// here, but the product is what the report specifies and it is what decides
        /// the zero-divisor error.
        let divide env cont args =
            match args with
            | [a; b] ->
                match opDivide a b with
                | Choice2Of2 result -> bounceContinue env cont result
                | Choice1Of2 error -> fail error
            | numerator :: (_ :: _ as divisors) ->
                let rec product acc = function
                    | [] -> Choice2Of2 acc
                    | next :: rest ->
                        match opMultiply acc next with
                        | Choice2Of2 value -> product value rest
                        | Choice1Of2 error -> Choice1Of2 error
                match product (List.head divisors) (List.tail divisors) with
                | Choice1Of2 error -> fail error
                | Choice2Of2 divisor ->
                    match opDivide numerator divisor with
                    | Choice2Of2 result -> bounceContinue env cont result
                    | Choice1Of2 error -> fail error
            | _ -> fail (NumArgs(2, args))
        /// R-1RK 12.9. The report gives these entries signatures only: Appendix A.2
        /// records that it is an incomplete draft whose unwritten portions were "only
        /// planned in rough outline". They therefore carry their standard mathematical
        /// meanings, and the choices the report leaves open are made here.
        ///
        /// A NaN result signals an error rather than being returned. In the report's
        /// terms NaN is a value with no primary value, and 12.2 signals an error for
        /// those; it is also what keeps (sqrt -1) from silently producing a non-number
        /// while the Complex module (12.10) is unimplemented. Infinities *are*
        /// returned: they are representable, ordered, and finite? reports them
        /// correctly, so (log 0) is negative infinity rather than an error.
        let private toFloat (value: obj) =
            match value with
            | :? byte as b -> Some(float b)
            | :? int as i -> Some(float i)
            | :? int64 as l -> Some(float l)
            | :? float32 as f -> Some(float f)
            | :? float as d -> Some d
            | _ -> None

        let private asComplex (value: obj) =
            match value with
            | :? Numerics.Complex as c -> Some c
            | :? byte as b -> Some(Numerics.Complex(float b, 0.0))
            | :? int as i -> Some(Numerics.Complex(float i, 0.0))
            | :? int64 as l -> Some(Numerics.Complex(float l, 0.0))
            | :? float32 as f -> Some(Numerics.Complex(float f, 0.0))
            | :? float as d -> Some(Numerics.Complex(d, 0.0))
            | _ -> None

        let private ofComplexValue (value: Numerics.Complex) : LispVal =
            if value.Imaginary = 0.0 then Obj(box value.Real) else Obj(box value)

        /// With the Complex module (12.10) supported, a real argument outside a
        /// function's real domain takes its complex value rather than signalling: this
        /// is where (sqrt -1) becomes i. A complex argument routes straight to the
        /// complex version. NaN still signals, since it has no primary value.
        let private realPrimitive
                name
                (apply: float -> float)
                (applyComplex: Numerics.Complex -> Numerics.Complex)
                env cont args =
            match args with
            | [Obj value] ->
                match value with
                | :? Numerics.Complex as c ->
                    bounceContinue env cont (ofComplexValue (applyComplex c))
                | _ ->
                    match toFloat value with
                    | None -> fail (TypeMismatch("number", Obj value))
                    | Some input ->
                        let result = apply input
                        if Double.IsNaN result && not (Double.IsNaN input) then
                            let complex = applyComplex (Numerics.Complex(input, 0.0))
                            if Double.IsNaN complex.Real || Double.IsNaN complex.Imaginary then
                                fail (Default(name + ": argument is outside the domain"))
                            else bounceContinue env cont (ofComplexValue complex)
                        else bounceContinue env cont (Obj(box result))
            | [found] -> fail (TypeMismatch("number", found))
            | _ -> fail (NumArgs(1, args))

        /// R-1RK 12.9.1: a complex is real iff its imaginary part is zero. Arithmetic
        /// collapses a zero-imaginary result back to a real, so a surviving Complex
        /// normally has a non-zero imaginary part; the check is made anyway.
        let isReal env cont args =
            let rec loop = function
                | [] -> bounceContinue env cont (Bool true)
                | Obj value :: rest ->
                    let real =
                        match value with
                        | :? byte | :? int | :? int64 | :? float32 | :? float -> true
                        | :? Numerics.Complex as c -> c.Imaginary = 0.0
                        | _ -> false
                    if real then loop rest else bounceContinue env cont (Bool false)
                | _ -> bounceContinue env cont (Bool false)
            loop args

        let expReal env cont args = realPrimitive "exp" Math.Exp Numerics.Complex.Exp env cont args
        let logReal env cont args = realPrimitive "log" Math.Log Numerics.Complex.Log env cont args
        let sinReal env cont args = realPrimitive "sin" Math.Sin Numerics.Complex.Sin env cont args
        let cosReal env cont args = realPrimitive "cos" Math.Cos Numerics.Complex.Cos env cont args
        let tanReal env cont args = realPrimitive "tan" Math.Tan Numerics.Complex.Tan env cont args
        let asinReal env cont args = realPrimitive "asin" Math.Asin Numerics.Complex.Asin env cont args
        let acosReal env cont args = realPrimitive "acos" Math.Acos Numerics.Complex.Acos env cont args
        let sqrtReal env cont args = realPrimitive "sqrt" Math.Sqrt Numerics.Complex.Sqrt env cont args

        /// R-1RK 12.9.4 gives atan both a one- and a two-argument form.
        let atanReal env cont args =
            match args with
            | [_] -> realPrimitive "atan" Math.Atan Numerics.Complex.Atan env cont args
            | [Obj y; Obj x] ->
                match toFloat y, toFloat x with
                | Some y', Some x' -> bounceContinue env cont (Obj(box (Math.Atan2(y', x'))))
                | None, _ -> fail (TypeMismatch("number", Obj y))
                | _, None -> fail (TypeMismatch("number", Obj x))
            | [found; _] -> fail (TypeMismatch("number", found))
            | _ -> fail (NumArgs(1, args))

        /// R-1RK 12.9.6. An integer base raised to a non-negative integer power stays
        /// an integer when the result is representable, so (expt 2 10) is 1024 rather
        /// than 1024.0; anything else is computed as a real.
        let exptReal env cont args =
            match args with
            | [Obj b; Obj e] ->
                match toFloat b, toFloat e with
                | Some baseValue, Some exponent ->
                    let integral (value: obj) =
                        match value with
                        | :? byte | :? int | :? int64 -> true
                        | _ -> false
                    let result = Math.Pow(baseValue, exponent)
                    if Double.IsNaN result then
                        // A negative base with a fractional exponent leaves the reals.
                        let complex =
                            Numerics.Complex.Pow(
                                Numerics.Complex(baseValue, 0.0), Numerics.Complex(exponent, 0.0))
                        if Double.IsNaN complex.Real || Double.IsNaN complex.Imaginary then
                            fail (Default "expt: argument is outside the domain")
                        else bounceContinue env cont (ofComplexValue complex)
                    elif integral b && integral e && exponent >= 0.0
                         && Math.Abs result <= 9.2233720368547758e18
                         && Math.Floor result = result then
                        bounceContinue env cont (Obj(box (int64 result)))
                    else bounceContinue env cont (Obj(box result))
                | None, _ -> fail (TypeMismatch("number", Obj b))
                | _, None -> fail (TypeMismatch("number", Obj e))
            | [found; _] -> fail (TypeMismatch("number", found))
            | _ -> fail (NumArgs(2, args))

        /// Type predicates from chapters 4 and 6. Each is variadic and true for an
        /// empty argument list, matching the report's "every element" phrasing.
        let private typePredicate test env cont args =
            let rec loop = function
                | [] -> bounceContinue env cont (Bool true)
                | value :: rest -> if test value then loop rest else bounceContinue env cont (Bool false)
            loop args

        let isBoolean env cont args =
            typePredicate (function Bool _ -> true | _ -> false) env cont args

        let isSymbol env cont args =
            typePredicate (function Atom _ -> true | _ -> false) env cont args

        let isInert env cont args =
            typePredicate (function Inert -> true | _ -> false) env cont args

        /// R-1RK 4.10.1 / 4.10.2 / 6.2.1. A combiner is an operative or an applicative;
        /// wrapping is what makes it applicative, so anything not wrapped is operative.
        let private isApplicativeValue = function
            | Applicative _ -> true
            | _ -> false

        let private isOperativeValue = function
            | Operative _
            | PrimitiveOperative _
            | CompiledCombiner _ -> true
            | ContractedCombiner record -> record.contract.mode = RawOperands
            | _ -> false

        let isApplicative env cont args = typePredicate isApplicativeValue env cont args
        let isOperative env cont args = typePredicate isOperativeValue env cont args

        let isCombiner env cont args =
            typePredicate (fun v -> isApplicativeValue v || isOperativeValue v) env cont args

        /// R-1RK 5.7.1. Returns (p n a c): pairs, nils, acyclic prefix length and cycle
        /// length of the improper list starting at the argument.
        ///
        /// IronKernel's pairs are immutable and it does not implement the optional Pair
        /// mutation module, so no cyclic structure can be built and c is always zero
        /// and a always equals p. The shape of the answer is still the report's.
        let getListMetrics env cont args =
            match args with
            | [value] ->
                let pairs, nils =
                    match value with
                    | List [] -> 0, 1
                    | List items -> List.length items, 1
                    | DottedList(items, tail) ->
                        List.length items, (match tail with List [] -> 1 | _ -> 0)
                    | _ -> 0, 0
                let counted n = Obj(box n)
                bounceContinue env cont (List [counted pairs; counted nils; counted pairs; counted 0])
            | _ -> fail (NumArgs(1, args))

        /// R-1RK 12.10. Like 12.9 the report gives these signatures only, so they take
        /// their standard meanings. A complex whose imaginary part is zero is a real,
        /// so make-rectangular collapses that case rather than creating a value that
        /// real? would have to reject.
        /// R-1RK 12.10.1: every number is a complex.
        let isComplex env cont args = isNumber env cont args

        let private complexFromParts build env cont args =
            match args with
            | [Obj a; Obj b] ->
                match toFloat a, toFloat b with
                | Some x, Some y -> bounceContinue env cont (ofComplexValue (build x y))
                | None, _ -> fail (TypeMismatch("number", Obj a))
                | _, None -> fail (TypeMismatch("number", Obj b))
            | [found; _] -> fail (TypeMismatch("number", found))
            | _ -> fail (NumArgs(2, args))

        let makeRectangular env cont args =
            complexFromParts (fun real imaginary -> Numerics.Complex(real, imaginary)) env cont args

        let makePolar env cont args =
            complexFromParts
                (fun magnitude angle -> Numerics.Complex.FromPolarCoordinates(magnitude, angle))
                env cont args

        let private complexPart name (pick: Numerics.Complex -> float) env cont args =
            match args with
            | [Obj value] ->
                match asComplex value with
                | Some c -> bounceContinue env cont (Obj(box (pick c)))
                | None -> fail (TypeMismatch("number", Obj value))
            | [found] -> fail (TypeMismatch("number", found))
            | _ -> fail (NumArgs(1, args))

        let realPart env cont args = complexPart "real-part" (fun c -> c.Real) env cont args
        let imagPart env cont args = complexPart "imag-part" (fun c -> c.Imaginary) env cont args
        let magnitudeOf env cont args = complexPart "magnitude" (fun c -> c.Magnitude) env cont args
        let angleOf env cont args = complexPart "angle" (fun c -> c.Phase) env cont args

        /// R-1RK 12.8.1. A rational is a ratio of integers, so every finite number
        /// qualifies and infinities and NaN do not. Being a type predicate, a
        /// non-number is false rather than an error.
        let isRational env cont args =
            let rec loop = function
                | [] -> bounceContinue env cont (Bool true)
                | Obj value :: rest ->
                    let rational =
                        match value with
                        | :? byte | :? int | :? int64 -> true
                        | :? float32 as f -> not (Single.IsNaN f) && not (Single.IsInfinity f)
                        | :? float as d -> not (Double.IsNaN d) && not (Double.IsInfinity d)
                        // R-1RK 12.8.1: a complex is rational iff its real part is and
                        // its imaginary part is zero.
                        | :? Numerics.Complex as c ->
                            c.Imaginary = 0.0 && not (Double.IsNaN c.Real)
                            && not (Double.IsInfinity c.Real)
                        | _ -> false
                    if rational then loop rest else bounceContinue env cont (Bool false)
                | _ -> bounceContinue env cont (Bool false)
            loop args

        /// R-1RK 12.8.4. Integers are returned unchanged; a real keeps its own numeric
        /// kind, which still satisfies integer? because that predicate accepts a float
        /// with an integral value.
        let private roundingPrimitive name (apply: float -> float) env cont args =
            match args with
            | [Obj value] ->
                match value with
                | :? byte | :? int | :? int64 -> bounceContinue env cont (Obj value)
                | :? float32 as f -> bounceContinue env cont (Obj(box (float32 (apply (float f)))))
                | :? float as d -> bounceContinue env cont (Obj(box (apply d)))
                | _ -> fail (TypeMismatch("number", Obj value))
            | [found] -> fail (TypeMismatch("number", found))
            | _ -> fail (NumArgs(1, args))

        let floorReal env cont args = roundingPrimitive "floor" Math.Floor env cont args
        let ceilingReal env cont args = roundingPrimitive "ceiling" Math.Ceiling env cont args
        let truncateReal env cont args = roundingPrimitive "truncate" Math.Truncate env cont args

        /// Rounds halfway cases to even, per R-1RK 12.8.4 and IEEE 754.
        let roundReal env cont args =
            roundingPrimitive "round" (fun d -> Math.Round(d, MidpointRounding.ToEven)) env cont args

        /// R-1RK 12.8.3, in least terms. A double is a dyadic rational, so doubling
        /// until the value is integral gives an exact numerator over a power of two,
        /// which is then reduced. Values whose exact denominator exceeds Int64 are
        /// rejected rather than silently approximated; IronKernel has no exact
        /// rational type to hold them.
        let private exactRatio (value: float) =
            if Double.IsNaN value || Double.IsInfinity value then None
            else
                let mutable numerator = value
                let mutable denominator = 1L
                let mutable overflow = false
                while not overflow && Math.Floor numerator <> numerator do
                    if denominator > Int64.MaxValue / 2L then overflow <- true
                    else
                        numerator <- numerator * 2.0
                        denominator <- denominator * 2L
                if overflow || Math.Abs numerator > 9.2233720368547758e18 then None
                else
                    let rec gcd (a: int64) (b: int64) = if b = 0L then a else gcd b (a % b)
                    let n = int64 numerator
                    let divisor = gcd (abs n) denominator
                    let divisor = if divisor = 0L then 1L else divisor
                    Some(n / divisor, denominator / divisor)

        let private ratioPart name pick env cont args =
            match args with
            | [Obj value] ->
                match value with
                | :? byte as b -> bounceContinue env cont (Obj(pick (int64 b, 1L)))
                | :? int as i -> bounceContinue env cont (Obj(pick (int64 i, 1L)))
                | :? int64 as l -> bounceContinue env cont (Obj(pick (l, 1L)))
                | :? float32 as f ->
                    match exactRatio (float f) with
                    | Some ratio -> bounceContinue env cont (Obj(pick ratio))
                    | None -> fail (Default(name + ": no exact ratio is representable"))
                | :? float as d ->
                    match exactRatio d with
                    | Some ratio -> bounceContinue env cont (Obj(pick ratio))
                    | None -> fail (Default(name + ": no exact ratio is representable"))
                | _ -> fail (TypeMismatch("number", Obj value))
            | [found] -> fail (TypeMismatch("number", found))
            | _ -> fail (NumArgs(1, args))

        let numeratorOf env cont args =
            ratioPart "numerator" (fun (n, _) -> box n) env cont args

        let denominatorOf env cont args =
            ratioPart "denominator" (fun (_, d) -> box d) env cont args

        /// R-1RK 12.5.8: a freshly allocated list of the quotient and the remainder.
        let divAndMod env cont args =
            match args with
            | [a; b] ->
                match opDivAndMod a b with
                | Choice2Of2 (quotient, remainder) ->
                    bounceContinue env cont (List [quotient; remainder])
                | Choice1Of2 error -> fail error
            | _ -> fail (NumArgs(2, args))

        let lessThan env cont args = numBoolBinop env cont opLessThan args
        let lessThanOrEqual env cont args = numBoolBinop env cont opLessThanOrEqual args
        let greaterThan env cont args = numBoolBinop env cont opGreaterThan args
        let greaterThanOrEqual env cont args = numBoolBinop env cont opGreaterThanOrEqual args

        let vector env cont args =
            Vector(List.toArray args) |> bounceContinue env cont

        /// An index outside the vector is reported as a Kernel error. Indexing the
        /// array directly raised IndexOutOfRangeException, which escaped the evaluator
        /// and aborted the process, the same way division by zero and file errors
        /// used to.
        let private checkedIndex (arr: LispVal array) (index: int) name =
            if index < 0 || index >= arr.Length then
                Some(Default(sprintf "%s: index %d is outside a vector of length %d" name index arr.Length))
            else None

        let vector_set env cont args =
            match args with
            | [Vector arr; Obj pos'; value] when typeof<int> = pos'.GetType() ->
                let index = pos' :?> int
                match checkedIndex arr index "vector-set!" with
                | Some error -> fail error
                | None ->
                    arr.[index] <- value
                    bounceContinue env cont Inert
            | [_; pos; _] -> fail (TypeMismatch("vector/int", pos))
            | _ -> fail (NumArgs(3, args))

        let vector_ref env cont args =
            match args with
            | [Vector arr; Obj pos'] when typeof<int> = pos'.GetType() ->
                let index = pos' :?> int
                match checkedIndex arr index "vector-ref" with
                | Some error -> fail error
                | None -> arr.[index] |> bounceContinue env cont
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
                  ("equal?", eqv);
                  ("boolean?", isBoolean);
                  ("symbol?", isSymbol);
                  ("inert?", isInert);
                  ("operative?", isOperative);
                  ("applicative?", isApplicative);
                  ("combiner?", isCombiner);
                  ("get-list-metrics", getListMetrics);
                  ("eqv?", eqv);
                  ("null?", isNull);
                  ("pair?", isPair) ;
                  ("zero?", isZero);
                  ("div-and-mod", divAndMod);
                  ("rational?", isRational);
                  ("real?", isReal);
                  ("complex?", isComplex);
                  ("make-rectangular", makeRectangular);
                  ("make-polar", makePolar);
                  ("real-part", realPart);
                  ("imag-part", imagPart);
                  ("magnitude", magnitudeOf);
                  ("angle", angleOf);
                  ("exp", expReal);
                  ("log", logReal);
                  ("sin", sinReal);
                  ("cos", cosReal);
                  ("tan", tanReal);
                  ("asin", asinReal);
                  ("acos", acosReal);
                  ("atan", atanReal);
                  ("sqrt", sqrtReal);
                  ("expt", exptReal);
                  ("floor", floorReal);
                  ("ceiling", ceilingReal);
                  ("truncate", truncateReal);
                  ("round", roundReal);
                  ("numerator", numeratorOf);
                  ("denominator", denominatorOf);
                  ("error", raiseError);
                  ("number?", isNumber);
                  ("integer?", isInteger);
                  ("finite?", isFinite);
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
                            certifiedVariadicApplicative
                                name
                                [ OneOfShape [NumberShape; DateTimeShape]
                                  OneOfShape [NumberShape; TimeSpanShape] ]
                                0
                                AnyShape)
                    | "-" ->
                        Some(
                            certifiedVariadicApplicative
                                name
                                [ OneOfShape [NumberShape; DateTimeShape]
                                  OneOfShape [NumberShape; DateTimeShape] ]
                                2
                                AnyShape)
                    | "*" ->
                        Some(certifiedVariadicApplicative name [NumberShape; NumberShape] 0 NumberShape)
                    | "/" ->
                        Some(certifiedVariadicApplicative name [NumberShape; NumberShape] 2 NumberShape)
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
