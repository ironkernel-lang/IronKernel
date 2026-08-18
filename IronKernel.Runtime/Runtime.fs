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

        // The three fundamental operations, each one cell access. Asked through the
        // list patterns they were linear: `car` walked a whole chain to read its first
        // cell, and `cdr` and `cons` walked it *and rebuilt it*, so every (cdr rest) in
        // a library loop copied the rest of the list and every traversal was quadratic.
        // Sharing the tail rather than copying it is also what R-1RK means by a pair --
        // and what set-cdr! will need in phase 3.
        let car env cont = function
            | [Pair cell] -> bounceContinue env cont cell.car
            | [badArg] -> fail (TypeMismatch("pair",badArg))
            | badArgList -> fail (NumArgs(1,badArgList))

        let cdr env cont = function 
            | [Pair cell] -> bounceContinue env cont cell.cdr
            | [badArg] -> fail (TypeMismatch("pair",badArg))
            | badArgList -> fail (NumArgs(1,badArgList))

        let cons env cont = function
            | [x; y] -> bounceContinue env cont (cons x y)
            | badArgList -> fail (NumArgs(2,badArgList))

        /// R-1RK 4.2.1 and 4.3.1. One walk serves both predicates; `pairsByIdentity`
        /// is what separates them.
        ///
        /// `eq?` is "effectively the same object, even in the presence of mutation",
        /// and the report is explicit that "two pairs returned by different calls to
        /// cons are not eq?, even if they have the same car and cdr and the
        /// implementation doesn't support pair mutation". So eq? compares pairs by
        /// cell identity. `equal?` compares them structurally -- "look the same as
        /// long as nothing is mutated" -- which is weaker, as 4.3.1 requires.
        ///
        /// Everything else is judged the same way by both. Two equal exact integers,
        /// or two equal symbols, are interchangeable in every way a program can
        /// observe, and the report leaves eq? on such objects to the implementation.
        let private compareValues pairsByIdentity left right =
            let pending = System.Collections.Generic.Stack<LispVal * LispVal>()
            pending.Push(left, right)
            let visited =
                System.Collections.Generic.HashSet<struct (PairCell * PairCell)>(
                    HashIdentity.Structural)
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
                // An object is the same object as itself, whatever its type. Without
                // this an environment, a vector or a primitive combiner was not equal
                // to itself, because the cases below cover only the types with a
                // structural comparison and everything else fell through to false --
                // which breaks the reflexivity 4.2.1 and 4.3.1 both require.
                | first, second when obj.ReferenceEquals(first, second) -> ()
                | Inert, Inert -> ()
                | Obj arg1, Obj arg2 -> equal <- arg1.Equals(arg2)
                | Bool arg1, Bool arg2 -> equal <- arg1 = arg2
                | Atom arg1, Atom arg2 -> equal <- arg1 = arg2
                | PromptTag arg1, PromptTag arg2 -> equal <- arg1 = arg2
                // Compared cell by cell rather than through the list patterns, which
                // materialised both chains before comparing them and walked each value
                // twice over -- once failing DottedList, once matching List.
                | Pair left, Pair right ->
                    if pairsByIdentity then
                        // Reference-equal cells were settled above; distinct cells are
                        // distinct pairs however alike they look.
                        equal <- false
                    // A pair of cells already under comparison is assumed equal. That is
                    // what makes equal? terminate on cyclic structure, which R-1RK 4.3.1
                    // requires and set-cdr! now makes reachable: if following the cycle
                    // round ever disagreed, the disagreement is found before the cells
                    // recur. eq? cannot loop, because it never descends into a pair.
                    elif not (visited.Add(struct (left, right))) then ()
                    else
                        pending.Push(left.cdr, right.cdr)
                        pending.Push(left.car, right.car)
                | Nil, Nil -> ()
                | _ -> equal <- false

            equal

        /// R-1RK 4.7.1. The result is inert, and 3.8 requires an error when the pair is
        /// immutable -- which is what protects a captured algorithm from being rewritten
        /// under the combiner that captured it.
        let private setPairPart name assign env cont args =
            match args with
            | [Pair cell; object'] ->
                if cell.immutable then
                    fail (Default(name + ": pair is immutable"))
                else
                    assign cell object'
                    bounceContinue env cont Inert
            | [found; _] -> fail (TypeMismatch("pair", found))
            | _ -> fail (NumArgs(2, args))

        let setCar env cont args =
            setPairPart "set-car!" (fun cell value -> cell.car <- value) env cont args

        let setCdr env cont args =
            setPairPart "set-cdr!" (fun cell value -> cell.cdr <- value) env cont args

        let private eqvValue left right = compareValues false left right

        let private eqValue left right = compareValues true left right

        let eqv' = function
            | [left; right] -> returnM (Bool(eqvValue left right))
            | badArgList -> throwError (NumArgs(2,badArgList))

        /// R-1RK 6.5.1 and 6.6.1 generalize both predicates to zero or more arguments:
        /// true unless some two of the arguments differ. Comparing neighbours settles
        /// that, because both relations are transitive (4.2.1 rule 1, 4.3.1 rule 1).
        let private variadicEquivalence compare env cont args =
            let rec loop = function
                | first :: (second :: _ as rest) ->
                    if compare first second then loop rest
                    else bounceContinue env cont (Bool false)
                | _ -> bounceContinue env cont (Bool true)
            loop args

        let eqv env cont args = variadicEquivalence eqvValue env cont args

        let eq env cont args = variadicEquivalence eqValue env cont args

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

        // Reading opens an existing file; only writing creates one. OpenOrCreate for
        // both meant `open-input-file` on a missing file silently created an empty one
        // and then read nothing from it, which is a surprising way to answer "that file
        // is not there".
        let private fileModeFor = function
            | FileAccess.Read -> FileMode.Open
            | _ -> FileMode.OpenOrCreate

        let makePort mode = function
            | [Obj filename] ->
                either {
                    let! fname = cast filename
                    return! guardIO "open file" (fun () ->
                        returnM (Port(File.Open(fname, fileModeFor mode, mode))))
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
                    return ofList expressions
                }
            | [found] -> throwError(TypeMismatch("string", found))
            | bad -> throwError(NumArgs(1, bad))

        /// R-1RK 15.1.4. The current ports are keyed dynamic variables (chapter 10),
        /// which is what makes `with-input-from-file` scope its port to a dynamic
        /// extent, and they default to the standard input and output.
        ///
        /// The console ports are compared by identity where it matters: writing to one
        /// goes through `Console.Out` rather than the raw stream, so that a host which
        /// has redirected it -- as the example tests do -- still sees the output.
        let private currentInputKey () = Guid "0f4a7c31-9b28-4d55-a7e6-1c83b5920af4"
        let private currentOutputKey () = Guid "6d1e93b7-42fa-4c08-93b1-8ae7d0641c25"

        let private consoleInput = lazy (Port(Console.OpenStandardInput()))
        let private consoleOutput = lazy (Port(Console.OpenStandardOutput()))

        let private isConsole (candidate: LispVal) (which: Lazy<LispVal>) =
            obj.ReferenceEquals(candidate, which.Force())

        let private currentPort key (fallback: Lazy<LispVal>) cont =
            match findDynamicBinding (key ()) cont with
            | Some (Port _ as port) -> port
            | _ -> fallback.Force()

        let private currentInput cont = currentPort currentInputKey consoleInput cont
        let private currentOutput cont = currentPort currentOutputKey consoleOutput cont

        /// R-1RK 15.1.1 and 15.1.2. `port?` is the primitive type predicate; the other
        /// two return false for a non-port rather than signalling, and "every port must
        /// be admitted by at least one of these two".
        // Spelled out rather than routed through `typePredicate`, which is defined
        // further down the file than the ports are.
        let private portPredicate test env cont args =
            let rec loop = function
                | [] -> bounceContinue env cont (Bool true)
                | value :: rest ->
                    if test value then loop rest else bounceContinue env cont (Bool false)
            loop args

        let isPort env cont args =
            portPredicate (function Port _ -> true | _ -> false) env cont args

        let isInputPort env cont args =
            portPredicate (function Port stream -> stream.CanRead | _ -> false) env cont args

        let isOutputPort env cont args =
            portPredicate (function Port stream -> stream.CanWrite | _ -> false) env cont args

        /// R-1RK 15.1.6. Closing is not mutation (see the chapter's preamble: a port's
        /// state is administrative), and the result is inert.
        let private closeFile name wanted env cont args =
            match args with
            | [Port stream as port] ->
                if not (wanted stream) then fail (TypeMismatch(name + " port", port))
                else
                    try stream.Close() with _ -> ()
                    bounceContinue env cont Inert
            | [found] -> fail (TypeMismatch("port", found))
            | _ -> fail (NumArgs(1, args))

        let closeInputFile env cont args =
            closeFile "input" (fun (s: IO.Stream) -> s.CanRead) env cont args

        let closeOutputFile env cont args =
            closeFile "output" (fun (s: IO.Stream) -> s.CanWrite) env cont args

        let getCurrentInputPort env cont args =
            match args with
            | [] -> bounceContinue env cont (currentInput cont)
            | _ -> fail (NumArgs(0, args))

        let getCurrentOutputPort env cont args =
            match args with
            | [] -> bounceContinue env cont (currentOutput cont)
            | _ -> fail (NumArgs(0, args))

        let private openFile name access filename =
            let mode =
                if access = IO.FileAccess.Read then IO.FileMode.Open else IO.FileMode.OpenOrCreate
            try Choice2Of2(Port(IO.File.Open(filename, mode, access)))
            with ex -> Choice1Of2(Default(name + ": " + ex.Message))

        /// R-1RK 15.1.3. "The opened port is accessed implicitly within the dynamic
        /// extent of the call, and is automatically closed on normal return" -- so the
        /// port is bound as a keyed dynamic variable and the combiner is called with no
        /// operands, and a continuation after the call closes it.
        ///
        /// A non-local exit leaves the port open. The report's own preamble offers this
        /// form as the safest of the three precisely because a *normal* return closes
        /// it; closing on an abnormal one would need an exit guard (7.2.4), and is
        /// recorded as a divergence rather than assumed.
        let private withPortFromFile name access key env cont args =
            match args with
            | [Obj filename; combiner] when (filename :? string) ->
                match openFile name access (filename :?> string) with
                | Choice1Of2 error -> fail error
                | Choice2Of2 (Port stream as port) ->
                    let closeAfter _ c value _ =
                        try stream.Close() with _ -> ()
                        More(fun () -> continueEvalStep env c value)
                    let afterCall = makeCPS env cont closeAfter
                    let isolated = newEnvWithClr (ofEnvironment env) [] []
                    bounceOperate
                        isolated
                        (makeDynamicBinding env afterCall (key ()) port)
                        combiner
                        []
                | Choice2Of2 _ -> fail (Default(name + ": could not open the file"))
            | [found; _] -> fail (TypeMismatch("string", found))
            | _ -> fail (NumArgs(2, args))

        let withInputFromFile env cont args =
            withPortFromFile "with-input-from-file" IO.FileAccess.Read currentInputKey env cont args

        let withOutputToFile env cont args =
            withPortFromFile "with-output-to-file" IO.FileAccess.Write currentOutputKey env cont args

        /// R-1RK 15.2.1. Like the above, but the port is handed to the combiner as an
        /// operand rather than bound implicitly, and is likewise closed on return.
        let private callWithFile name access env cont args =
            match args with
            | [Obj filename; combiner] when (filename :? string) ->
                match openFile name access (filename :?> string) with
                | Choice1Of2 error -> fail error
                | Choice2Of2 (Port stream as port) ->
                    let closeAfter _ c value _ =
                        try stream.Close() with _ -> ()
                        More(fun () -> continueEvalStep env c value)
                    bounceOperate env (makeCPS env cont closeAfter) combiner [port]
                | Choice2Of2 _ -> fail (Default(name + ": could not open the file"))
            | [found; _] -> fail (TypeMismatch("string", found))
            | _ -> fail (NumArgs(2, args))

        let callWithInputFile env cont args =
            callWithFile "call-with-input-file" IO.FileAccess.Read env cont args

        let callWithOutputFile env cont args =
            callWithFile "call-with-output-file" IO.FileAccess.Write env cont args

        /// R-1RK 15.1.8. With no port the current output port is used, which is what
        /// gives `with-output-to-file` its effect: the chapter's preamble has that form
        /// accessed "implicitly", meaning through this default.
        ///
        /// Writing to the console port goes through `Console.Out` rather than the raw
        /// standard-output stream, so that a host which has redirected it still sees
        /// the output. The stream is not disposed after writing -- a port outlives one
        /// write, and closing it is 15.1.6's job.
        let private writeTo (port: LispVal) (value: LispVal) =
            if isConsole port consoleOutput then
                Console.Out.Write(showVal value)
                returnM (Bool true)
            else
                match port with
                | Port stream ->
                    guardIO "write" (fun () ->
                        // leaveOpen: disposing the writer must not close the port --
                        // 15.1.6 is what closes it. Leaving the writer *undisposed*
                        // instead is worse than it looks: its finalizer flushes, and a
                        // flush to an already closed stream throws on the finalizer
                        // thread, which aborts the process.
                        use writer = new StreamWriter(stream, Text.Encoding.UTF8, 1024, true)
                        writer.Write(showVal value)
                        returnM (Bool true))
                | found -> throwError (TypeMismatch("port", found))

        let writeValue env cont args =
            let finish result =
                match result with
                | Choice1Of2 error -> fail error
                | Choice2Of2 value -> bounceContinue env cont value
            match args with
            | [value] -> finish (writeTo (currentOutput cont) value)
            | [value; (Port _ as port)] -> finish (writeTo port value)
            | [_; found] -> fail (TypeMismatch("port", found))
            | _ -> fail (NumArgs(1, args))

        /// R-1RK 15.1.7, and the counterpart of write: with no port the current input
        /// port is read, which is how `with-input-from-file` takes effect.
        let private readFrom (port: LispVal) =
            let parseReader (reader: TextReader) =
                match requireSourceServices () with
                | Choice1Of2 error -> throwError error
                | Choice2Of2 services ->
                    // ReadLine returns null at end of input, and the parser dereferences
                    // what it is given. IronKernel has no end-of-file object to return
                    // instead, so this signals; before, a read past the end of a port
                    // reached the parser as a null string and faulted the process.
                    match reader.ReadLine() with
                    | null -> throwError (Default "read: end of input")
                    | line -> services.parseExpression line
            if isConsole port consoleInput then parseReader Console.In
            else
                match port with
                | Port stream ->
                    guardIO "read" (fun () ->
                        // leaveOpen, as for write: closing the port is 15.1.6's job.
                        use reader = new StreamReader(stream, Text.Encoding.UTF8, true, 1024, true)
                        parseReader reader)
                | found -> throwError (TypeMismatch("port", found))

        let readValue env cont args =
            let finish result =
                match result with
                | Choice1Of2 error -> fail error
                | Choice2Of2 value -> bounceContinue env cont value
            match args with
            | [] -> finish (readFrom (currentInput cont))
            | [Port _ as port] -> finish (readFrom port)
            | [found] -> fail (TypeMismatch("port", found))
            | _ -> fail (NumArgs(0, args))
          
        let ioPrimitives : (string * (LispVal list -> ThrowsError<LispVal>)) list =
            [
                    ("open-input-file", makePort FileAccess.Read);
                    ("open-output-file", makePort FileAccess.Write);
                    ("close-input-port", closePort);
                    ("close-output-port", closePort);
                    ("read-contents", readContents);
                    ("read-all", readAll) ]

        // Nil is the empty list, so this is one comparison. Spelled `List []` it went
        // through the list pattern, which walks a whole chain to build its elements
        // before discovering they are not empty -- O(n) for a question about one cell.
        let isNull env cont = function 
            | [Nil]      -> bounceContinue env cont <| Bool(true) 
            | _          -> bounceContinue env cont <| Bool(false)

        let isEnvironment env cont = function 
            | [Environment _ ]   -> bounceContinue env cont <| Bool(true) 
            | _          -> bounceContinue env cont <| Bool(false)

        let isVector env cont = function 
            | [Vector _ ]   -> bounceContinue env cont <| Bool(true) 
            | _          -> bounceContinue env cont <| Bool(false)

        // Likewise: a pair is one cell. Asking through the list patterns walked the
        // chain twice -- once to fail DottedList, once to match List -- which made
        // every (pair? xs) in the list library linear in the list.
        let isPair env cont = function 
            | [Pair _]          -> bounceContinue env cont <| Bool(true) 
            | _                 -> bounceContinue env cont <| Bool(false)

        /// R-1RK 12.5.1. `number?` and `integer?` are type predicates, so a
        /// non-number argument yields false rather than an error; `finite?` requires
        /// numbers, so a non-number is an error. All three are variadic and true for
        /// an empty argument list.
        let private isNumberValue (value: obj) =
            match value with
            | :? byte | :? int | :? int64 | :? float32 | :? float -> true
            | :? Numerics.BigInteger | :? ExactRatio | :? ExactInfinity -> true
            | :? Numerics.Complex -> true
            | _ -> false

        let private isIntegerValue (value: obj) =
            match value with
            | :? byte | :? int | :? int64 | :? Numerics.BigInteger -> true
            | :? ExactRatio as ratio -> ratio.Denominator.IsOne
            // R-1RK 12.5.14 calls an integer-or-infinity an *improper* integer, so an
            // infinity is not an integer.
            | :? ExactInfinity -> false
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
            | :? byte | :? int | :? int64 | :? Numerics.BigInteger | :? ExactRatio -> Some true
            | :? ExactInfinity -> Some false
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
                        | :? Numerics.BigInteger as x -> x = Numerics.BigInteger.Zero
                        | :? ExactRatio as x -> x.Numerator.IsZero
                        | :? ExactInfinity -> false
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
                        //
                        // R-1RK 15.2.2 has load acquire immutable copies of what it
                        // captures; it captures nothing here. Each form is evaluated and
                        // discarded, and an operative created along the way acquires its
                        // own structure through `vau` above (ADR 0005 phase 0).
                        let evaluateForm form = eval env (newContinuation env) form
                        match sequence (List.map evaluateForm lisp) [] with
                        | Choice1Of2 e -> fail e
                        | Choice2Of2 _ -> bounceContinue env cont Inert
            | badform -> fail (NumArgs(1, badform))

        /// R-1RK 4.10.3. The parameter tree and the body are acquired immutably, per
        /// 4.7.2: an operative must not change under whoever captured it. See ADR 0005
        /// -- today `acquireImmutable` is the identity, and this is the seam that has to
        /// start copying when pairs become mutable.
        /// The environment parameter may be `#ignore` (R-1RK 4.10.3), which declines
        /// the dynamic environment rather than binding it. It is spelled here as a name
        /// no symbol can be read as, so that `bind` simply never finds it.
        let private ignoredEnvironmentName = "#ignore environment parameter"

        let vau _env cont xs = 
            let build prms envarg body =
                bounceContinue _env cont (
                    Operative{ prms = acquireImmutable prms
                               envarg = envarg
                               body = acquireImmutableForms body
                               closure = _env
                               compiledBody = None } )
            match xs with
            | prms :: Atom e :: body -> build prms e body
            | prms :: Ignore :: body -> build prms ignoredEnvironmentName body
            | _ -> fail (Default("invalid arguments"))

        let define env cont xs = 
            match xs with 
            | [ l; r ] ->
                let cps e c result _ = bounceBind e c l result
                bounceEval env (makeCPS env cont cps) r 
            | badForm -> fail (BadSpecialForm("invalid arguments",ofList(badForm)))

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
                        (ofList
                            [ mode
                              ofList(List.map shapeValue contract.operands)
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
         
        /// R-1RK 6.7.1. Operative: the first operand is evaluated in the dynamic
        /// environment and must be an environment; the rest are symbols, and the
        /// predicate is true iff every one of them is visibly bound in it.
        ///
        /// The report derives this from an exit guard on error-continuation, catching
        /// the error an unbound lookup signals. That derivation does not work here --
        /// signalling an error is not an abnormal pass to error-continuation, which the
        /// 7.2.7 divergence records -- so the lookup is asked directly instead.
        let bindsPredicate env cont args =
            match args with
            | environmentExpression :: symbols ->
                let decide _ resultCont value _ =
                    match value with
                    | Environment _ ->
                        let rec loop = function
                            | [] -> More(fun () -> continueEvalStep env resultCont (Bool true))
                            | Atom name :: rest ->
                                if (getVar' value name).IsSome then loop rest
                                else More(fun () -> continueEvalStep env resultCont (Bool false))
                            // A non-symbol operand is a type error rather than false:
                            // the question "is this bound" has no meaning for it.
                            | found :: _ -> fail (TypeMismatch("symbol", found))
                        loop symbols
                    | found -> fail (TypeMismatch("environment", found))
                bounceEval env (makeCPS env cont decide) environmentExpression
            | [] -> fail (NumArgs(1, args))

        let primitiveOperatives : (string * (LispVal -> LispVal -> LispVal list -> Step)) list =
            [
                  ("vau"    , vau);
                  ("$binds?", bindsPredicate);
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
        
        /// R-1RK 7.2.6. The ancestor of all other continuations. IronKernel's drivers
        /// give each top-level form its own continuation rather than threading one root
        /// through the session, so root is not literally at the end of every chain;
        /// instead the extent test below reports it as containing everything, which is
        /// what "ancestor of all other continuations" means and is the only thing the
        /// selection algorithm asks of it. A guard clause selecting on it is therefore
        /// always selected, which the report's rationale gives as its whole purpose.
        ///
        /// Receiving a value normally ends the session (7.2.6), which travels out as
        /// SessionExit rather than as a result, because there is no continuation left
        /// below it to receive one.
        /// The terminal record a native frame needs below it: the evaluator invokes a
        /// native frame only when one follows, and these frames never pass anything on.
        let private terminalRecord () =
            { closure = Nil; currentCont = None; nextCont = None; args = None }

        let private distinguishedContinuation receive =
            Continuation(
                { closure = Nil
                  currentCont = Some(NativeCode { cont = receive; args = None })
                  nextCont = Some(Continuation(terminalRecord (), None, Full))
                  args = None },
                None, Full)

        let private rootRecord () =
            distinguishedContinuation (fun _ _ value _ -> Done(Choice1Of2(SessionExit value)))

        let private theRoot = lazy (rootRecord ())

        let rootContinuation () = theRoot.Force()

        /// R-1RK 7.2.7. Receiving a value provides a diagnostic and resumes the system
        /// outside all user computation, which is what aborting the computation with an
        /// error does here. Its extent is disjoint from ordinary computation because it
        /// has no ancestors and is nobody's ancestor.
        let private theErrorContinuation =
            lazy (distinguishedContinuation (fun _ _ value _ -> Done(Choice1Of2(Default(showVal value)))))

        let errorContinuation () = theErrorContinuation.Force()

        let private isRoot (record: ContinuationRecord) =
            match rootContinuation () with
            | Continuation(root, _, _) -> obj.ReferenceEquals(record, root)
            | _ -> false

        /// R-1RK 7.2.5, selection. An exit-guard list is considered iff the pass leaves
        /// the extent of its inner continuation, and an entry-guard list iff the pass
        /// enters the extent of its outer continuation. A record is left iff it is an
        /// ancestor of the source and not of the destination, and entered iff the other
        /// way round, so the two lists fall straight out of the chains.
        ///
        /// Exit lists are considered from smallest extent to largest -- outward from
        /// the source, which is the order the source chain already has -- and entry
        /// lists from largest to smallest, inward to the destination, which is the
        /// destination chain reversed.
        let private selectInterceptors source destination =
            let sourceChain = continuationAncestry source
            let destinationChain = continuationAncestry destination
            let barrier (record: ContinuationRecord) =
                match record.currentCont with
                | Some (GuardBarrier guards) -> Some(record, guards)
                | _ -> None
            // The selector's extent has to contain the destination for an exit guard and
            // the source for an entry guard. root-continuation contains everything.
            let selectorHolds chain (selector: LispVal) =
                match selector with
                | Continuation(record, _, _) -> isRoot record || withinExtent chain record
                | _ -> false
            let firstMatch chain clauses =
                clauses |> List.tryPick (fun (selector, interceptor) ->
                    if selectorHolds chain selector then Some interceptor else None)
            let exited =
                sourceChain
                |> List.filter (fun record -> not (withinExtent destinationChain record))
                |> List.choose barrier
                |> List.choose (fun (record, guards) ->
                    // Exit guards are about leaving the *inner* extent. Where the inner
                    // continuation is known, that is the test; an interceptor's own
                    // continuation sits between inner and outer, which is what keeps it
                    // from re-triggering the guard it was selected by.
                    let leavesInner =
                        match guards.inner with
                        | Some inner ->
                            withinExtent sourceChain inner
                            && not (withinExtent destinationChain inner)
                        | None -> true
                    if not leavesInner then None
                    else firstMatch destinationChain guards.exitClauses
                         |> Option.map (fun interceptor -> interceptor, record, guards.guardEnv))
            let entered =
                destinationChain
                |> List.filter (fun record -> not (withinExtent sourceChain record))
                |> List.choose barrier
                |> List.choose (fun (record, guards) ->
                    firstMatch sourceChain guards.entryClauses
                    |> Option.map (fun interceptor -> interceptor, record, guards.guardEnv))
                |> List.rev
            exited @ entered

        /// R-1RK 7.2.5. The applicative's underlying operative abnormally passes its
        /// operand tree to `target`.
        ///
        /// The operand tree of a combination is a list, which is what the evaluator
        /// hands a primitive, so it is rebuilt as one here. An *atomic* operand tree,
        /// which the report also allows, has no representation in that list -- use
        /// apply-continuation, which takes the object directly.
        let rec private abnormalPass target =
            Applicative(
                PrimitiveOperative
                    { identity = None
                      invoke = fun e c args -> passAbnormally e c target (ofList args) })

        /// The whole chain of interceptions is scheduled at once as *normal* passes, so
        /// that handing the value from one interceptor to the next is not itself subject
        /// to interception. Each interceptor's result continuation is a child of that
        /// guard's outer continuation, putting the call inside the outer extent and
        /// outside the inner one.
        and private passAbnormally env source target value =
            let interceptions = selectInterceptors source target
            let rec chain remaining =
                match remaining with
                | [] -> fun v -> More(fun () -> continueEvalStep env target v)
                | (interceptor, outerRecord: ContinuationRecord, guardEnv) :: rest ->
                    let next = chain rest
                    fun v ->
                        let outer = Continuation(outerRecord, None, Full)
                        let resultCont =
                            Continuation(
                                { closure = guardEnv
                                  currentCont =
                                    Some(
                                        NativeCode
                                            { cont = fun _ _ result _ -> next result
                                              args = None })
                                  nextCont = Some outer
                                  args = None },
                                None, Full)
                        // The interceptor is unwrapped exactly once (7.2.4), so its
                        // operands -- the value and a route to the outer continuation --
                        // reach it unevaluated.
                        match interceptor with
                        | Applicative underlying ->
                            More(fun () ->
                                operateStep guardEnv resultCont underlying [v; abnormalPass outer])
                        | _ -> fail (TypeMismatch("applicative", interceptor))
            chain interceptions value

        let continuationToApplicative env cont args =
            match args with
            | [Continuation _ as target] -> bounceContinue env cont (abnormalPass target)
            | [found] -> fail (TypeMismatch("continuation", found))
            | _ -> fail (NumArgs(1, args))

        /// R-1RK 7.3.1: (apply-continuation continuation object). Derived in the report
        /// from continuation->applicative and apply, but written directly here so that
        /// an atomic object is passed as the operand tree rather than wrapped in the
        /// argument list the evaluator would build for it.
        let applyContinuation env cont args =
            match args with
            | [Continuation _ as target; value] -> passAbnormally env cont target value
            | [found; _] -> fail (TypeMismatch("continuation", found))
            | _ -> fail (NumArgs(2, args))

        /// R-1RK 7.2.3. A child of `target` that, on normally receiving v, calls the
        /// underlying combiner of `applicative` with dynamic environment `dynamicEnv`
        /// and operand tree v, its result normally returning to `target`.
        ///
        /// The child relation is the chain itself: the new record's nextCont is
        /// `target`, so `target` is its ancestor in exactly the sense of 7.1.
        let private extendWith target applicative dynamicEnv =
            match applicative, target with
            | Applicative underlying, Continuation(cr, mc, ct) ->
                let operands = function
                    | List values -> values
                    | Nil -> []
                    // An atomic operand tree has no list form; the combiner receives it
                    // as a one-element tree, which is the closest available reading.
                    | value -> [value]
                let receive _ c value _ =
                    More(fun () -> operateStep dynamicEnv c underlying (operands value))
                Choice2Of2(
                    Continuation(
                        { closure = dynamicEnv
                          currentCont = Some(NativeCode { cont = receive; args = None })
                          nextCont = Some(Continuation(cr, None, Full))
                          args = None },
                        mc, ct))
            | Applicative _, found -> Choice1Of2(TypeMismatch("continuation", found))
            | found, _ -> Choice1Of2(TypeMismatch("applicative", found))

        let extendContinuation env cont args =
            // The two-argument form is sugar for an empty environment (7.2.3).
            let extend target applicative dynamicEnv =
                match extendWith target applicative dynamicEnv with
                | Choice2Of2 extended -> bounceContinue env cont extended
                | Choice1Of2 error -> fail error
            match args with
            | [target; applicative; (Environment _ as dynamicEnv)] ->
                extend target applicative dynamicEnv
            | [target; applicative] ->
                extend target applicative (newEnvWithClr (ofEnvironment env) [] [])
            | [_; _; found] -> fail (TypeMismatch("environment", found))
            | _ -> fail (NumArgs(2, args))

        /// R-1RK 7.2.4. Each clause is (selector interceptor): a continuation, and an
        /// applicative whose underlying combiner is operative. The clauses are taken
        /// apart here and held as a list, which is the "internal copies ... so that the
        /// selectors and interceptors ... remain fixed thereafter" the report asks for.
        let private guardClauses name value =
            let rec collect acc = function
                | [] -> Choice2Of2(List.rev acc)
                | List [selector; interceptor] :: rest ->
                    match selector, interceptor with
                    | Continuation _, Applicative underlying ->
                        // "an applicative whose underlying combiner is operative", so a
                        // multiply wrapped interceptor is rejected: unwrapping once has
                        // to reach the operative that receives the value unevaluated.
                        match underlying with
                        | Applicative _ ->
                            Choice1Of2(TypeMismatch(name + " interceptor underlying operative", interceptor))
                        | _ -> collect ((selector, interceptor) :: acc) rest
                    | Continuation _, found ->
                        Choice1Of2(TypeMismatch(name + " interceptor applicative", found))
                    | found, _ -> Choice1Of2(TypeMismatch(name + " selector continuation", found))
                | found :: _ -> Choice1Of2(TypeMismatch(name + " clause of length two", found))
            match value with
            | List clauses -> collect [] clauses
            | Nil -> Choice2Of2 []
            | found -> Choice1Of2(TypeMismatch(name + " list", found))

        /// Builds the outer continuation, a child of `target` carrying the guards, and
        /// the inner continuation, a child of the outer one, and returns the inner.
        /// Normal receipt passes straight through both (see Eval), so in the absence of
        /// abnormal passing they behave exactly as `target` does.
        let private buildGuarded env target entry exit =
            match target with
            | Continuation(targetRecord, metaCont, ct) ->
                match guardClauses "entry-guard" entry, guardClauses "exit-guard" exit with
                | Choice1Of2 error, _ | _, Choice1Of2 error -> Choice1Of2 error
                | Choice2Of2 entryClauses, Choice2Of2 exitClauses ->
                    let guards =
                        { entryClauses = entryClauses
                          exitClauses = exitClauses
                          guardEnv = env
                          inner = None }
                    let outerRecord =
                        { closure = env
                          currentCont = Some(GuardBarrier guards)
                          nextCont = Some(Continuation(targetRecord, None, Full))
                          args = None }
                    let innerRecord =
                        { closure = env
                          currentCont = None
                          nextCont = Some(Continuation(outerRecord, None, Full))
                          args = None }
                    guards.inner <- Some innerRecord
                    Choice2Of2(Continuation(innerRecord, metaCont, ct))
            | found -> Choice1Of2(TypeMismatch("continuation", found))

        let guardContinuation env cont args =
            match args with
            | [entry; (Continuation _ as target); exit] ->
                match buildGuarded env target entry exit with
                | Choice2Of2 inner -> bounceContinue env cont inner
                | Choice1Of2 error -> fail error
            | [_; found; _] -> fail (TypeMismatch("continuation", found))
            | _ -> fail (NumArgs(3, args))

        /// R-1RK 7.3.3: extends the current continuation with the guards and calls
        /// combiner in the dynamic extent of the new continuation, with no operands and
        /// the dynamic environment of this call.
        ///
        /// The report derives this from guard-continuation with an elaborate detour: a
        /// dedicated bypass continuation, and an entry guard prepended to override all
        /// the client's, so that getting *into* the new extent does not trigger the very
        /// entry guards being installed. That detour exists because a library definition
        /// can only reach the new continuation by an abnormal pass. A primitive already
        /// holds the current continuation, so it can call the combiner with the inner
        /// continuation directly -- no abnormal entry happens, and no entry guard fires,
        /// which is the behaviour the derivation goes to that trouble to achieve.
        let guardDynamicExtent env cont args =
            match args with
            | [entry; combiner; exit] ->
                match buildGuarded env cont entry exit with
                | Choice1Of2 error -> fail error
                | Choice2Of2 inner -> bounceOperate env inner combiner []
            | _ -> fail (NumArgs(3, args))

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

        /// The result type has to be found by walking the base types, not by testing
        /// the concrete one. An F# `task { ... return v }` is an
        /// AsyncTaskMethodBuilder`1+AsyncStateMachineBox`1, which *derives from*
        /// Task<T> but whose own generic definition is not Task<>. Testing the
        /// concrete type therefore always failed, and every awaited value was
        /// discarded and reported as #inert.
        let rec private taskResultType (candidate: Type) =
            // `isNull` is shadowed in this module by the `null?` primitive.
            if obj.ReferenceEquals(candidate, null) then None
            elif candidate.IsGenericType
                 && candidate.GetGenericTypeDefinition() = typedefof<Task<_>> then
                Some candidate
            else taskResultType candidate.BaseType

        let private taskOutcome (completed: Task) =
            try
                completed.GetAwaiter().GetResult()
                match taskResultType (completed.GetType()) with
                | Some taskType ->
                    // `task { do! ... }` with no value is Task<VoidTaskResult>; that
                    // carries no result and is inert.
                    let resultType = taskType.GetGenericArguments().[0]
                    if resultType.FullName = "System.Threading.Tasks.VoidTaskResult" then
                        returnM Inert
                    else
                        match taskType.GetProperty("Result").GetValue(completed) with
                        | null -> returnM Inert
                        | :? LispVal as value -> returnM value
                        | other -> returnM (Obj other)
                | None -> returnM Inert
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

        /// R-1RK 12.6.6. strict-arithmetic is a keyed dynamic variable like any other
        /// (chapter 10), except that its accessor answers even with no binder in scope.
        /// The key is fixed rather than freshly generated so that the arithmetic
        /// primitives and the two applicatives share it; nothing can forge it, because
        /// make-keyed-dynamic-variable only ever mints new ones.
        ///
        /// It is a function rather than a module-level value because a module-level
        /// binding is null until the module initialiser has run, which is not
        /// guaranteed at the point a primitive first reads it.
        let private strictArithmeticKey () = Guid "9d2f5a10-7c3e-4b58-9a61-2f7c1d4e8b03"

        /// R-1RK 12.7.1's narrow-arithmetic variable, the other of the pair.
        let private narrowArithmeticKey () = Guid "4e81c6b2-05da-4f37-8c19-6b3a7f20d5ee"

        let private booleanDynamicVariable key defaultValue cont =
            match findDynamicBinding (key ()) cont with
            | Some (Bool value) -> value
            | _ -> defaultValue

        /// The report leaves the initial value open. True is what IronKernel has always
        /// done: a result with no primary value has been an error here rather than a
        /// NaN that propagates silently into later arithmetic.
        let private isStrictArithmetic cont =
            booleanDynamicVariable strictArithmeticKey true cont

        /// R-1RK 12.7.1 phrases narrowing as advice the client asks for, so it starts
        /// off. Nothing here reads it beyond the accessor: see the divergence recorded
        /// for 12.7 in the conformance matrix.
        let private isNarrowArithmetic cont =
            booleanDynamicVariable narrowArithmeticKey false cont

        /// R-1RK 12.2: a real with no primary value is NaN here. That is where the
        /// indeterminate infinity combinations land -- infinity minus infinity, zero
        /// times infinity, infinity over infinity -- as well as inexact arithmetic's
        /// own NaN.
        let private hasNoPrimaryValue (value: obj) =
            match value with
            // An exact result always has a primary value. int is much the commonest
            // result of all, so it short-circuits the tests below rather than falling
            // through every one of them on the hottest path in the language.
            | :? int -> false
            | :? double as d -> Double.IsNaN d
            | :? Numerics.Complex as c -> Double.IsNaN c.Real || Double.IsNaN c.Imaginary
            | :? float32 as f -> Single.IsNaN f
            | _ -> false

        /// R-1RK 12.2: "an error is or is not signaled depending on the current value
        /// of the strict-arithmetic keyed dynamic variable". The variable is only read
        /// when the result actually has no primary value, so the ordinary path pays a
        /// type test rather than a walk of the continuation.
        let private continueNumeric env cont value =
            match value with
            | Obj result when hasNoPrimaryValue result && isStrictArithmetic cont ->
                fail (Default "arithmetic result has no primary value")
            | _ -> bounceContinue env cont value

        /// R-1RK 12.5.4 / 12.5.5: (+ . numbers) and (* . numbers) are variadic, with
        /// the empty sum zero and the empty product one. Folding left keeps the CLR
        /// extensions working -- (+ date timespan) is still a DateTime -- because each
        /// step is the same binary operation as before.
        let private foldNumeric op identity env cont args =
            match args with
            | [] -> bounceContinue env cont (Obj identity)
            | first :: rest ->
                let rec loop acc = function
                    | [] -> continueNumeric env cont acc
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
                | Choice2Of2 result -> continueNumeric env cont result
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
                | Choice2Of2 result -> continueNumeric env cont result
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
                    | Choice2Of2 result -> continueNumeric env cont result
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
            | :? Numerics.BigInteger as v -> Some(float v)
            | :? ExactRatio as r -> Some(float r.Numerator / float r.Denominator)
            | :? ExactInfinity as i ->
                Some(if i = ExactPositiveInfinity then Double.PositiveInfinity
                     else Double.NegativeInfinity)
            | :? byte as b -> Some(float b)
            | :? int as i -> Some(float i)
            | :? int64 as l -> Some(float l)
            | :? float32 as f -> Some(float f)
            | :? float as d -> Some d
            | _ -> None

        let private asComplex (value: obj) =
            match value with
            | :? Numerics.Complex as c -> Some c
            | :? Numerics.BigInteger as v -> Some(Numerics.Complex(float v, 0.0))
            | :? ExactRatio as r ->
                Some(Numerics.Complex(float r.Numerator / float r.Denominator, 0.0))
            | :? ExactInfinity as i ->
                Some(Numerics.Complex(
                        (if i = ExactPositiveInfinity then Double.PositiveInfinity
                         else Double.NegativeInfinity), 0.0))
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
                                // No primary value even in the complex plane, so R-1RK
                                // 12.2's rule applies here as it does to arithmetic:
                                // strict signals, non-strict returns the NaN.
                                if isStrictArithmetic cont then
                                    fail (Default(name + ": argument is outside the domain"))
                                else bounceContinue env cont (Obj(box result))
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
                        | :? Numerics.BigInteger | :? ExactRatio | :? ExactInfinity -> true
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

        /// The numerator and denominator of an exact argument; None for an inexact one.
        let private asExact (value: obj) =
            match value with
            | :? byte as b -> Some(Numerics.BigInteger(int b), Numerics.BigInteger.One)
            | :? int as i -> Some(Numerics.BigInteger i, Numerics.BigInteger.One)
            | :? int64 as l -> Some(Numerics.BigInteger l, Numerics.BigInteger.One)
            | :? Numerics.BigInteger as v -> Some(v, Numerics.BigInteger.One)
            | :? ExactRatio as r -> Some(r.Numerator, r.Denominator)
            | _ -> None

        /// An exact base raised to a whole exact power, as numerator and denominator.
        /// None when either argument is inexact, when the exponent is not a whole
        /// number -- a root is rarely rational -- or when the exact answer would be
        /// absurdly large, where the real result is what the caller wants anyway.
        let private exactPower (b: obj) (e: obj) =
            match asExact b, asExact e with
            | Some(numerator, denominator), Some(exponent, exponentDenominator)
                    when exponentDenominator.IsOne ->
                let magnitude = Numerics.BigInteger.Abs exponent
                let widest = max (Numerics.BigInteger.Abs numerator) denominator
                let bits = if widest.IsZero then 1L else widest.GetBitLength()
                if magnitude > Numerics.BigInteger Int32.MaxValue
                   || int64 magnitude * bits > 1000000L then None
                else
                    let raised (value: Numerics.BigInteger) =
                        Numerics.BigInteger.Pow(value, int magnitude)
                    if exponent.Sign >= 0 then Some(raised numerator, raised denominator)
                    else Some(raised denominator, raised numerator)
            | _ -> None

        /// R-1RK 12.9.6. Exact arguments give an exact result, so (expt 2 100) is the
        /// whole 31-digit integer and (expt 2 -3) is an eighth. The result used to be
        /// read back out of a double, which both rounded -- (expt 3 39) came back
        /// short by 11 -- and capped the answer at what a double can count.
        let exptReal env cont args =
            match args with
            | [Obj b; Obj e] ->
                match toFloat b, toFloat e with
                | Some baseValue, Some exponent ->
                    match exactPower b e with
                    // An exact zero to a negative power divides by zero, which R-1RK
                    // 12.8.2 makes an error rather than an infinity.
                    | Some(_, denominator) when denominator.IsZero ->
                        fail (Default "division by zero")
                    | Some(numerator, denominator) ->
                        bounceContinue env cont (Obj(ofRatio numerator denominator))
                    | None ->
                        let result = Math.Pow(baseValue, exponent)
                        if Double.IsNaN result then
                            // A negative base with a fractional exponent leaves the reals.
                            let complex =
                                Numerics.Complex.Pow(
                                    Numerics.Complex(baseValue, 0.0), Numerics.Complex(exponent, 0.0))
                            if Double.IsNaN complex.Real || Double.IsNaN complex.Imaginary then
                                fail (Default "expt: argument is outside the domain")
                            else bounceContinue env cont (ofComplexValue complex)
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

        /// R-1RK 4.8.2: the primitive type predicate for type ignore.
        let isIgnore env cont args =
            typePredicate (function Ignore -> true | _ -> false) env cont args

        /// R-1RK 13.1.1. The report gives it by signature only; a symbol is its name,
        /// so this is the symbol with that name.
        let stringToSymbol env cont args =
            match args with
            | [Obj value] when (value :? string) -> bounceContinue env cont (Atom(value :?> string))
            | [found] -> fail (TypeMismatch("string", found))
            | _ -> fail (NumArgs(1, args))

        /// R-1RK 4.7.2. The result must have an immutable evaluation structure and be
        /// initially equal? to the argument. A mutable argument is therefore copied --
        /// "if object is a mutable pair, then the result is not eq? to object" -- while
        /// one that is already immutable may come back as itself, which the report
        /// permits and `acquireImmutable` does. Contrast copy-es (6.4.2), which must
        /// return a fresh pair either way.
        let copyEsImmutable env cont args =
            match args with
            | [object'] -> bounceContinue env cont (acquireImmutable object')
            | _ -> fail (NumArgs(1, args))

        /// R-1RK 4.6: whether a pair may be mutated. Not a report feature -- it has no
        /// predicate for this -- but the distinction is now observable through
        /// set-car!, and a test can ask about it directly rather than by catching an
        /// error.
        let isImmutablePair env cont args =
            match args with
            | [Pair cell] -> bounceContinue env cont (Bool cell.immutable)
            | [_] -> bounceContinue env cont (Bool false)
            | _ -> fail (NumArgs(1, args))

        /// R-1RK 7.2.1: the primitive type predicate for type continuation.
        let isContinuation env cont args =
            typePredicate (function Continuation _ -> true | _ -> false) env cont args

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

        /// R-1RK 5.7.1. Returns `(p n a c)`: the number of pairs, the number of nils
        /// (0 or 1), the acyclic prefix length, and the cycle length of the improper
        /// list starting at the argument. `a + c = p`, and `n` and `c` are never both
        /// non-zero.
        ///
        /// This used to answer "acyclic, of this length" unconditionally, which was
        /// true only because no list could be cyclic. `set-cdr!` changed that, and this
        /// is the primitive the whole derived list library asks about shape, so it is
        /// the one place a cycle has to be measured rather than merely survived.
        ///
        /// Floyd: a second reference advancing at half speed meets the first inside any
        /// cycle. From that meeting point the cycle length is one lap, and restarting
        /// one reference at the beginning and advancing both in step meets at the
        /// cycle's first pair, which is the acyclic prefix length.
        let getListMetrics env cont args =
            match args with
            | [value] ->
                let cdrOf = function
                    | Pair cell -> Some cell.cdr
                    | _ -> None
                let rec advance steps current =
                    if steps = 0 then current
                    else
                        match cdrOf current with
                        | Some next -> advance (steps - 1) next
                        | None -> current
                // Look for a meeting point.
                let mutable slow = value
                let mutable fast = value
                let mutable met = false
                let mutable ended = false
                while not met && not ended do
                    match cdrOf fast with
                    | None -> ended <- true
                    | Some once ->
                        match cdrOf once with
                        | None -> ended <- true
                        | Some twice ->
                            fast <- twice
                            slow <- advance 1 slow
                            if obj.ReferenceEquals(slow, fast) then met <- true
                let pairs, nils, acyclic, cycle =
                    if not met then
                        // Acyclic: count pairs to the terminator, which is a nil or not.
                        let mutable current = value
                        let mutable count = 0
                        let mutable walking = true
                        while walking do
                            match cdrOf current with
                            | Some next -> count <- count + 1; current <- next
                            | None -> walking <- false
                        let terminatorIsNil = (match current with Nil -> 1 | _ -> 0)
                        count, terminatorIsNil, count, 0
                    else
                        // One lap from the meeting point gives the cycle length.
                        let mutable cycleLength = 1
                        let mutable current = advance 1 fast
                        while not (obj.ReferenceEquals(current, fast)) do
                            current <- advance 1 current
                            cycleLength <- cycleLength + 1
                        // Advancing in step from the start and from the meeting point
                        // brings both to the cycle's first pair.
                        let mutable fromStart = value
                        let mutable fromMeeting = fast
                        let mutable prefix = 0
                        while not (obj.ReferenceEquals(fromStart, fromMeeting)) do
                            fromStart <- advance 1 fromStart
                            fromMeeting <- advance 1 fromMeeting
                            prefix <- prefix + 1
                        prefix + cycleLength, 0, prefix, cycleLength
                let counted (n: int) = Obj(box n)
                bounceContinue env cont (
                    ofList [counted pairs; counted nils; counted acyclic; counted cycle])
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
                        | :? byte | :? int | :? int64 | :? Numerics.BigInteger -> true
                        | :? ExactRatio -> true
                        // R-1RK 12.8.1: a rational is a ratio of integers, which an
                        // infinity is not.
                        | :? ExactInfinity -> false
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

        /// The truncated quotient of a ratio and the remainder that goes with it. The
        /// denominator is positive by construction, so the remainder carries the sign
        /// of the numerator.
        let private truncatedParts (numerator: Numerics.BigInteger) (denominator: Numerics.BigInteger) =
            let truncated = Numerics.BigInteger.Divide(numerator, denominator)
            truncated, numerator - truncated * denominator

        let private floorExact numerator denominator =
            let truncated, remainder = truncatedParts numerator denominator
            if remainder.Sign < 0 then truncated - Numerics.BigInteger.One else truncated

        let private ceilingExact numerator denominator =
            let truncated, remainder = truncatedParts numerator denominator
            if remainder.Sign > 0 then truncated + Numerics.BigInteger.One else truncated

        let private truncateExact numerator denominator =
            fst (truncatedParts numerator denominator)

        /// Halfway cases go to even, matching the inexact path. Comparing twice the
        /// fractional part against the denominator keeps the test in exact integers.
        let private roundExact numerator denominator =
            let two = Numerics.BigInteger 2
            let below = floorExact numerator denominator
            let comparison = ((numerator - below * denominator) * two).CompareTo denominator
            if comparison < 0 then below
            elif comparison > 0 then below + Numerics.BigInteger.One
            elif (below % two).IsZero then below
            else below + Numerics.BigInteger.One

        /// R-1RK 12.8.4. Integers are returned unchanged; an exact ratio rounds to an
        /// exact integer, because 12.3.2 requires an exact argument to give an exact
        /// result; a real keeps its own numeric kind, which still satisfies integer?
        /// because that predicate accepts a float with an integral value.
        let private roundingPrimitive
                (applyExact: Numerics.BigInteger -> Numerics.BigInteger -> Numerics.BigInteger)
                (apply: float -> float)
                env cont args =
            match args with
            | [Obj value] ->
                match value with
                | :? byte | :? int | :? int64 | :? Numerics.BigInteger ->
                    bounceContinue env cont (Obj value)
                | :? ExactRatio as ratio ->
                    bounceContinue env cont (Obj(ofBig (applyExact ratio.Numerator ratio.Denominator)))
                // Rounding an infinity leaves it where it is.
                | :? ExactInfinity -> bounceContinue env cont (Obj value)
                | :? float32 as f -> bounceContinue env cont (Obj(box (float32 (apply (float f)))))
                | :? float as d -> bounceContinue env cont (Obj(box (apply d)))
                | _ -> fail (TypeMismatch("number", Obj value))
            | [found] -> fail (TypeMismatch("number", found))
            | _ -> fail (NumArgs(1, args))

        let floorReal env cont args = roundingPrimitive floorExact Math.Floor env cont args
        let ceilingReal env cont args = roundingPrimitive ceilingExact Math.Ceiling env cont args
        let truncateReal env cont args = roundingPrimitive truncateExact Math.Truncate env cont args

        /// Rounds halfway cases to even, per R-1RK 12.8.4 and IEEE 754.
        let roundReal env cont args =
            roundingPrimitive roundExact (fun d -> Math.Round(d, MidpointRounding.ToEven)) env cont args

        /// R-1RK 12.8.3, in least terms. A finite double is a dyadic rational, so
        /// doubling until the value is integral gives an exact numerator over a power
        /// of two. Both parts are arbitrary-size, so every finite real has an answer;
        /// the loop terminates because a double large enough to overflow is already
        /// integral, and the smallest subnormal reaches an integer within 1074 steps.
        let private exactRatioOf (value: float) =
            if Double.IsNaN value || Double.IsInfinity value then None
            else
                let two = Numerics.BigInteger 2
                let mutable numerator = value
                let mutable denominator = Numerics.BigInteger.One
                while Math.Floor numerator <> numerator do
                    numerator <- numerator * 2.0
                    denominator <- denominator * two
                Some(makeExactRatio (Numerics.BigInteger numerator) denominator)

        let private ratioPart wantNumerator env cont args =
            let pick (ratio: ExactRatio) =
                Obj(ofBig (if wantNumerator then ratio.Numerator else ratio.Denominator))
            let ofInteger (value: Numerics.BigInteger) =
                // An exact integer is itself over one, whatever its size.
                Obj(if wantNumerator then ofBig value else box 1)
            match args with
            | [Obj value] ->
                match value with
                | :? byte as b -> bounceContinue env cont (ofInteger (Numerics.BigInteger(int b)))
                | :? int as i -> bounceContinue env cont (ofInteger (Numerics.BigInteger i))
                | :? int64 as l -> bounceContinue env cont (ofInteger (Numerics.BigInteger l))
                | :? Numerics.BigInteger as v -> bounceContinue env cont (ofInteger v)
                | :? ExactRatio as ratio -> bounceContinue env cont (pick ratio)
                // R-1RK 12.8.3 is defined on rationals, which an infinity is not.
                | :? ExactInfinity -> fail (TypeMismatch("rational", Obj value))
                | :? float32 as f ->
                    match exactRatioOf (float f) with
                    | Some ratio -> bounceContinue env cont (pick ratio)
                    | None -> fail (TypeMismatch("rational", Obj value))
                | :? float as d ->
                    match exactRatioOf d with
                    | Some ratio -> bounceContinue env cont (pick ratio)
                    | None -> fail (TypeMismatch("rational", Obj value))
                | _ -> fail (TypeMismatch("number", Obj value))
            | [found] -> fail (TypeMismatch("number", found))
            | _ -> fail (NumArgs(1, args))

        // --- R-1RK 12.6, module Inexact -----------------------------------------
        //
        // The report sanctions this implementation directly (12.2): "An implementation
        // can fully support module Inexact without making any effort to maintain finite
        // bounds or robustness on inexact real numbers... The implementation might
        // simply take all inexact real numbers to be non-robust with upper bound
        // positive infinity and lower bound negative infinity, and describe each
        // inexact real number by a single internal real number and a tag indicating
        // that it is inexact." IronKernel's tag is the CLR type: float32 and double are
        // inexact, every other real is exact. Maintaining tighter bounds is what module
        // Narrow inexact (12.7) asks for, and that module stays absent.
        //
        // Two consequences follow and are worth naming. Every inexact real is
        // non-robust, so `robust?` is exactly "every argument is exact". And bounds are
        // never crossed, so no number is ever created with its lower bound above its
        // upper bound -- the report's `undefined` number (12.2) never arises, and
        // `undefined?` is correspondingly always false.

        let private isExactValue (value: obj) =
            match value with
            | :? byte | :? int | :? int64 | :? Numerics.BigInteger
            | :? ExactRatio | :? ExactInfinity -> true
            | _ -> false

        /// R-1RK 12.6.1. None of these are type predicates -- they take numbers, not
        /// arbitrary objects -- but none depend on a primary value either, so a NaN
        /// argument is answered rather than signalled.
        let private numberPredicate test env cont args =
            let rec loop = function
                | [] -> bounceContinue env cont (Bool true)
                | Obj value :: rest when isNumberValue value ->
                    if test value then loop rest else bounceContinue env cont (Bool false)
                | found :: _ -> fail (TypeMismatch("number", found))
            loop args

        let isExact env cont args = numberPredicate isExactValue env cont args

        /// A complex is inexact if any rectangular component is; IronKernel's complex
        /// components are always double, so every complex is inexact and none is exact.
        let isInexact env cont args = numberPredicate (isExactValue >> not) env cont args

        /// R-1RK 12.2: "an exact real is considered to be robust". Inexact reals here
        /// claim no bounds, so none of them is robust.
        let isRobust env cont args = numberPredicate isExactValue env cont args

        /// The undefined number arises only from an inexact real created with its lower
        /// bound above its upper bound, which infinite bounds never allow.
        let isUndefined env cont args = numberPredicate (fun _ -> false) env cont args

        /// The infinity of the same internal format as `value`, for the bounds of an
        /// inexact real (12.6.2). float32 keeps float32 so that the returned bounds
        /// carry the format the report asks for.
        let private internalInfinity (value: obj) positive =
            match value with
            | :? float32 ->
                box (if positive then Single.PositiveInfinity else Single.NegativeInfinity)
            | _ ->
                box (if positive then Double.PositiveInfinity else Double.NegativeInfinity)

        /// The 12.6.2 and 12.6.3 applicatives take a real, so a complex -- which the
        /// report leaves out pending "deeper analysis of the complex-representation
        /// issues involved" -- is a type error rather than a component-wise answer.
        let private realArgument args (apply: obj -> Step) =
            match args with
            | [Obj value] when isNumberValue value && not (value :? Numerics.Complex) ->
                apply value
            | [found] -> fail (TypeMismatch("real", found))
            | _ -> fail (NumArgs(1, args))

        /// R-1RK 12.6.2. An exact real is its own bounds. An inexact real is bounded
        /// only by the infinities, in the internal format of its primary value here and
        /// by the exact infinities of 12.3.2 for the exact form.
        let getRealInternalBounds env cont args =
            realArgument args (fun value ->
                if isExactValue value then
                    bounceContinue env cont (ofList [Obj value; Obj value])
                else
                    bounceContinue env cont (
                        ofList [Obj(internalInfinity value false); Obj(internalInfinity value true)]))

        let getRealExactBounds env cont args =
            realArgument args (fun value ->
                if isExactValue value then
                    bounceContinue env cont (ofList [Obj value; Obj value])
                else
                    bounceContinue env cont (
                        ofList [Obj(box ExactNegativeInfinity); Obj(box ExactPositiveInfinity)]))

        /// R-1RK 12.6.3. Both signal an error when there is no primary value, which
        /// keeps get-real-exact-primary's promise to return an exact real and
        /// get-real-internal-primary's to return a real whose primary is within its
        /// bounds.
        let getRealInternalPrimary env cont args =
            realArgument args (fun value ->
                if hasNoPrimaryValue value then
                    fail (Default "get-real-internal-primary: no primary value")
                else bounceContinue env cont (Obj value))

        /// The exact value of a double is exact: a finite one is a dyadic rational, and
        /// an infinite one is an exact infinity. That is stronger than the report
        /// requires -- with infinite bounds any exact real would be permissible -- but
        /// it is the closest to the primary value, which the report prefers.
        let private exactValueOf (value: obj) =
            if isExactValue value then Some value
            else
                match toFloat value with
                | None -> None
                | Some primary when Double.IsNaN primary -> None
                | Some primary when Double.IsPositiveInfinity primary ->
                    Some(box ExactPositiveInfinity)
                | Some primary when Double.IsNegativeInfinity primary ->
                    Some(box ExactNegativeInfinity)
                | Some primary ->
                    exactRatioOf primary
                    |> Option.map (fun ratio -> ofRatio ratio.Numerator ratio.Denominator)

        let getRealExactPrimary env cont args =
            realArgument args (fun value ->
                match exactValueOf value with
                | Some exact -> bounceContinue env cont (Obj exact)
                | None -> fail (Default "get-real-exact-primary: no primary value"))

        /// R-1RK 12.6.5. real->exact behaves just as get-real-exact-primary.
        let realToExact env cont args = getRealExactPrimary env cont args

        let private inexactValueOf (value: obj) =
            if isExactValue value then
                match value with
                | :? ExactInfinity as infinity ->
                    box (if infinity = ExactPositiveInfinity then Double.PositiveInfinity
                         else Double.NegativeInfinity)
                | _ ->
                    match toFloat value with
                    | Some primary -> box primary
                    | None -> box Double.NaN
            else value

        let realToInexact env cont args =
            realArgument args (fun value ->
                bounceContinue env cont (Obj(inexactValueOf value)))

        /// R-1RK 12.6.4. The result takes its primary value and robustness from real2;
        /// real1 and real3 are required to be reals but cannot narrow the result, since
        /// bounds here are always infinite. Constraining them is what module Narrow
        /// inexact (12.7) would ask for.
        let makeInexact env cont args =
            match args with
            | [Obj lower; Obj primary; Obj upper] when
                    [lower; primary; upper]
                    |> List.forall (fun v -> isNumberValue v && not (v :? Numerics.Complex)) ->
                bounceContinue env cont (Obj(inexactValueOf primary))
            | [_; _; _] -> fail (TypeMismatch("real", ofList args))
            | _ -> fail (NumArgs(3, args))

        /// R-1RK 12.6.6 and 12.7.1 are each "the binder and accessor of" a keyed
        /// dynamic variable, so the binder is one from 10.1.1 -- the setting follows the
        /// dynamic extent of its call, including across captured continuations -- and
        /// the accessor differs from a plain one only in answering with a default when
        /// no binder encloses it.
        let private withBooleanVariable key env cont args =
            match args with
            | [Bool _ as flag; combiner] ->
                let isolated = newEnvWithClr (ofEnvironment env) [] []
                bounceOperate
                    isolated
                    (makeDynamicBinding env cont (key ()) flag)
                    combiner
                    []
            | [found; _] -> fail (TypeMismatch("boolean", found))
            | _ -> fail (NumArgs(2, args))

        let private getBooleanVariable read env cont args =
            match args with
            | [] -> bounceContinue env cont (Bool(read cont))
            | _ -> fail (NumArgs(0, args))

        let withStrictArithmetic env cont args =
            withBooleanVariable strictArithmeticKey env cont args

        let getStrictArithmetic env cont args =
            getBooleanVariable isStrictArithmetic env cont args

        /// R-1RK 12.7.1. Setting this asks the implementation to maintain the most
        /// restrictive bounding and robustness information it correctly can. It is
        /// advice, and the report's only hard constraints are that whatever is
        /// maintained be correct and be no less restrictive when the variable is true
        /// than when it is false. IronKernel's bounds are the infinities either way, so
        /// both hold and nothing observable changes; the matrix records that rather
        /// than leaving a reader to discover it.
        let withNarrowArithmetic env cont args =
            withBooleanVariable narrowArithmeticKey env cont args

        let getNarrowArithmetic env cont args =
            getBooleanVariable isNarrowArithmetic env cont args

        let numeratorOf env cont args = ratioPart true env cont args

        let denominatorOf env cont args = ratioPart false env cont args

        /// R-1RK 12.5.8: a freshly allocated list of the quotient and the remainder.
        let divAndMod env cont args =
            match args with
            | [a; b] ->
                match opDivAndMod a b with
                | Choice2Of2 (quotient, remainder) ->
                    bounceContinue env cont (ofList [quotient; remainder])
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

                ofList [encapsulator; predicate; decapsulator] |> bounceContinue env cont
            | bad -> fail(NumArgs(0, bad))

        /// R-1RK 10.1.1. Each call returns a fresh `(binder accessor)` pair sharing a
        /// private key. The binder takes an object and a combiner, and calls the
        /// combiner with no operands in a fresh empty environment; within that call's
        /// dynamic extent the accessor, called with no operands, returns the object.
        ///
        /// The binding is a continuation frame rather than an entry on a side stack,
        /// so the extent is exactly right under first-class continuations: escaping
        /// the binder's call leaves the binding behind, and resuming a continuation
        /// captured inside the call re-enters it.
        let make_keyed_dynamic_variable env cont = function
            | [] ->
                let key = Guid.NewGuid()
                let primitive f =
                    PrimitiveOperative { identity = None; invoke = f }
                let binder =
                    Applicative(
                        primitive (fun e c -> function
                            | [value; combiner] ->
                                // "A fresh empty environment": no bindings and no
                                // parents, so the combiner sees nothing of the binder's
                                // caller. Capabilities are inherited rather than granted
                                // afresh -- an environment with no parents would
                                // otherwise carry every host capability, and the binder
                                // must not be a way to widen what its caller may do.
                                let isolated = newEnvWithClr (ofEnvironment e) [] []
                                bounceOperate isolated (makeDynamicBinding e c key value) combiner []
                            | bad -> fail (NumArgs(2, bad))))
                let accessor =
                    Applicative(
                        primitive (fun e c -> function
                            | [] ->
                                match findDynamicBinding key c with
                                | Some value -> bounceContinue e c value
                                | None ->
                                    fail (Default "keyed dynamic variable is unbound here")
                            | bad -> fail (NumArgs(0, bad))))

                ofList [binder; accessor] |> bounceContinue env cont
            | bad -> fail(NumArgs(0, bad))

        /// R-1RK 11.1.1, the static counterpart of 10.1.1. Each call returns a fresh
        /// `(binder accessor)` pair sharing a private key. The binder takes an object
        /// and an environment and returns a fresh child of that environment; the
        /// accessor, called with no operands anywhere in that child or its
        /// descendants, returns the object. Where a keyed *dynamic* variable is scoped
        /// by the extent of a call, this one is scoped by environment ancestry, so it
        /// survives being closed over and read long after the binder returned.
        ///
        /// The key is an ordinary binding under a name containing spaces, which the
        /// reader cannot produce in an atom. That alone is not privacy -- 13.1.1's
        /// `string->symbol` will build any name asked of it -- so what keeps the key
        /// private is the fresh GUID in it, which is never handed out. The spaces only
        /// keep it out of the reader's reach.
        ///
        /// Reusing the environment's own lookup is the point -- "the nearest such
        /// ancestor" then means exactly what it means for every other variable,
        /// including in an environment with several parents.
        let make_keyed_static_variable env cont = function
            | [] ->
                let key = "keyed static variable " + string (Guid.NewGuid())
                let primitive f =
                    PrimitiveOperative { identity = None; invoke = f }
                let binder =
                    Applicative(
                        primitive (fun e c -> function
                            | [value; (Environment _ as target)] ->
                                let child = newEnv [target]
                                match defineVar child key value with
                                | Choice1Of2 error -> fail error
                                | Choice2Of2 _ -> bounceContinue e c child
                            | [_; found] -> fail (TypeMismatch("environment", found))
                            | bad -> fail (NumArgs(2, bad))))
                let accessor =
                    Applicative(
                        // The environment here is the one the call appears in, which is
                        // what makes the variable static: a combination is evaluated
                        // where it is written, so an accessor call inside a procedure
                        // body reads from that procedure's environment, not its caller's.
                        primitive (fun e c -> function
                            | [] ->
                                match getVar' e key with
                                | Some value -> bounceContinue e c value
                                | None -> fail (Default "keyed static variable is unbound here")
                            | bad -> fail (NumArgs(0, bad))))

                ofList [binder; accessor] |> bounceContinue env cont
            | bad -> fail(NumArgs(0, bad))

        let primitiveApplicatives : (string * (LispVal -> LispVal -> LispVal list -> Step)) list =
            [
                  ("eval", evaluate);
                  ("wrap", wrap);
                  ("unwrap", unwrap);
                  ("load", loadAndEval);
                  ("call/cc", callcc);
                  ("continuation->applicative", continuationToApplicative);
                  ("apply-continuation", applyContinuation);
                  ("extend-continuation", extendContinuation);
                  ("continuation?", isContinuation);
                  ("copy-es-immutable", copyEsImmutable);
                  ("ignore?", isIgnore);
                  ("string->symbol", stringToSymbol);
                  ("port?", isPort);
                  ("input-port?", isInputPort);
                  ("output-port?", isOutputPort);
                  ("close-input-file", closeInputFile);
                  ("close-output-file", closeOutputFile);
                  ("get-current-input-port", getCurrentInputPort);
                  ("get-current-output-port", getCurrentOutputPort);
                  ("with-input-from-file", withInputFromFile);
                  ("with-output-to-file", withOutputToFile);
                  ("call-with-input-file", callWithInputFile);
                  ("call-with-output-file", callWithOutputFile);
                  ("read", readValue);
                  ("write", writeValue);
                  ("set-car!", setCar);
                  ("set-cdr!", setCdr);
                  ("immutable-pair?", isImmutablePair);
                  ("guard-continuation", guardContinuation);
                  ("guard-dynamic-extent", guardDynamicExtent);
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
                  ("eq?", eq);
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
                  ("make-keyed-dynamic-variable", make_keyed_dynamic_variable);
                  ("make-keyed-static-variable", make_keyed_static_variable);
                  ("exact?", isExact);
                  ("inexact?", isInexact);
                  ("robust?", isRobust);
                  ("undefined?", isUndefined);
                  ("get-real-internal-bounds", getRealInternalBounds);
                  ("get-real-exact-bounds", getRealExactBounds);
                  ("get-real-internal-primary", getRealInternalPrimary);
                  ("get-real-exact-primary", getRealExactPrimary);
                  ("make-inexact", makeInexact);
                  ("real->inexact", realToInexact);
                  ("real->exact", realToExact);
                  ("with-strict-arithmetic", withStrictArithmetic);
                  ("get-strict-arithmetic?", getStrictArithmetic);
                  ("with-narrow-arithmetic", withNarrowArithmetic);
                  ("get-narrow-arithmetic?", getNarrowArithmetic);
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
                    && (not (Set.contains name
                                (Set.ofList
                                    [ "print"; "printf"; "show"; "read"; "write"
                                      "close-input-file"; "close-output-file"
                                      "get-current-input-port"; "get-current-output-port"
                                      "with-input-from-file"; "with-output-to-file"
                                      "call-with-input-file"; "call-with-output-file" ]))
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
            // R-1RK 7.2.6 and 7.2.7 are continuations, not combiners, so they are bound
            // as values rather than built from the applicative lists.
            let continuations =
                [ "root-continuation", rootContinuation ()
                  "error-continuation", errorContinuation () ]
            io @ operatives @ applicatives @ generated @ continuations
            |> bindVars (newEnvWithCapabilities capabilities [])

        let makePrimitiveBindings () =
            makePrimitiveBindingsForProfile Unrestricted

        /// Shared bootstrap environment (REPL / CLI). Prefer `makePrimitiveBindings` in tests.
        let primitiveBindings = makePrimitiveBindings ()
