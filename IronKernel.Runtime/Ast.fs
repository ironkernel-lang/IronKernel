namespace IronKernel

module Ast =

    type SourcePosition = {
        offset : int64
        line : int64
        column : int64
    }

    type SourceSpan = {
        sourceName : string
        startPosition : SourcePosition
        endPosition : SourcePosition
    }

    type HostCapability =
        | RawClrInterop
        | HostIO
        | SourceLoading
        | HostAsync
        | GeneratedClr of string

    type CapabilityProfile =
        | Minimal
        | Safe
        | Unrestricted

    type CapabilitySet = Set<HostCapability>

    type ContractMode =
        | RawOperands
        | EvaluatedArguments

    type ContractShape =
        | AnyShape
        | NumberShape
        | IntegerShape
        | StringShape
        | BooleanShape
        | AtomShape
        | ListShape
        | PromptTagShape
        | ResumptionShape
        | DateTimeShape
        | TimeSpanShape
        /// Matches when any member shape matches; lets combiners like `+`
        /// declare number-or-datetime operands instead of falling back to any.
        | OneOfShape of ContractShape list

    type ContractEffect =
        | Pure
        | Effectful

    type ContractTrust =
        | Certified
        | Asserted

    type OperativeContract = {
        name : string
        mode : ContractMode
        operands : ContractShape list
        result : ContractShape
        effect : ContractEffect
        inlineable : bool
        trust : ContractTrust
        /// `None` fixes the arity at `operands.Length`. `Some n` accepts n or more
        /// arguments, matching argument i against `operands[i]` and every argument
        /// past the end against the last declared shape. R-1RK's arithmetic is
        /// variadic ((+ . numbers)), so a fixed arity cannot describe it.
        minimumOperands : int option
    }

    /// The two exact real infinities (R-1RK 12.3.2). "Every implementation of Kernel
    /// must support the two exact real infinity objects, positive and negative": they
    /// are part of the required baseline rather than an optional module, and several
    /// of the report's behaviours are stated in terms of them -- (max) is exact
    /// negative infinity, (gcd) is exact positive infinity, and the bounds of an
    /// inexact real are infinite (12.6.2).
    ///
    /// Nullary union cases are singletons, so each infinity is one object: the report
    /// speaks of "the two exact real infinity objects", and eq? agrees.
    type ExactInfinity =
        | ExactPositiveInfinity
        | ExactNegativeInfinity
        override this.ToString() =
            match this with
            | ExactPositiveInfinity -> "#e+infinity"
            | ExactNegativeInfinity -> "#e-infinity"

    /// An exact ratio of integers (R-1RK 12.8), always kept in least terms with a
    /// positive denominator. Normalising on construction is what makes the record's
    /// structural equality agree with numeric equality, so `eqv?` needs no special
    /// case and 2/4 and 1/2 are the same value.
    type ExactRatio =
        { Numerator : System.Numerics.BigInteger
          Denominator : System.Numerics.BigInteger }
        override this.ToString() =
            string this.Numerator + "/" + string this.Denominator

    /// The caller must reject a zero denominator first; R-1RK 12.8.2 signals an error
    /// for that rather than producing an infinity.
    let makeExactRatio (numerator: System.Numerics.BigInteger) (denominator: System.Numerics.BigInteger) =
        let negative = denominator.Sign < 0
        let numerator = if negative then -numerator else numerator
        let denominator = if negative then -denominator else denominator
        let divisor =
            System.Numerics.BigInteger.GreatestCommonDivisor(
                System.Numerics.BigInteger.Abs numerator, denominator)
        let divisor =
            if divisor.IsZero then System.Numerics.BigInteger.One else divisor
        { Numerator = numerator / divisor; Denominator = denominator / divisor }

    type ContinuationType = Full | Delimited

    /// Trampoline step used by the CPS evaluator / compiler runtime.
    type Step =
        | Done of ThrowsError<LispVal>
        | More of (unit -> Step)
        | Await of AwaitRequest

    and AwaitRequest = {
        register : (ThrowsError<LispVal> -> unit) -> unit
        resume : ThrowsError<LispVal> -> Step
    }

    and OperativeRecord = {
        prms    : LispVal ;
        envarg  : string;
        body    : LispVal list;
        closure : LispVal
        /// Compiled form of `body`, used in preference to interpreting it. Filled in
        /// lazily on first application (ADR 0004). `body` stays authoritative so
        /// anything reading a combiner's source, and any artifact built without the
        /// compiler, keeps working. The write is a single reference assignment and
        /// recompiling is pure, so a race can only duplicate work, never corrupt.
        mutable compiledBody : ((LispVal -> LispVal -> Step) list) option
    }
    and NativeFuncRecord = { 
        cont : LispVal -> LispVal -> LispVal -> (LispVal list) option -> Step
        args : (LispVal list) option
    }
    and DeferredCode =
        | KernelCode of (LispVal list)
        /// A compiled procedure body, kept as a *list* of compiled forms rather
        /// than one delegate. Continuation capture and the stepping rule both work
        /// on the remaining-forms tail, so keeping the list preserves proper tail
        /// calls and lets a captured continuation resume mid-body, exactly as
        /// `KernelCode` does. Typed as a plain function so `IronKernel.Runtime`
        /// stays independent of the compiler (ADR 0002).
        | CompiledCode of (LispVal -> LispVal -> Step) list
        | NativeCode of NativeFuncRecord
        /// A keyed dynamic binding (R-1RK 10.1.1). It is not code -- returning
        /// through it just ends the binding -- but it lives here so that the binding
        /// is a *continuation frame* rather than an entry on a side stack. That is
        /// what makes the dynamic extent right in the presence of first-class
        /// continuations: capturing a continuation inside the extent captures the
        /// binding with it, and resuming that continuation from outside re-enters
        /// the binding, where a push/pop discipline would already have popped it.
        | DynamicBinding of System.Guid * LispVal
        /// The entry/exit guards of R-1RK 7.2.4, carried on the *outer* continuation
        /// that guard-continuation builds. Like a dynamic binding it holds no code --
        /// receiving a value normally just passes it onward -- but living in the chain
        /// is what makes the extent tests of 7.1 mean what the report says: whether a
        /// guard applies to an abnormal pass is decided by whether its continuation is
        /// an ancestor of the source or of the destination.
        | GuardBarrier of GuardBarrierRecord
    and GuardBarrierRecord = {
        /// Each clause is a selector continuation and an interceptor applicative,
        /// already taken apart and copied, so later mutation of the argument lists
        /// cannot change them (7.2.4).
        entryClauses : (LispVal * LispVal) list
        exitClauses  : (LispVal * LispVal) list
        /// The dynamic environment of the guard-continuation call, which interceptors
        /// are called in.
        guardEnv     : LispVal
        /// The inner continuation, a child of the outer one holding this record. Exit
        /// guards are about leaving *its* extent, which is what keeps an interceptor
        /// calling its second argument from re-triggering the guard it came from.
        /// Assigned once, immediately after both continuations are built.
        mutable inner : ContinuationRecord option
    }
    and ContinuationRecord = {
        closure     : LispVal
        currentCont : DeferredCode option
        nextCont    : LispVal option
        args        : (LispVal list) option
    }
    and PromptFrame = {
        parentCont : LispVal
        tag : System.Guid option
        handler : LispVal option
    }
    and ResumptionRecord = {
        continuation : LispVal
        mutable consumed : int
    }
    and EncapsulationRecord = {
        tag     : System.Guid
        value   : LispVal
    }
    and PrimitiveIdentity =
        | PrimitiveIf
        | PrimitiveDefine
    and PrimitiveOperativeRecord = {
        identity : PrimitiveIdentity option
        invoke : LispVal -> LispVal -> LispVal list -> Step
    }
    and ContractedCombinerRecord = {
        combiner : LispVal
        contract : OperativeContract
    }
    and BindingState = {
        value : LispVal
        version : int64
    }
    and BindingCell = {
        id : int64
        mutable state : BindingState
    }
    /// Frame-local bindings. A dictionary keeps the global/stdlib frame O(1);
    /// within-frame shadowing overwrites the entry, matching the previous
    /// first-match-wins association-list semantics.
    and Env = System.Collections.Generic.Dictionary<string, BindingCell>
    and EnvironmentRecord = {
        bindings : Env
        parents : LispVal list
        capabilities : CapabilitySet
        /// Prefixes tried when resolving short CLR type names (env-local).
        clrNamespaces : string list ref
        /// Short name → full CLR type name (env-local).
        clrAliases : Map<string, string> ref
    }
    and LispVal = 
        | Atom of string 
        /// R-1RK's pair. A list is a chain of these ending at Nil; an improper list
        /// ends at anything else. ADR 0005: the cell is mutable so that set-car! and
        /// set-cdr! have somewhere to write, though nothing mutates one yet.
        | Pair of PairCell
        | Bool of bool
        | Environment of EnvironmentRecord
        | PrimitiveOperative of PrimitiveOperativeRecord
        | ContractedCombiner of ContractedCombinerRecord
        | Operative of OperativeRecord
        | Applicative of LispVal
        | IOFunc of HostCapability * (LispVal list -> ThrowsError<LispVal>)
        /// R-1RK 15. A stream rather than a FileStream, so that the standard input
        /// and output can be ports too (15.1.4).
        | Port of System.IO.Stream
        | Inert
        /// R-1RK 4.8. The one value of type ignore. In a parameter tree it matches an
        /// operand and binds nothing, and as $vau's environment parameter it declines
        /// the dynamic environment.
        | Ignore
        | Nil
        | Obj of obj
        | Continuation of ContinuationRecord * PromptFrame option * ContinuationType
        | PromptTag of System.Guid
        | Resumption of ResumptionRecord
        | Status of string
        | Keyword of string
        | Vector of LispVal array
        | Encapsulation of EncapsulationRecord
        /// CLR-compiled combiner (Expression / IL).
        | CompiledCombiner of (LispVal -> LispVal -> LispVal list -> Step)

    /// Reference equality, not structural: two cells are the same pair only if they
    /// are the same object, which is what `eq?` will come to mean (ADR 0005 phase 2).
    /// It also keeps the compiler-generated equality on LispVal from walking a cycle
    /// once one can exist.
    and [<ReferenceEquality>] PairCell = {
        mutable car : LispVal
        mutable cdr : LispVal
        /// R-1RK distinguishes mutable from immutable pairs (4.7.2). Everything is
        /// built immutable until phase 3 gives set-car! something to refuse.
        mutable immutable : bool
    }

    and LispError = 
       | NumArgs of int * LispVal list
       | TypeMismatch of string * LispVal
       | ClrTypeMismatch of string * string
       | Parser of string
       | BadSpecialForm of string*LispVal
       | NotFunction of string*string
       | UnboundVar of string*string
       | Default of string
       | ClrException of System.Exception
       | LocatedError of SourceSpan * string option * LispError
       | CapabilityDenied of string
       | ContractViolation of string
       /// Not an error: an abnormal pass reached root-continuation (R-1RK 7.2.6), so
       /// the Kernel session ends with this value. It travels the error channel
       /// because that is the one path that unwinds a computation without a
       /// continuation to receive the result, and the drivers recognise it.
       | SessionExit of LispVal

    and ThrowsError<'a> = Choice<LispError,'a>

    /// R-1RK 4.7.2 at the value level: the object with an immutable evaluation
    /// structure -- the set of pairs reachable from it without passing through a
    /// non-pair. `$vau` (4.10.3) acquires immutable copies of what it captures, which
    /// is what keeps an algorithm from changing under the combiner that captured it,
    /// and what makes `OperativeRecord.compiledBody`'s memo of a compiled body sound.
    ///
    /// A structure already wholly immutable is returned as it is, which 4.7.2 permits
    /// for an immutable pair and which keeps the common case -- capturing structure the
    /// reader produced -- free. Anything else is copied, and the copy stops at
    /// non-pairs, so shared non-pair referents stay `eq?` as the report requires.
    /// Already-copied cells are remembered, so sharing is preserved and a cyclic
    /// structure terminates.
    let acquireImmutable (value: LispVal) =
        let rec allImmutable seen current =
            match current with
            | Pair cell ->
                if not cell.immutable then false
                elif List.exists (fun other -> obj.ReferenceEquals(other, cell)) seen then true
                else
                    let seen = cell :: seen
                    allImmutable seen cell.car && allImmutable seen cell.cdr
            | _ -> true
        if allImmutable [] value then value
        else
            let copies = System.Collections.Generic.Dictionary<PairCell, LispVal>(HashIdentity.Reference)
            let rec copy current =
                match current with
                | Pair cell ->
                    match copies.TryGetValue cell with
                    | true, existing -> existing
                    | _ ->
                        let fresh = { car = Nil; cdr = Nil; immutable = true }
                        copies.[cell] <- Pair fresh
                        fresh.car <- copy cell.car
                        fresh.cdr <- copy cell.cdr
                        Pair fresh
                | other -> other
            copy value

    /// The same, for a body held as a list of forms rather than as one structure.
    let acquireImmutableForms (forms: LispVal list) =
        if forms |> List.forall (fun form -> obj.ReferenceEquals(acquireImmutable form, form))
        then forms
        else forms |> List.map acquireImmutable

    /// The pair constructors. Data a Kernel program builds at run time is mutable, so
    /// that `(set-car! (list 1 2) 0)` has somewhere to write; structure the reader
    /// produces is immutable, because it is the text of an algorithm rather than data
    /// the program made (R-1RK 4.7.2's rationale: mutating an algorithm "ought to be
    /// difficult to do by accident").
    let cons car cdr = Pair { car = car; cdr = cdr; immutable = false }

    let consImmutable car cdr = Pair { car = car; cdr = cdr; immutable = true }

    let ofList (values: LispVal list) = List.foldBack cons values Nil

    let ofDotted (values: LispVal list) (tail: LispVal) = List.foldBack cons values tail

    let ofListImmutable (values: LispVal list) = List.foldBack consImmutable values Nil

    let ofDottedImmutable (values: LispVal list) (tail: LispVal) =
        List.foldBack consImmutable values tail

    /// Matches a proper list -- a chain of pairs ending at Nil -- and yields its
    /// elements. `Nil` matches as the empty list, so `| List [] ->` still reads the
    /// empty list and `| List (x :: rest) ->` still destructures a non-empty one.
    ///
    /// A cyclic argument is not a proper list, and saying so has to be cheap and
    /// certain now that `set-cdr!` can build one: a second pointer advancing at half
    /// speed meets the first inside any cycle, so the walk ends without a step limit to
    /// tune and without allocating anything to remember where it has been.
    let (|List|_|) (value: LispVal) : LispVal list option =
        let mutable slow = value
        let mutable current = value
        let mutable acc = []
        let mutable steps = 0
        let mutable result = None
        let mutable walking = true
        while walking do
            match current with
            | Nil ->
                result <- Some(List.rev acc)
                walking <- false
            | Pair cell ->
                acc <- cell.car :: acc
                current <- cell.cdr
                steps <- steps + 1
                if steps % 2 = 0 then
                    match slow with
                    | Pair slowCell -> slow <- slowCell.cdr
                    | _ -> ()
                    if obj.ReferenceEquals(slow, current) then walking <- false
            | _ -> walking <- false
        result

    /// Matches an improper list: at least one pair, ending at something other than
    /// Nil. Yields the elements before the tail, and the tail. Cyclic arguments end the
    /// walk the same way, and match neither this nor `List`.
    let (|DottedList|_|) (value: LispVal) : (LispVal list * LispVal) option =
        let mutable slow = value
        let mutable current = value
        let mutable acc = []
        let mutable steps = 0
        let mutable result = None
        let mutable walking = true
        while walking do
            match current with
            | Pair cell ->
                acc <- cell.car :: acc
                current <- cell.cdr
                steps <- steps + 1
                if steps % 2 = 0 then
                    match slow with
                    | Pair slowCell -> slow <- slowCell.cdr
                    | _ -> ()
                    if obj.ReferenceEquals(slow, current) then walking <- false
            | Nil -> walking <- false
            | tail ->
                if not (List.isEmpty acc) then result <- Some(List.rev acc, tail)
                walking <- false
        result

    let makeObj = (fun x -> x :> obj  |> Obj)

    let allHostCapabilities : CapabilitySet =
        Set.ofList
            [ RawClrInterop
              HostIO
              SourceLoading
              HostAsync
              GeneratedClr "safe" ]

    let private inheritClrState frames =
        let namespaces =
            frames
            |> List.choose (function Environment record -> Some !record.clrNamespaces | _ -> None)
            |> List.concat
            |> List.distinct
        let aliases =
            frames
            |> List.choose (function Environment record -> Some !record.clrAliases | _ -> None)
            |> List.fold
                (fun acc map ->
                    Map.fold
                        (fun merged key value ->
                            if Map.containsKey key merged then merged
                            else Map.add key value merged)
                        acc
                        map)
                Map.empty
        ref namespaces, ref aliases

    let newEnvWithClr capabilities frames clrSources =
        let clrNamespaces, clrAliases = inheritClrState clrSources
        Environment
            { bindings = Env()
              parents = frames
              capabilities = capabilities
              clrNamespaces = clrNamespaces
              clrAliases = clrAliases }

    let newEnvWithCapabilities capabilities frames =
        newEnvWithClr capabilities frames frames

    let newEnv = function
        | [Environment parent] as frames ->
            Environment
                { bindings = Env()
                  parents = frames
                  capabilities = parent.capabilities
                  clrNamespaces = ref !parent.clrNamespaces
                  clrAliases = ref !parent.clrAliases }
        | frames ->
            let inherited =
                frames
                |> List.choose (function Environment record -> Some record.capabilities | _ -> None)
            let capabilities =
                match inherited with
                | [] -> allHostCapabilities
                | first :: rest -> List.fold Set.intersect first rest
            newEnvWithCapabilities capabilities frames

    let newContinuation env = Continuation ({closure = env; currentCont = None; nextCont = None; args = None}, None, Full)

    let makeCPS env cont f =
        match cont with
        | Continuation(cr, mc, ct) ->
            Continuation ({closure = env; currentCont = Some (NativeCode { cont = f ; args = None} ); nextCont = Some (Continuation(cr,None, Full)) ; args = None},mc, ct)
        | _ -> invalidArg (nameof cont) "Expected a continuation"

    /// Pushes a keyed dynamic binding onto `cont`, the same shape `makeCPS` builds:
    /// the metacontinuation stays at the outermost record, since the evaluator treats
    /// one nested inside `nextCont` as an internal error.
    let makeDynamicBinding env cont key value =
        match cont with
        | Continuation(cr, mc, ct) ->
            Continuation (
                { closure = env
                  currentCont = Some (DynamicBinding(key, value))
                  nextCont = Some (Continuation(cr, None, Full))
                  args = None },
                mc, ct)
        | _ -> invalidArg (nameof cont) "Expected a continuation"

    let unwords (lst: string list) = System.String.Join(" ",List.toArray(*mono needs this call toArray*) lst)
    let unwordsa (lst: string array) = System.String.Join(" ",lst)

    type private RenderWork =
        | Render of LispVal
        | Append of string

    let showVal value =
        let output = System.Text.StringBuilder()
        let mutable pending = [Render value]

        let prependValues values =
            let mutable hasLaterValue = false
            for child in List.rev values do
                if hasLaterValue then
                    pending <- Render child :: Append " " :: pending
                else
                    pending <- Render child :: pending
                    hasLaterValue <- true

        while not pending.IsEmpty do
            let work = pending.Head
            pending <- pending.Tail
            match work with
            | Append text -> output.Append(text) |> ignore
            | Render current ->
                match current with
                | Atom name -> output.Append(name) |> ignore
                | Bool true -> output.Append("#t") |> ignore
                | Bool false -> output.Append("#f") |> ignore
                | List contents ->
                    pending <- Append ")" :: pending
                    prependValues contents
                    pending <- Append "(" :: pending
                | DottedList(head, tail) ->
                    pending <- Render tail :: Append ")" :: pending
                    pending <- Append " & " :: pending
                    prependValues head
                    pending <- Append "(" :: pending
                // A pair that is neither proper nor improper has come back on itself.
                // Nothing builds one yet; ADR 0005 phase 4 gives cyclic structure its
                // external representation, and until then saying so beats looping.
                | Pair _ -> output.Append("<circular list>") |> ignore
                | Applicative applicative ->
                    pending <- Render applicative :: Append " >" :: pending
                    pending <- Append "<applicative " :: pending
                | PrimitiveOperative _ -> output.Append("<primitive operative>") |> ignore
                | ContractedCombiner contracted ->
                    output.Append("<contracted ").Append(contracted.contract.name).Append(">") |> ignore
                | Operative { prms = args } ->
                    pending <- Render args :: Append "))" :: pending
                    pending <- Append "(vau (" :: pending
                | Port _ -> output.Append("<IO port>") |> ignore
                | IOFunc _ -> output.Append("<IO primitive>") |> ignore
                | Environment _ -> output.Append("<environment>") |> ignore
                | Nil -> output.Append("()") |> ignore
                | Obj (:? System.Type as objectType) ->
                    output.Append("<type ").Append(objectType.FullName).Append(">") |> ignore
                | Obj value ->
                    output.Append("<obj ") |> ignore
                    if isNull value then
                        output.Append("null") |> ignore
                    else
                        output.Append(value.ToString()).Append(" : ").Append(value.GetType().Name) |> ignore
                    output.Append(">") |> ignore
                | Continuation _ -> output.Append("<continuation>") |> ignore
                | PromptTag _ -> output.Append("<prompt-tag>") |> ignore
                | Resumption _ -> output.Append("<resumption>") |> ignore
                | Status status -> output.Append("error : ").Append(status) |> ignore
                | Inert -> output.Append("#inert") |> ignore
                | Ignore -> output.Append("#ignore") |> ignore
                | Keyword name -> output.Append(":").Append(name) |> ignore
                | Vector contents ->
                    pending <- Append "]" :: pending
                    prependValues (Array.toList contents)
                    pending <- Append "[" :: pending
                | Encapsulation { tag = tag } ->
                    output.Append("encapsulation: ").Append(tag.ToString()) |> ignore
                | CompiledCombiner _ -> output.Append("<compiled combiner>") |> ignore

        output.ToString()

    let unwordsList values = values |> List.map showVal |> unwords
    let unwordsArray values = values |> Array.map showVal |> unwordsa
    let printBindings (bnds: Env) =
        Seq.fold
            (fun (acc:string) (KeyValue(name, cell)) ->
                acc + "(" + name + ": " + showVal cell.state.value + " )\n")
            ""
            bnds

