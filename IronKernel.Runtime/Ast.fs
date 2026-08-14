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
    }

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
    }
    and NativeFuncRecord = { 
        cont : LispVal -> LispVal -> LispVal -> (LispVal list) option -> Step
        args : (LispVal list) option
    }
    and DeferredCode =
        | KernelCode of (LispVal list)
        | NativeCode of NativeFuncRecord
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
        | List of LispVal list
        | DottedList of (LispVal list * LispVal)
        | Bool of bool
        | Environment of EnvironmentRecord
        | PrimitiveOperative of PrimitiveOperativeRecord
        | ContractedCombiner of ContractedCombinerRecord
        | Operative of OperativeRecord
        | Applicative of LispVal
        | IOFunc of HostCapability * (LispVal list -> ThrowsError<LispVal>)
        | Port of System.IO.FileStream
        | Inert
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

    and ThrowsError<'a> = Choice<LispError,'a>

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

