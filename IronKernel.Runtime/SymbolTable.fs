namespace IronKernel

module SymbolTable =

    open System
    open System.Threading
    open Ast
    open Errors

    /// What a guarded specialization needs is that `name` still denotes a primitive
    /// with `expectedIdentity` in the environment the code is *running* in. The
    /// binding cell it denoted when the form was compiled is deliberately not part of
    /// that (ADR 0008): pinning it rejected a binding that had been rebound and
    /// restored, and rejected every environment except the compiling one -- and the
    /// package format never carried it anyway, since a decoded guard is rebuilt
    /// against the decoding environment.
    type BindingGuard = {
        name : string
        expectedIdentity : PrimitiveIdentity
    }

    let mutable private nextBindingId = 0L

    let private newBindingCell value =
        { id = Interlocked.Increment(&nextBindingId)
          state = { value = value; version = 0L } }

    let private updateBindingCell cell value =
        let state = cell.state
        cell.state <- { value = value; version = state.version + 1L }

    let keyEq name (k,_) = k = name

    let private tryFindBinding name (bindings: Env) =
        match bindings.TryGetValue name with
        | true, cell -> ValueSome cell
        | _ -> ValueNone

    /// Resolve a binding cell without boxing the result. Parent lists are fixed
    /// at construction, so environment graphs are acyclic; a pending stack and
    /// visited set exist only for frames that declare multiple parents. The
    /// common single-parent chain walks without allocating.
    let tryResolveBindingCell env var : BindingCell voption =
        let mutable visited : Collections.Generic.HashSet<obj> = null
        let mutable pending : LispVal list = []
        let mutable current = env
        let mutable result = ValueNone
        let mutable running = true
        // Kept inline (not a local function): closing over the mutable loop
        // state would heap-allocate it and put an allocation on every lookup.
        let inline advance () =
            match pending with
            | next :: rest ->
                current <- next
                pending <- rest
            | [] -> running <- false

        while running do
            match current with
            | Environment record when isNull visited || visited.Add(record :> obj) ->
                match tryFindBinding var record.bindings with
                | ValueSome cell ->
                    result <- ValueSome cell
                    running <- false
                | ValueNone ->
                    match record.parents with
                    | [(Environment _ as parent)] -> current <- parent
                    | [] | [_] -> advance ()
                    | parents ->
                        if isNull visited then
                            visited <-
                                Collections.Generic.HashSet<obj>(
                                    Collections.Generic.ReferenceEqualityComparer.Instance)
                            visited.Add(record :> obj) |> ignore
                        let mutable environmentParents = []
                        for parent in List.rev parents do
                            match parent with
                            | Environment _ -> environmentParents <- parent :: environmentParents
                            | _ -> ()
                        match environmentParents with
                        | first :: rest ->
                            current <- first
                            pending <- rest @ pending
                        | [] -> advance ()
            | _ -> advance ()

        result

    let resolveBindingCell env var =
        tryResolveBindingCell env var |> ValueOption.toOption

    /// A frame scanned (and missed) on the way to a resolved binding, with the
    /// number of bindings it held at resolution time. Frame dictionaries only
    /// grow — bindings are never removed — so an unchanged count proves no new
    /// definition could have shadowed the resolved cell through this frame.
    [<Struct>]
    type VisitedFrame = {
        frame : EnvironmentRecord
        bindingCount : int
    }

    /// A resolution along a simple single-parent chain: the cell, the frame holding
    /// it, and how many frames were skipped to reach it.
    ///
    /// Call sites inside a procedure body see a *fresh* frame on every call, because
    /// application binds parameters in a new environment. A cache keyed on
    /// environment identity therefore never hits there. Revalidating a chain
    /// resolution instead costs one dictionary miss per skipped frame and allocates
    /// nothing, and stays valid as the frame changes.
    type ChainResolution = {
        cell : BindingCell
        owner : EnvironmentRecord
        depth : int
    }

    /// `ValueNone` when the walk meets a frame with anything other than exactly one
    /// environment parent; such chains keep the general resolver.
    let tryResolveAlongChain env var : ChainResolution voption =
        let mutable current = env
        let mutable depth = 0
        let mutable result = ValueNone
        let mutable running = true
        while running do
            match current with
            | Environment record ->
                match record.bindings.TryGetValue var with
                | true, cell ->
                    result <- ValueSome { cell = cell; owner = record; depth = depth }
                    running <- false
                | _ ->
                    match record.parents with
                    | [(Environment _ as parent)] ->
                        depth <- depth + 1
                        current <- parent
                    | _ -> running <- false
            | _ -> running <- false
        result

    /// True when resolving `var` from `env` would still reach `resolution.owner`:
    /// every nearer frame must still lack the name, and the frame at that depth must
    /// be the same object. Frames only gain bindings, so an absent name stays absent
    /// unless something defines it, which this check sees.
    let chainResolutionHolds env var (resolution: ChainResolution) =
        let mutable current = env
        let mutable remaining = resolution.depth
        let mutable holds = false
        let mutable running = true
        while running do
            match current with
            | Environment record ->
                if remaining = 0 then
                    holds <- obj.ReferenceEquals(record, resolution.owner)
                    running <- false
                elif record.bindings.ContainsKey var then
                    running <- false
                else
                    match record.parents with
                    | [(Environment _ as parent)] ->
                        remaining <- remaining - 1
                        current <- parent
                    | _ -> running <- false
            | _ -> running <- false
        holds

    /// Resolve a binding cell and record every frame scanned before the hit.
    /// Call-site inline caches revalidate against these snapshots instead of
    /// re-walking the environment chain.
    let resolveBindingCellWithPath env var : (BindingCell * VisitedFrame[]) voption =
        let mutable visited : Collections.Generic.HashSet<obj> = null
        let mutable pending : LispVal list = []
        let mutable current = env
        let mutable result = ValueNone
        let mutable running = true
        let path = Collections.Generic.List<VisitedFrame>()
        let inline advance () =
            match pending with
            | next :: rest ->
                current <- next
                pending <- rest
            | [] -> running <- false

        while running do
            match current with
            | Environment record when isNull visited || visited.Add(record :> obj) ->
                match tryFindBinding var record.bindings with
                | ValueSome cell ->
                    result <- ValueSome(cell, path.ToArray())
                    running <- false
                | ValueNone ->
                    path.Add { frame = record; bindingCount = record.bindings.Count }
                    match record.parents with
                    | [(Environment _ as parent)] -> current <- parent
                    | [] | [_] -> advance ()
                    | parents ->
                        if isNull visited then
                            visited <-
                                Collections.Generic.HashSet<obj>(
                                    Collections.Generic.ReferenceEqualityComparer.Instance)
                            visited.Add(record :> obj) |> ignore
                        let mutable environmentParents = []
                        for parent in List.rev parents do
                            match parent with
                            | Environment _ -> environmentParents <- parent :: environmentParents
                            | _ -> ()
                        match environmentParents with
                        | first :: rest ->
                            current <- first
                            pending <- rest @ pending
                        | [] -> advance ()
            | _ -> advance ()

        result

    let getVar' env var =
        match tryResolveBindingCell env var with
        | ValueSome cell -> Some cell.state.value
        | ValueNone -> None

    let setVar' env var value =
        match tryResolveBindingCell env var with
        | ValueSome cell ->
            updateBindingCell cell value
            Some value
        | ValueNone -> None

    /// Only bare primitive operatives carry a guarded identity. An Applicative
    /// wrapping a primitive (e.g. after `(define if (wrap if))`) must not match,
    /// because the compiler fast path invokes operative semantics while the
    /// binding evaluates all operands first.
    let private primitiveIdentity = function
        | PrimitiveOperative primitive -> primitive.identity
        | _ -> None

    let tryCreateBindingGuard env name expectedIdentity =
        match resolveBindingCell env name with
        | Some cell ->
            let state = cell.state
            if primitiveIdentity state.value = Some expectedIdentity then
                Some { name = name; expectedIdentity = expectedIdentity }
            else None
        | _ -> None

    /// The live guard test: does `name` denote a primitive with this identity in the
    /// environment we are running in? Both compiled paths use this.
    let bindingHasPrimitiveIdentity env name expectedIdentity =
        match tryResolveBindingCell env name with
        | ValueSome cell -> primitiveIdentity cell.state.value = Some expectedIdentity
        | ValueNone -> false

    let getVar env var =
        match tryResolveBindingCell env var with
        | ValueSome cell -> succeed cell.state.value
        | ValueNone -> throwError (UnboundVar("Getting an unbound variable",var))

    let setVar env var value = 
        match setVar' env var value with
        |Some(x) -> succeed x
        |None      -> throwError (UnboundVar("Getting an unbound variable",var))

    let defineVar env var value =
        match env with
        | Environment record ->
            match record.bindings.TryGetValue var with
            | true, cell ->
                updateBindingCell cell value
                succeed value
            | _ ->
                record.bindings.[var] <- newBindingCell value
                succeed value
        | found -> throwError(TypeMismatch("environment", found))

    /// Import bindings into the environment
    let bindVars env bindings =
        match env with
        | Environment record ->
            let merged = Env(record.bindings)
            // Reverse iteration keeps the association-list rule: an earlier
            // entry in `bindings` shadows a later duplicate of the same name.
            for name, value in List.rev bindings do
                merged.[name] <- newBindingCell value
            Environment { record with bindings = merged }
        | _ -> invalidArg (nameof env) "Expected an environment"
