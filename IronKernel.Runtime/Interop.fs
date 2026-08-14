namespace IronKernel

    open System
    open System.Collections.Concurrent
    open Ast
    open Errors
    open Choice
    open Eval
    open Capabilities

    module Interop =

        let private resolvedTypes = ConcurrentDictionary<string, Type>()

        let toObjects : LispVal -> ThrowsError<obj>  = function
            |Bool b -> returnM (b :> obj)
            |Obj o  -> returnM o
            |badForm -> throwError (TypeMismatch("Obj",badForm))

        /// Resolve a fully-qualified CLR type name across loaded assemblies.
        let resolveTypeExact (name: string) =
            match resolvedTypes.TryGetValue(name) with
            | true, resolved -> resolved
            | _ ->
                let mutable resolved = Type.GetType(name)
                let assemblies = AppDomain.CurrentDomain.GetAssemblies()
                let mutable index = 0
                while isNull resolved && index < assemblies.Length do
                    resolved <- assemblies.[index].GetType(name, false)
                    index <- index + 1
                if not (isNull resolved) then
                    resolvedTypes.TryAdd(name, resolved) |> ignore
                resolved

        let private clrState = function
            | Environment record -> Some record
            | _ -> None

        /// Resolve a type name using aliases and env-local opened namespaces.
        let resolveType (env: LispVal) (name: string) =
            let aliases, namespaces =
                match clrState env with
                | Some record -> !record.clrAliases, !record.clrNamespaces
                | None -> Map.empty, []
            let canonical =
                match Map.tryFind name aliases with
                | Some full -> full
                | None -> name
            let exact = resolveTypeExact canonical
            if exact <> null then exact
            elif canonical.Contains(".") then null
            else
                let matches =
                    namespaces
                    |> List.choose (fun ns ->
                        let candidate = ns + "." + canonical
                        let found = resolveTypeExact candidate
                        if found = null then None else Some (candidate, found))
                match matches with
                | [] -> null
                | [(_, t)] -> t
                | many ->
                    let options =
                        many
                        |> List.map fst
                        |> String.concat ", "
                    raise
                        (InvalidOperationException(
                            "Ambiguous CLR type '" + name + "': " + options))

        let tryResolveType env name =
            try
                let t = resolveType env name
                if t = null then None else Some t
            with :? InvalidOperationException ->
                reraise ()

        let private typeFromTarget env = function
            | Obj (:? Type as t) -> Some t
            | Atom name ->
                try tryResolveType env name
                with :? InvalidOperationException as ex ->
                    raise ex
            | _ -> None

        let new_object env cont = function
            | _ when not (has RawClrInterop env) ->
                fail (CapabilityDenied "raw CLR construction requires RawClrInterop")
            | target :: args ->
                try
                    match typeFromTarget env target with
                    | None ->
                        match target with
                        | Atom t -> fail (Default("Couldn't find type '" + t + "'"))
                        | _ -> fail (TypeMismatch("type name or type", target))
                    | Some typ ->
                        // Evaluate constructor arguments (operative operands arrive raw).
                        match sequence (List.map (eval env (newContinuation env)) args) [] with
                        | Choice1Of2 e -> fail e
                        | Choice2Of2 evaluated ->
                            match sequence (List.map toObjects evaluated) [] with
                            | Choice1Of2 e -> fail e
                            | Choice2Of2 mapargs ->
                                try
                                    let obj = Activator.CreateInstance(typ, List.toArray mapargs)
                                    bounceContinue env cont (Obj obj)
                                with ex ->
                                    fail (Default("Couldn't create type '" + typ.FullName + "', " + ex.Message))
                with :? InvalidOperationException as ex ->
                    fail (Default ex.Message)
            | bad -> fail (NumArgs(1, bad))

        open System.Reflection

        let get env cont (t:Type) (o:obj) p =
            let f = t.GetField(p)
            if f = null then
                let f = t.GetProperty(p)
                if f = null then 
                    fail (Default("field or property '" + p + "' does not exist"))
                else
                    bounceContinue env cont (Obj(f.GetValue(o,null)))
            else
                bounceContinue env cont (Obj(f.GetValue(o)))

        let set env cont (t:Type) (o:obj) p (v:obj)=
            let f = t.GetField(p)
            if f = null then
                let f = t.GetProperty(p)
                if f = null then 
                    fail (Default("field or property '" + p + "' does not exist"))
                else
                    f.SetValue(o, v, null)
                    bounceContinue env cont Inert
            else
                f.SetValue(o, v)
                bounceContinue env cont Inert

        let rec dot_get env cont prms = 
            match prms with
            | _ when not (has RawClrInterop env) ->
                fail (CapabilityDenied "raw CLR property access requires RawClrInterop")
            | (clazz::Atom(p)::tail) ->
                try
                    match clazz with
                    | Obj (:? Type as typ) -> get env cont typ null p
                    | Obj o -> let typ = o.GetType() in get env cont typ o p
                    | Atom c ->
                        match tryResolveType env c with
                        | Some typ -> get env cont typ null p
                        | None ->
                            // Not a type name — evaluate as an instance expression.
                            let cps e c result _ =
                                dot_get e c (result::Atom(p)::tail)
                            bounceEval env (makeCPS env cont cps) clazz
                    | exp -> let cps e c result _ =
                                dot_get e c (result::Atom(p)::tail)
                             bounceEval env (makeCPS env cont cps) exp
                with :? InvalidOperationException as ex ->
                    fail (Default ex.Message)
            | _ -> fail (NumArgs(2,prms))

        let rec dot_set env cont prms = 
            match prms with
            | _ when not (has RawClrInterop env) ->
                fail (CapabilityDenied "raw CLR property mutation requires RawClrInterop")
            | (clazz::Atom(p)::value::_) ->
                try
                    let apply target evaluatedValue =
                        match target, evaluatedValue with
                        | Obj (:? Type as typ), Obj x -> set env cont typ null p x
                        | Obj o, Obj x -> set env cont (o.GetType()) o p x
                        | _, Obj _ -> fail (TypeMismatch("object", target))
                        | _, bad -> fail (TypeMismatch("object", bad))
                    let ensureValue target =
                        match value with
                        | Obj _ as ready -> apply target ready
                        | _ ->
                            let cps e c evaluated _ =
                                match target with
                                | Obj _ ->
                                    // Re-enter with evaluated value.
                                    dot_set e c (target :: Atom p :: evaluated :: [])
                                | _ -> fail (TypeMismatch("object", target))
                            bounceEval env (makeCPS env cont cps) value
                    match clazz with
                    | Obj _ -> ensureValue clazz
                    | Atom c ->
                        match tryResolveType env c with
                        | Some typ -> ensureValue (Obj (typ :> obj))
                        | None ->
                            let cps e c result _ =
                                dot_set e c (result :: Atom p :: value :: [])
                            bounceEval env (makeCPS env cont cps) clazz
                    | exp ->
                        let cps e c result _ =
                            dot_set e c (result :: Atom p :: value :: [])
                        bounceEval env (makeCPS env cont cps) exp
                with :? InvalidOperationException as ex ->
                    fail (Default ex.Message)
            | _ -> fail (NumArgs(3,prms))

        let invoke (t:Type) (o:obj) (m: string) args= 
            try
                either {
                    let! mapargs = sequence (List.map toObjects args) []
                    let r = t.InvokeMember(m,BindingFlags.InvokeMethod,Type.DefaultBinder,o, List.toArray mapargs)
                    if r = null then return Inert
                    else return (Obj(r))
                }
            with ex -> throwError(Default("member invokation failed: " + ex.Message))

        let rec dot env cont = function
            | _ when not (has RawClrInterop env) ->
                fail (CapabilityDenied "raw CLR invocation requires RawClrInterop")
            | (clazz::Atom(m)::args) ->
                try
                    match clazz with
                    | Atom _
                    | Obj _ ->
                        match sequence (List.map (eval env (newContinuation env)) args) [] with
                        | Choice1Of2 e -> fail e
                        | Choice2Of2 args' ->
                            let result =
                                match clazz with
                                | Obj (:? Type as typ) -> invoke typ null m args'
                                | Obj o  -> let typ = o.GetType() in invoke typ o m args'
                                | Atom c ->
                                    match tryResolveType env c with
                                    | Some typ -> invoke typ null m args'
                                    | None ->
                                        match eval env (newContinuation env) clazz with
                                        | Choice2Of2 (Obj (:? Type as typ)) -> invoke typ null m args'
                                        | Choice2Of2 (Obj o) ->
                                            let typ = o.GetType()
                                            invoke typ o m args'
                                        | Choice2Of2 bad -> throwError (TypeMismatch("Obj", bad))
                                        | Choice1Of2 e -> throwError e
                                | bad -> throwError (TypeMismatch("object", bad))
                            match result with
                            | Choice1Of2 e -> fail e
                            | Choice2Of2 r -> bounceContinue env cont r
                    | exp ->
                        let cps e c result _ =
                            dot e c (result :: Atom m :: args)
                        bounceEval env (makeCPS env cont cps) exp
                with :? InvalidOperationException as ex ->
                    fail (Default ex.Message)
            | prms -> fail (NumArgs(2, prms))

        let clr_open env cont = function
            | _ when not (has RawClrInterop env) ->
                fail (CapabilityDenied "CLR namespace imports require RawClrInterop")
            | namespaces ->
                match clrState env with
                | None -> fail (TypeMismatch("environment", env))
                | Some record ->
                    let rec add = function
                        | [] -> bounceContinue env cont Inert
                        | Atom ns :: rest when ns.Length > 0 ->
                            if not (List.contains ns !record.clrNamespaces) then
                                record.clrNamespaces := !record.clrNamespaces @ [ns]
                            add rest
                        | bad :: _ -> fail (TypeMismatch("namespace atom", bad))
                    add namespaces

        let clr_alias env cont = function
            | _ when not (has RawClrInterop env) ->
                fail (CapabilityDenied "CLR namespace imports require RawClrInterop")
            | [Atom shortName; Atom fullName] when shortName.Length > 0 && fullName.Length > 0 ->
                match clrState env with
                | None -> fail (TypeMismatch("environment", env))
                | Some record ->
                    record.clrAliases := Map.add shortName fullName !record.clrAliases
                    bounceContinue env cont Inert
            | bad -> fail (NumArgs(2, bad))

        let clr_type env cont = function
            | _ when not (has RawClrInterop env) ->
                fail (CapabilityDenied "clr-type requires RawClrInterop")
            | [Atom name] ->
                try
                    match tryResolveType env name with
                    | Some t -> bounceContinue env cont (Obj (t :> obj))
                    | None -> fail (Default("Couldn't find type '" + name + "'"))
                with :? InvalidOperationException as ex ->
                    fail (Default ex.Message)
            | [Obj (:? Type as t)] ->
                bounceContinue env cont (Obj (t :> obj))
            | bad -> fail (NumArgs(1, bad))

        let clr_opens env cont = function
            | [] ->
                match clrState env with
                | None -> bounceContinue env cont (List [])
                | Some record ->
                    let names = !record.clrNamespaces |> List.map Atom
                    bounceContinue env cont (List names)
            | bad -> fail (NumArgs(0, bad))

        let print env cont (prms : LispVal list) =
          match prms with
          | _ when not (has HostIO env) ->
                fail (CapabilityDenied "host output requires HostIO")
          | [Obj(sf)] ->
                System.Console.Write(sf.ToString())
                bounceContinue env cont Inert
          | _ -> fail (NumArgs(1,prms))

        let printf' env cont (prms : LispVal list) =
          match prms with
          | _ when not (has HostIO env) ->
                fail (CapabilityDenied "host output requires HostIO")
          | Obj(sf)::tail when typeof<string> = sf.GetType() -> 
                match sequence (List.map toObjects tail) [] with
                | Choice1Of2 e -> fail e
                | Choice2Of2 mapargs ->
                    let str = String.Format(sf :?> string,List.toArray mapargs) 
                    System.Console.Write(str)
                    bounceContinue env cont Inert
          | _ -> fail (NumArgs(2,prms))

        let show env cont (prms : LispVal list) =
          match prms with
          | _ when not (has HostIO env) ->
              fail (CapabilityDenied "host output requires HostIO")
          | h :: _ ->
              System.Console.Write(showVal h)
              bounceContinue env cont Inert
          | [] -> fail (NumArgs(1, []))
