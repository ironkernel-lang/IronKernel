namespace IronKernel

/// Clojure-inspired CLR call sugar shared by the interpreter and analyzer.
module ClrSugar =

    open Ast

    /// Rewrite Type/Method, Type., .method, and .-field into `.` / `new` / `.get`.
    /// Bound atoms always win at the call site; this only applies when unbound.
    let tryRewrite (name: string) (args: LispVal list) : LispVal option =
        if name = "." || name = ".get" || name = ".set" || name = "new" then
            None
        elif name.StartsWith(".-") && name.Length > 2 then
            match args with
            | instance :: rest ->
                Some (List (Atom ".get" :: instance :: Atom (name.Substring(2)) :: rest))
            | [] -> None
        elif name.StartsWith(".") && name.Length > 1 then
            match args with
            | instance :: rest ->
                Some (List (Atom "." :: instance :: Atom (name.Substring(1)) :: rest))
            | [] -> None
        elif name.EndsWith(".") && name.Length > 1 then
            Some (List (Atom "new" :: Atom (name.Substring(0, name.Length - 1)) :: args))
        elif name.Contains("/") then
            match name.Split([| '/' |], 2) with
            | [| typ; method |] when typ.Length > 0 && method.Length > 0 ->
                Some (List (Atom "." :: Atom typ :: Atom method :: args))
            | _ -> None
        else
            None
