module IronKernel.Tests.InteropTests

open Xunit
open IronKernel.Ast
open IronKernel.Errors
open IronKernel.Interop
open IronKernel.Runtime
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``exact type resolution caches hits but preserves misses`` () =
    let resolved = resolveTypeExact "System.String"
    Assert.Same(typeof<string>, resolved)
    Assert.Same(resolved, resolveTypeExact "System.String")

    let missing = "IronKernel.Tests.MissingType." + System.Guid.NewGuid().ToString("N")
    Assert.Null(resolveTypeExact missing)
    Assert.Null(resolveTypeExact missing)

[<Fact>]
let ``new and static method call`` () =
    let env = freshEnv ()
    match evalIn env "(. System.Guid NewGuid)" with
    | Obj (:? System.Guid) -> ()
    | v -> failwith (showVal v)

[<Fact>]
let ``string format via CLR`` () =
    let env = freshEnv ()
    match evalIn env "(. System.String Format \"{0}-{1}\" 1 2)" with
    | Obj (:? string as s) -> Assert.Equal("1-2", s)
    | v -> failwith (showVal v)

[<Fact>]
let ``static property get DateTime`` () =
    let env = freshEnv ()
    match evalIn env "(.get System.DateTime UtcNow)" with
    | Obj (:? System.DateTime) -> ()
    | v -> failwith (showVal v)

[<Fact>]
let ``path combine and file roundtrip`` () =
    let env = freshEnv ()
    let dir = System.IO.Path.GetTempPath()
    let file = System.IO.Path.Combine(dir, "ironkernel-interop-test.txt")
    try
        let escaped = file.Replace("\\", "\\\\")
        ignore (evalIn env (sprintf "(define path \"%s\")" escaped))
        ignore (evalIn env "(. System.IO.File WriteAllText path \"kernel\")")
        match evalIn env "(. System.IO.File ReadAllText path)" with
        | Obj (:? string as s) -> Assert.Equal("kernel", s)
        | v -> failwith (showVal v)
    finally
        if System.IO.File.Exists file then System.IO.File.Delete file

[<Fact>]
let ``console write returns inert`` () =
    [
        "(. System.Console Write \"\")", Inert
    ] |> evalSession

[<Fact>]
let ``set property on instance variable`` () =
    let env = freshEnv ()
    ignore (evalIn env "(clr-open System.Text)")
    ignore (evalIn env "(define sb (StringBuilder.))")
    ignore (evalIn env "(.set sb Capacity 64)")
    match evalIn env "(.-Capacity sb)" with
    | Obj (:? int as n) -> Assert.Equal(64, n)
    | v -> failwith (showVal v)

[<Fact>]
let ``new evaluates constructor arguments`` () =
    let env = freshEnv ()
    ignore (evalIn env "(clr-open System System.IO System.Text)")
    ignore (evalIn env "(define bytes (.GetBytes (.-UTF8 Encoding) \"hi\"))")
    ignore (evalIn env "(define stream (new MemoryStream bytes))")
    ignore (evalIn env "(define reader (new StreamReader stream))")
    match evalIn env "(.ReadToEnd reader)" with
    | Obj (:? string as s) -> Assert.Equal("hi", s)
    | v -> failwith (showVal v)

[<Fact>]
let ``clr-open resolves short type names`` () =
    let env = freshEnv ()
    ignore (evalIn env "(clr-open System)")
    match evalIn env "(. Guid NewGuid)" with
    | Obj (:? System.Guid) -> ()
    | v -> failwith (showVal v)

[<Fact>]
let ``clr-open supports multiple namespaces`` () =
    let env = freshEnv ()
    ignore (evalIn env "(clr-open System System.IO System.Text)")
    match evalIn env "(clr-opens)" with
    | List [Atom "System"; Atom "System.IO"; Atom "System.Text"] -> ()
    | v -> failwith (showVal v)
    match evalIn env "(. Path GetExtension \"a.ikr\")" with
    | Obj (:? string as s) -> Assert.Equal(".ikr", s)
    | v -> failwith (showVal v)

[<Fact>]
let ``single-parent environments copy CLR namespace state`` () =
    let parent = freshEnv ()
    ignore (evalIn parent "(clr-open System)")
    let child = newEnv [parent]
    ignore (evalIn child "(clr-open System.Text)")

    assertEval parent "(clr-opens)" (ofList [Atom "System"])
    assertEval child "(clr-opens)" (ofList [Atom "System"; Atom "System.Text"])

[<Fact>]
let ``clr-alias binds a short type name`` () =
    let env = freshEnv ()
    ignore (evalIn env "(clr-alias SB System.Text.StringBuilder)")
    match evalIn env "(new SB)" with
    | Obj (:? System.Text.StringBuilder) -> ()
    | v -> failwith (showVal v)

[<Fact>]
let ``clr-type returns a first-class Type value`` () =
    let env = freshEnv ()
    ignore (evalIn env "(clr-open System)")
    match evalIn env "(clr-type Guid)" with
    | Obj (:? System.Type as t) -> Assert.Equal(typeof<System.Guid>, t)
    | v -> failwith (showVal v)
    match evalIn env "(. (clr-type System.String) Format \"{0}\" 7)" with
    | Obj (:? string as s) -> Assert.Equal("7", s)
    | v -> failwith (showVal v)

[<Fact>]
let ``clr-open is inherited by operative closures`` () =
    withKernel (fun ken ->
        ignore (evalIn ken "(clr-open System)")
        match evalIn ken "((vau () _ (. Guid NewGuid)))" with
        | Obj (:? System.Guid) -> ()
        | v -> failwith (showVal v))

[<Fact>]
let ``ambiguous short type names are rejected`` () =
    let env = freshEnv ()
    ignore (evalIn env "(clr-open System.Threading System.Timers)")
    match evalRaw Interpreted env "(clr-type Timer)" with
    | Choice1Of2 (Default msg) when msg.Contains("Ambiguous") -> ()
    | other -> failwithf "expected ambiguity error, got %A" other

[<Fact>]
let ``clojure style static method call`` () =
    let env = freshEnv ()
    ignore (evalIn env "(clr-open System)")
    match evalIn env "(String/Format \"{0}-{1}\" 1 2)" with
    | Obj (:? string as s) -> Assert.Equal("1-2", s)
    | v -> failwith (showVal v)

[<Fact>]
let ``clojure style constructor`` () =
    let env = freshEnv ()
    ignore (evalIn env "(clr-open System.Text)")
    match evalIn env "(StringBuilder.)" with
    | Obj (:? System.Text.StringBuilder) -> ()
    | v -> failwith (showVal v)

[<Fact>]
let ``clojure style instance method and field`` () =
    let env = freshEnv ()
    ignore (evalIn env "(clr-open System System.Text)")
    ignore (evalIn env "(define sb (StringBuilder.))")
    ignore (evalIn env "(.Append sb \"ab\")")
    match evalIn env "(.ToString sb)" with
    | Obj (:? string as s) -> Assert.Equal("ab", s)
    | v -> failwith (showVal v)
    match evalIn env "(.-Length sb)" with
    | Obj (:? int as n) -> Assert.Equal(2, n)
    | v -> failwith (showVal v)

[<Fact>]
let ``clojure style does not override bound atoms`` () =
    let env = freshEnv ()
    ignore (evalIn env "(define String/Format (wrap (vau (a b c) _ a)))")
    assertEval env "(String/Format \"x\" 1 2)" (Obj ("x" :> obj))

[<Fact>]
let ``clr-open denied without RawClrInterop`` () =
    let env = makePrimitiveBindingsForProfile Safe
    match evalRaw Interpreted env "(clr-open System)" with
    | Choice1Of2 (UnboundVar _)
    | Choice1Of2 (CapabilityDenied _) -> ()
    | other -> failwithf "expected denial, got %A" other
