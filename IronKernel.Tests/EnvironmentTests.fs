module IronKernel.Tests.EnvironmentTests

open System
open Xunit
open IronKernel.Ast
open IronKernel.Errors
open IronKernel.SymbolTable
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``define and lookup`` () =
    [
        "(define answer 42)", Inert
        "answer", Obj 42
        "(define answer 7)", Inert
        "answer", Obj 7
    ] |> evalSession

[<Fact>]
let ``symbol table rejects non-environments without match failures`` () =
    let invalid = Bool false
    Assert.True(resolveBindingCell invalid "value" |> Option.isNone)
    match defineVar invalid "value" (Obj (1 :> obj)) with
    | Choice1Of2 (TypeMismatch ("environment", Bool false)) -> ()
    | result -> failwithf "unexpected definition result: %A" result
    let error = Assert.Throws<ArgumentException>(fun () -> bindVars invalid [] |> ignore)
    Assert.Equal("env", error.ParamName)

[<Fact>]
let ``make-environment and remote-eval`` () =
    evalSessionKernel [
        "(define e (bindings->environment (x 10) (y 20)))", Inert
        "(remote-eval x e)", Obj 10
        "(remote-eval y e)", Obj 20
        "(environment? e)", Bool true
        "(environment? 1)", Bool false
    ]

[<Fact>]
let ``import! brings bindings into current env`` () =
    evalSessionKernel [
        "(define lib (bindings->environment (a 1) (b 2) (c 3)))", Inert
        "(import! lib a c)", Inert
        "a", Obj 1
        "c", Obj 3
    ]

[<Fact>]
let ``get-current-environment is reified`` () =
    evalSessionKernel [
        "(environment? (get-current-environment))", Bool true
    ]

[<Fact>]
let ``eval with explicit environment`` () =
    evalSessionKernel [
        "(define e (make-environment (get-current-environment)))", Inert
        "(eval '(define x 99) e)", Inert
        "(eval 'x e)", Obj 99
    ]

[<Fact>]
let ``binding guards track identity and version`` () =
    let env = freshEnv ()
    let guard =
        tryCreateBindingGuard env "if" PrimitiveIf
        |> Option.defaultWith (fun () -> failwith "missing primitive if guard")

    Assert.True(bindingGuardMatches env guard)
    ignore (defineVar env "unrelated" (Obj (1 :> obj)))
    Assert.True(bindingGuardMatches env guard)

    ignore (evalIn env "(define if (vau operands caller operands))")
    Assert.False(bindingGuardMatches env guard)

[<Fact>]
let ``binding guards reject applicative-wrapped primitives`` () =
    let env = freshEnv ()
    ignore (evalIn env "(define if (wrap if))")

    Assert.True(tryCreateBindingGuard env "if" PrimitiveIf |> Option.isNone)

    // Rebuild a guard against a fresh env, then wrap in place without relying on
    // version alone: identity check must fail for Applicative-wrapped if.
    let env2 = freshEnv ()
    let guard =
        tryCreateBindingGuard env2 "if" PrimitiveIf
        |> Option.defaultWith (fun () -> failwith "missing primitive if guard")
    match getVar' env2 "if" with
    | Some bare ->
        // Mutate the cell value while preserving id/version so only identity is tested.
        match resolveBindingCell env2 "if" with
        | Some cell ->
            cell.state <- { cell.state with value = Applicative bare }
            Assert.False(bindingGuardMatches env2 guard)
        | None -> failwith "missing if binding"
    | None -> failwith "missing if binding"

[<Fact>]
let ``set updates only the first binding in depth-first order`` () =
    let first = newEnv []
    let second = newEnv []
    ignore (defineVar first "x" (Obj (1 :> obj)))
    ignore (defineVar second "x" (Obj (2 :> obj)))
    let child = newEnv [first; second]

    ignore (setVar child "x" (Obj (9 :> obj)))

    match getVar first "x", getVar second "x" with
    | Choice2Of2 (Obj (:? int as firstValue)), Choice2Of2 (Obj (:? int as secondValue)) ->
        Assert.Equal(9, firstValue)
        Assert.Equal(2, secondValue)
    | values -> failwithf "unexpected parent values: %A" values

[<Fact>]
let ``lookup handles deeply nested parent environments`` () =
    let depth = 100_000
    let root = newEnv []
    ignore (defineVar root "deep-binding" (Obj(42 :> obj)))
    let mutable environment = root
    for _ in 1..depth do
        environment <- newEnv [environment]

    match getVar environment "deep-binding" with
    | Choice2Of2 (Obj (:? int as value)) -> Assert.Equal(42, value)
    | result -> failwithf "unexpected deep lookup result: %A" result
