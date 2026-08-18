module IronKernel.Tests.VauTests

open Xunit
open IronKernel.Ast
open IronKernel.Errors
open IronKernel.Eval
open IronKernel.SymbolTable
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``vau receives unevaluated operands`` () =
    [
        "(define quote-one (vau (x) _ x))", Inert
        "(quote-one (+ 1 2))", ofList [Atom "+"; Obj 1; Obj 2]
    ] |> evalSession

[<Fact>]
let ``vau rejects operands that do not match formals`` () =
    let cases =
        [ "((vau (x y) _ 42) 1)", ofList []
          "((vau (x y) _ 42) 1 2 3)", ofList [Obj 3]
          "((vau ((x y)) _ 42) (1))", ofList [] ]

    for expression, badForm in cases do
        for mode in [Interpreted; Compiled] do
            let env = freshEnv ()
            match evalRaw mode env expression with
            | Choice1Of2 (BadSpecialForm ("invalid arguments", actual)) ->
                assertEqv actual badForm
            | Choice1Of2 error ->
                failwithf "%A returned the wrong error: %s" mode (showError error)
            | Choice2Of2 value ->
                failwithf "%A accepted malformed operands: %s" mode (showVal value)

[<Fact>]
let ``vau dotted formals collect remaining operands`` () =
    assertParityValueSession
        [ "((vau (x & rest) _ rest) 1 2 3)" ]
        (ofList [Obj 2; Obj 3])

[<Fact>]
let ``vau combines nested destructuring with rest formals`` () =
    assertParityValueSession
        [ "((vau ((a (b c)) & rest) _ b) (1 (2 3)) 4)" ]
        (Obj 2)

[<Fact>]
let ``formal binding handles very long lists`` () =
    let env = freshEnv ()
    let formals = ofList(List.replicate 100000 (Atom "value"))
    let values = ofList([0..99999] |> List.map (fun value -> Obj(value :> obj)))

    match bind env (newContinuation env) formals values with
    | Choice1Of2 error -> failwithf "deep formal binding failed: %s" (showError error)
    | Choice2Of2 Inert -> ()
    | Choice2Of2 value -> failwithf "unexpected deep formal binding result: %s" (showVal value)

    match getVar env "value" with
    | Choice2Of2 (Obj (:? int as value)) -> Assert.Equal(99999, value)
    | result -> failwithf "unexpected final deep binding: %A" result

[<Fact>]
let ``vau can eval in caller environment`` () =
    [
        "(define force-it (vau (x) e (eval x e)))", Inert
        "(define n 21)", Inert
        "(force-it (+ n n))", Obj 42
    ] |> evalSession

[<Fact>]
let ``operative unless short-circuits`` () =
    evalSessionKernel [
        """(define unless
             (vau (test & body) env
               (if (eval test env) #inert (eval (cons sequence body) env))))""", Inert
        "(define ran #f)", Inert
        "(unless #t (define ran #t))", Inert
        "ran", Bool false
        "(unless #f (define ran #t))", Inert
        "ran", Bool true
    ]

[<Fact>]
let ``wrap and unwrap`` () =
    [
        "(define op (vau (x) _ x))", Inert
        "(define ap (wrap op))", Inert
        "(ap (+ 1 2))", Obj 3
        "((unwrap ap) (+ 1 2))", ofList [Atom "+"; Obj 1; Obj 2]
    ] |> evalSession

[<Fact>]
let ``wrap requires exactly one operand`` () =
    let env = freshEnv ()
    for expression, foundCount in [ "(wrap)", 0; "(wrap if if)", 2 ] do
        match evalRaw Interpreted env expression with
        | Choice1Of2 (NumArgs (1, found)) -> Assert.Equal(foundCount, List.length found)
        | result -> failwithf "%s returned the wrong arity result: %A" expression result

[<Fact>]
let ``encapsulation types enforce arity and generative identity`` () =
    let env = freshEnv ()
    let defineType prefix =
        ignore (evalIn env $"(define {prefix}-type (make-encapsulation-type))")
        ignore (evalIn env $"(define {prefix}-wrap (car {prefix}-type))")
        ignore (evalIn env $"(define {prefix}? (car (cdr {prefix}-type)))")
        ignore (evalIn env $"(define {prefix}-unwrap (car (cdr (cdr {prefix}-type))))")

    defineType "first"
    defineType "second"
    ignore (evalIn env "(define wrapped (first-wrap 42))")
    assertEval env "(first? wrapped)" (Bool true)
    assertEval env "(second? wrapped)" (Bool false)
    assertEval env "(first-unwrap wrapped)" (Obj (42 :> obj))

    for expression in
        [ "(make-encapsulation-type 1)"
          "(first-wrap)"
          "(first?)"
          "(first-unwrap)" ] do
        match evalRaw Interpreted env expression with
        | Choice1Of2 (NumArgs _) -> ()
        | result -> failwithf "%s returned the wrong arity result: %A" expression result

    match evalRaw Interpreted env "(second-unwrap wrapped)" with
    | Choice1Of2 (Default "encapsulation type mismatch") -> ()
    | result -> failwithf "foreign decapsulation returned the wrong result: %A" result

[<Fact>]
let ``lambda is sugar over vau`` () =
    evalSessionKernel [
        "((lambda (x y) (+ x y)) 3 4)", Obj 7
        "((λ (x) (* x x)) 6)", Obj 36
    ]
