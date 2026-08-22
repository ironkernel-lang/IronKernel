module IronKernel.Tests.VectorTests

open Xunit
open IronKernel.Ast
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``vector primitives`` () =
    [
        "(vector? (vector 1 2 3))", Bool true
        "(vector? 1)", Bool false
        "(vector-ref (vector 10 20 30) 1)", Obj 20
        "(define v (make-vector 3 9))", Inert
        "(vector-ref v 0)", Obj 9
        "(vector-set! v 1 8)", Inert
        "(vector-ref v 1)", Obj 8
    ] |> evalSession

[<Fact>]
let ``vector literal from parser evaluates as self`` () =
    let env = freshEnv ()
    match evalIn env "[1 2]" with
    | Vector arr ->
        Assert.Equal(2, arr.Length)
        assertEqv arr.[0] (Obj 1)
    | v -> failwith (showVal v)

[<Fact>]
let ``vector-length reports element count`` () =
    [
        "(vector-length (vector))", Obj 0
        "(vector-length (vector 1 2 3))", Obj 3
    ] |> evalSession

[<Fact>]
let ``equal? compares vectors element by element`` () =
    // Structural equality descends into vectors as it does into pairs; eq?
    // stays identity. The nested case is what a JSON array inside an object
    // exercises.
    [
        "(equal? (vector 1 2) (vector 1 2))", Bool true
        "(equal? (vector 1 2) (vector 1 3))", Bool false
        "(equal? (vector 1 2) (vector 1 2 3))", Bool false
        "(equal? (vector) (vector))", Bool true
        "(equal? (cons (vector 1) \"x\") (cons (vector 1) \"x\"))", Bool true
        "(equal? (vector (cons 1 2)) (vector (cons 1 2)))", Bool true
        "(eq? (vector 1) (vector 1))", Bool false
        "(define v (vector 1))", Inert
        "(eq? v v)", Bool true
    ] |> evalSession

[<Fact>]
let ``equal? terminates on a self-containing vector`` () =
    [
        "(define a (vector 1 2))", Inert
        "(define b (vector 1 2))", Inert
        "(vector-set! a 0 a)", Inert
        "(vector-set! b 0 b)", Inert
        "(equal? a b)", Bool true
        "(vector-set! b 1 3)", Inert
        "(equal? a b)", Bool false
    ] |> evalSession
