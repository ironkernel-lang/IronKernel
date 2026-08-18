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
