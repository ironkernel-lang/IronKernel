module IronKernel.Tests.ArithmeticTests

open Xunit
open IronKernel.Ast
open IronKernel.Arithmetic
open IronKernel.Errors
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``basic arithmetic`` () =
    [
        "(+ 2 3)", Obj 5
        "(- 10 4)", Obj 6
        "(* 6 7)", Obj 42
        "(/ 15 3)", Obj 5
    ] |> evalSession

[<Fact>]
let ``nested arithmetic`` () =
    [
        "(+ 1 (* 2 (+ 3 4)))", Obj 15
        "(- (* 5 5) (+ 2 3))", Obj 20
    ] |> evalSession

[<Fact>]
let ``numeric predicates and comparisons`` () =
    [
        "(zero? 0)", Bool true
        "(zero? 1)", Bool false
        "(< 1 2)", Bool true
        "(< 2 1)", Bool false
        "(<= 2 2)", Bool true
        "(> 5 3)", Bool true
    ] |> evalSession

[<Fact>]
let ``mixed-width comparisons widen instead of truncating`` () =
    // Regression: (<= 2.5 2L) truncated 2.5 to 2L and answered #t.
    [
        "(<= 2.5 2L)", Bool false
        "(< 2.5 2L)", Bool false
        "(< 1.5 2L)", Bool true
        "(<= 2L 2.5)", Bool true
        "(> 2.5 2L)", Bool true
        "(< 2L 2.5)", Bool true
    ] |> evalSession

[<Fact>]
let ``mixed int and float`` () =
    let env = freshEnv ()
    match evalIn env "(+ 1 2.5)" with
    | Obj (:? float as n) -> Assert.True(abs (n - 3.5) < 1e-9)
    | v -> failwith (showVal v)

[<Fact>]
let ``arithmetic preserves structured type errors`` () =
    // The + contract now rejects non-numeric, non-datetime operands before the
    // primitive runs, so the surfaced error is a contract violation.
    for mode in [Interpreted; Compiled] do
        let env = freshEnv ()
        match evalRaw mode env "(+ \"wrong\" 1)" with
        | Choice1Of2 (ContractViolation message) ->
            Assert.Contains("operand 1 expected number or datetime", message)
        | result -> failwithf "%A returned the wrong arithmetic error: %A" mode result

    // The raw primitive still reports a structured CLR type mismatch.
    match opAdd (Obj ("wrong" :> obj)) (Obj (1 :> obj)) with
    | Choice1Of2 (ClrTypeMismatch("number", "String")) -> ()
    | result -> failwithf "direct opAdd returned the wrong arithmetic error: %A" result

[<Fact>]
let ``comparisons preserve structured type errors`` () =
    for mode in [Interpreted; Compiled] do
        let env = freshEnv ()
        for operator in ["<"; "<="; ">"] do
            match evalRaw mode env $"({operator} #t 1)" with
            | Choice1Of2 (ContractViolation message) ->
                Assert.Contains("operand 1 expected number", message)
            | result -> failwithf "%A %s returned the wrong comparison error: %A" mode operator result

    let invalid = Bool true
    let valid = Obj (1 :> obj)
    for compare in [opLessThan; opLessThanOrEqual; opGreaterThan; opGreaterThanOrEqual] do
        match compare invalid valid with
        | Choice1Of2 (TypeMismatch ("object", Bool true)) -> ()
        | result -> failwithf "direct comparison returned the wrong error: %A" result

[<Fact>]
let ``eqv on numbers`` () =
    [
        "(eqv? 7 7)", Bool true
        "(eqv? 7 8)", Bool false
        "(eq? 1 1)", Bool true
    ] |> evalSession

[<Fact>]
let ``dividing by zero signals an error instead of faulting`` () =
    // R-1RK 12.8.2 requires an error when the divisor is zero. .NET disagrees in both
    // directions: integer division throws, and floating-point division yields an
    // infinity. Before this was handled, either case escaped as a CLR exception and
    // faulted the process -- so a test host running this at all is part of the check.
    let env = freshEnv ()
    for expression in [ "(/ 1 0)"; "(/ 1.0 0.0)"; "(/ 0 0)"; "(/ 5 (- 3 3))" ] do
        match evalIn env expression with
        | Status message -> Assert.Contains("division by zero", message)
        | value -> failwithf "%s should signal an error, got %s" expression (showVal value)

[<Fact>]
let ``arithmetic overflow signals an error instead of faulting`` () =
    // Int32.MinValue / -1 has no representable result and raises inside the CLR.
    let env = freshEnv ()
    match evalIn env "(/ -2147483648 -1)" with
    | Status message -> Assert.Contains("overflow", message.ToLowerInvariant())
    | value -> failwithf "overflow should signal an error, got %s" (showVal value)

[<Fact>]
let ``division still works for non-zero divisors`` () =
    [
        "(/ 8 2)", Obj 4
        "(/ 9.0 2.0)", Obj 4.5
        "(/ -6 3)", Obj -2
    ] |> evalSession

[<Fact>]
let ``a signalled division error leaves the environment usable`` () =
    // The failure must be an ordinary Kernel error, not something that unwinds past
    // the evaluator: further evaluation in the same environment has to keep working.
    let env = freshEnv ()
    match evalIn env "(/ 1 0)" with
    | Status _ -> ()
    | value -> failwithf "expected an error, got %s" (showVal value)
    assertEval env "(+ 1 2)" (Obj 3)

[<Fact>]
let ``div and mod satisfy the division identity for every sign`` () =
    // R-1RK 12.5.8 defines mod as real1 - (real2 * n). The report's own phrasing
    // ("greatest integer n with real2 * n <= real1") is unbounded for a negative
    // divisor; its rationale defers to the R6RS, whose defining property is
    // 0 <= mod < |real2|. Both are checked here.
    withKernel (fun env ->
        for a in [ -7; -1; 0; 1; 7; 12 ] do
            for b in [ -3; -1; 1; 3; 5 ] do
                let identity = sprintf "(=? %d (+ (* %d (div %d %d)) (mod %d %d)))" a b a b a b
                assertEval env identity (Bool true)
                let ranged = sprintf "(and? (<=? 0 (mod %d %d)) (<? (mod %d %d) (abs %d)))" a b a b b
                assertEval env ranged (Bool true))

[<Fact>]
let ``div0 and mod0 centre the remainder`` () =
    // R-1RK 12.5.9: the remainder lies in [-|real2|/2, |real2|/2).
    withKernel (fun env ->
        for a in [ -8; -7; 0; 6; 7; 8 ] do
            for b in [ -3; 3; 4 ] do
                let identity = sprintf "(=? %d (+ (* %d (div0 %d %d)) (mod0 %d %d)))" a b a b a b
                assertEval env identity (Bool true)
                let ranged =
                    sprintf "(and? (<=? (- 0 (abs %d)) (* 2 (mod0 %d %d))) (<? (* 2 (mod0 %d %d)) (abs %d)))"
                        b a b a b b
                assertEval env ranged (Bool true))

[<Fact>]
let ``integer division by zero signals an error`` () =
    withKernel (fun env ->
        for expression in [ "(div 7 0)"; "(mod 7 0)"; "(div0 7 0)"; "(div-and-mod 7 0)" ] do
            match evalIn env expression with
            | Status message -> Assert.Contains("division by zero", message)
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value))

[<Fact>]
let ``max and min reject an empty argument list`` () =
    // The report returns exact infinities here, which IronKernel cannot represent.
    withKernel (fun env ->
        for expression in [ "(max)"; "(min)" ] do
            match evalIn env expression with
            | Status message -> Assert.Contains("at least one argument", message)
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value))

[<Fact>]
let ``type predicates accept non-numbers but finite? does not`` () =
    withKernel (fun env ->
        // number? and integer? are type predicates (R-1RK 12.5.1).
        assertEval env "(number? 'a)" (Bool false)
        assertEval env "(integer? \"x\")" (Bool false)
        // finite? requires numbers, so a non-number is an error.
        match evalIn env "(finite? 'a)" with
        | Status _ -> ()
        | value -> failwithf "(finite? 'a) should signal an error, got %s" (showVal value))

[<Fact>]
let ``numeric comparison is not structural equality`` () =
    withKernel (fun env ->
        assertEval env "(=? 1 1.0)" (Bool true)
        // eqv? compares representations, so it disagrees -- that is expected.
        assertEval env "(eqv? 1 1.0)" (Bool false))
