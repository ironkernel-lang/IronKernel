module IronKernel.Tests.ContinuationFeatureTests

open Xunit
open IronKernel.Ast
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``continuation? is the type predicate for continuations`` () =
    // R-1RK 7.2.1, variadic like the other type predicates.
    [
        "(call/cc (lambda (k) (continuation? k)))", Bool true
        "(eqv? (continuation? 5) #f)", Bool true
        "(eqv? (continuation? (lambda () 0)) #f)", Bool true
        "(continuation?)", Bool true
        "(call/cc (lambda (k) (continuation? k k)))", Bool true
        "(call/cc (lambda (k) (eqv? (continuation? k 5) #f)))", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``apply-continuation passes the object itself`` () =
    // R-1RK 7.3.1. The object is passed whole -- an atom stays an atom, rather than
    // becoming the one element of an argument list.
    [
        "(=? (call/cc (lambda (k) (apply-continuation k 5) 99)) 5)", Bool true
        "(=? (car (call/cc (lambda (k) (apply-continuation k (list 1 2)) 99))) 1)", Bool true
        // The pass is abnormal: whatever follows it in the combiner never runs.
        "(=? (call/cc (lambda (k) (apply-continuation k 1) 99)) 1)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``continuation->applicative abnormally passes its operand tree`` () =
    // R-1RK 7.2.5. The operand tree of a combination is a list, so the continuation
    // receives the whole list rather than a single operand.
    [
        "(call/cc (lambda (k) (applicative? (continuation->applicative k))))", Bool true
        "(=? (car (call/cc (lambda (k) ((continuation->applicative k) 1 2) 99))) 1)", Bool true
        "(=? (car (cdr (call/cc (lambda (k) ((continuation->applicative k) 1 2) 99)))) 2)", Bool true
        // With no operands the tree is the empty list.
        "(null? (call/cc (lambda (k) ((continuation->applicative k)) 99)))", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``extend-continuation prepends a computation to a continuation`` () =
    // R-1RK 7.2.3: a child of the continuation that, on receiving v, calls the
    // underlying combiner of the applicative with operand tree v, its result normally
    // returning to the original continuation.
    [
        "(=? (call/cc (lambda (k) (apply-continuation (extend-continuation k (lambda (x) (* x 10))) (list 4)))) 40)",
            Bool true
        // The result really does return to the original continuation, so the context
        // around the call/cc still applies.
        "(=? (+ 1 (call/cc (lambda (k) (apply-continuation (extend-continuation k (lambda (x) (* x 10))) (list 4))))) 41)",
            Bool true
        "(call/cc (lambda (k) (continuation? (extend-continuation k (lambda (x) x)))))", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``extend-continuation takes the dynamic environment for the call`` () =
    // A compound applicative resolves its body in its own closure, so observing the
    // dynamic environment takes a combiner that actually uses it.
    [
        "(define e (make-environment))", Inert
        "(eval (list define (quote factor) 3) e)", Inert
        "(define scaled (wrap (vau (x) d (eval (list * x (quote factor)) d))))", Inert
        "(=? (call/cc (lambda (k) (apply-continuation (extend-continuation k scaled e) (list 5)))) 15)",
            Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the two-argument extend-continuation supplies an empty environment`` () =
    // 7.2.3: (extend-continuation c a) is sugar for (extend-continuation c a
    // (make-environment)), so a combiner that reads its dynamic environment finds
    // nothing there.
    withKernel (fun env ->
        for expression in
            [ "(define scaled (wrap (vau (x) d (eval (list * x (quote factor)) d))))"
              "(define e (make-environment))"
              "(eval (list define (quote factor) 3) e)" ] do
            match evalIn env expression with
            | Status message -> failwithf "setup failed: %s" message
            | _ -> ()
        // With the environment given, the binding resolves.
        match evalIn env "(call/cc (lambda (k) (apply-continuation (extend-continuation k scaled e) (list 5))))" with
        | Obj (:? int as scaled) -> Assert.Equal(15, scaled)
        | value -> failwithf "extend with an environment gave %s" (showVal value)
        // Without it, the empty environment has no such binding.
        match evalIn env "(call/cc (lambda (k) (apply-continuation (extend-continuation k scaled) (list 5))))" with
        | Status message -> Assert.Contains("factor", message)
        | value -> failwithf "the two-argument form should see an empty environment, got %s" (showVal value))

[<Fact>]
let ``the continuation applicatives check their argument types`` () =
    withKernel (fun env ->
        let cases =
            [ "(continuation->applicative 5)", "continuation"
              "(apply-continuation 5 1)", "continuation"
              "(call/cc (lambda (k) (extend-continuation k 5)))", "applicative"
              "(extend-continuation 5 (lambda (x) x))", "continuation"
              "(call/cc (lambda (k) (extend-continuation k (lambda (x) x) 5)))", "environment" ]
        for expression, fragment in cases do
            match evalIn env expression with
            | Status message -> Assert.Contains(fragment, message)
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value)
        for expression in [ "(continuation->applicative)"; "(apply-continuation)" ] do
            match evalIn env expression with
            | Status _ -> ()
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value))
