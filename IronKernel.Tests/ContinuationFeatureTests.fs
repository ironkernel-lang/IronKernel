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

[<Fact>]
let ``an exit guard intercepts an abnormal pass out of its extent`` () =
    // R-1RK 7.2.4 / 7.3.3. The interceptor's result becomes the value passed onward,
    // and a normal return is not an abnormal pass, so it is not intercepted.
    [
        "(=? (call/cc (lambda (out) (guard-dynamic-extent (list) (lambda () (apply-continuation out 1) 99) (list (list root-continuation (lambda (v d) (* v 10))))))) 10)",
            Bool true
        "(=? (guard-dynamic-extent (list) (lambda () 7) (list (list root-continuation (lambda (v d) (* v 10))))) 7)",
            Bool true
        // "Exit-guard lists are considered first, proceeding from smallest to largest
        // dynamic extent": the inner guard adds one before the outer multiplies.
        "(=? (call/cc (lambda (out) (guard-dynamic-extent (list) (lambda () (guard-dynamic-extent (list) (lambda () (apply-continuation out 1)) (list (list root-continuation (lambda (v d) (+ v 1)))))) (list (list root-continuation (lambda (v d) (* v 100))))))) 200)",
            Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``an entry guard intercepts an abnormal pass into its extent`` () =
    // The continuation is captured inside the guarded extent and escaped with, so the
    // later pass enters from outside and the entry guard is selected. A pass that
    // never leaves the extent enters nothing and is not intercepted.
    [
        """(=? (let ((flag (vector 0)))
               (let ((k (call/cc (lambda (return)
                           (guard-dynamic-extent
                             (list (list root-continuation (lambda (v d) (+ v 1000))))
                             (lambda () (call/cc (lambda (c) (return c))))
                             (list))))))
                 (if (zero? (vector-ref flag 0))
                     (begin (vector-set! flag 0 1) (apply-continuation k 5))
                     k))) 1005)""", Bool true
        "(=? (guard-dynamic-extent (list (list root-continuation (lambda (v d) (+ v 1000)))) (lambda () (call/cc (lambda (c) (apply-continuation c 5)))) (list)) 5)",
            Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``a selector whose extent excludes the other end is not selected`` () =
    // "for each exit-guard list considered, the first interceptor (if any) is selected
    // whose selector's dynamic extent contains the destination". A selector captured
    // inside the guarded extent does not contain a destination outside it, so nothing
    // is selected and the value passes through untouched.
    [
        "(=? (call/cc (lambda (out) (guard-dynamic-extent (list) (lambda () (apply-continuation out 1) 99) (list (list (call/cc (lambda (k) k)) (lambda (v d) (* v 10))))))) 1)",
            Bool true
        // At most one interceptor is selected from each list: the first that matches.
        "(=? (call/cc (lambda (out) (guard-dynamic-extent (list) (lambda () (apply-continuation out 1) 99) (list (list root-continuation (lambda (v d) (+ v 1))) (list root-continuation (lambda (v d) (* v 100))))))) 2)",
            Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``guard-continuation builds a continuation that guards abnormal passes`` () =
    // 7.2.4 directly: the inner continuation behaves as the guarded one on a normal
    // receipt, and guards an abnormal pass out of its extent.
    [
        "(call/cc (lambda (k) (continuation? (guard-continuation (list) k (list)))))", Bool true
        "(=? (call/cc (lambda (k) (apply-continuation (guard-continuation (list) k (list)) 5))) 5)",
            Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``dynamic-wind can be built from the guards as the report derives it`` () =
    // The implementation in R-1RK 7.2.5's rationale, transcribed. This is the check
    // that the pieces compose: `after` has to run when the extent is left abnormally,
    // which is the whole point of exit guards.
    [
        "(define top (get-current-environment))", Inert
        "(define trace (list))", Inert
        "(define note (lambda (x) (set! top trace (cons x trace))))", Inert
        """(define dynamic-wind
              (lambda (before thunk after)
                (guard-dynamic-extent
                  (list (list root-continuation (lambda (value ignored) (before) value)))
                  (lambda () (before) (let ((result (thunk))) (after) result))
                  (list (list root-continuation (lambda (value ignored) (after) value))))))""", Inert
        // A normal return runs before and after exactly once each.
        "(=? (dynamic-wind (lambda () (note 1)) (lambda () 42) (lambda () (note 2))) 42)", Bool true
        "(=? (length trace) 2)", Bool true
        // Escaping runs `after` on the way out.
        "(set! top trace (list))", Inert
        "(=? (call/cc (lambda (k) (dynamic-wind (lambda () (note 1)) (lambda () (apply-continuation k 7)) (lambda () (note 2))))) 7)",
            Bool true
        "(=? (length trace) 2)", Bool true
        "(=? (car trace) 2)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``root-continuation and error-continuation are continuations`` () =
    [
        "(continuation? root-continuation)", Bool true
        "(continuation? error-continuation)", Bool true
        // R-1RK 7.2.6: root is the ancestor of all continuations, so a guard clause
        // selecting on it is always selected -- which is what the guard tests rely on.
        "(=? (call/cc (lambda (out) (guard-dynamic-extent (list) (lambda () (apply-continuation out 3) 99) (list (list root-continuation (lambda (v d) v)))))) 3)",
            Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``guard clause lists are checked`` () =
    withKernel (fun env ->
        let cases =
            [ "(call/cc (lambda (k) (guard-continuation 5 k (list))))", "entry-guard"
              "(call/cc (lambda (k) (guard-continuation (list) k 5)))", "exit-guard"
              "(call/cc (lambda (k) (guard-continuation (list (list 1 (lambda (v d) v))) k (list))))", "selector"
              "(call/cc (lambda (k) (guard-continuation (list (list root-continuation 5)) k (list))))", "interceptor"
              // "an applicative whose underlying combiner is operative", so a doubly
              // wrapped interceptor is rejected.
              "(call/cc (lambda (k) (guard-continuation (list (list root-continuation (wrap (lambda (v d) v)))) k (list))))", "operative"
              "(guard-continuation (list) 5 (list))", "continuation" ]
        for expression, fragment in cases do
            match evalIn env expression with
            | Status message -> Assert.Contains(fragment, message)
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value))

[<Fact>]
let ``exit abnormally transfers inert to root-continuation`` () =
    // R-1RK 7.3.4. Calling (exit) outright would end the test session, so the pass is
    // caught by an exit guard selecting on root -- which also shows where it was
    // headed -- and diverted before it arrives.
    [
        "(applicative? exit)", Bool true
        "(call/cc (lambda (out) (guard-dynamic-extent (list) (lambda () (exit) 99) (list (list root-continuation (lambda (v d) (apply-continuation out (inert? v))))))))",
            Bool true
    ] |> evalSessionKernel
