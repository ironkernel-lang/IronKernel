module IronKernel.Tests.ListTests

open Xunit
open IronKernel.Ast
open IronKernel.Runtime
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``cons car cdr`` () =
    [
        "(cons 1 ())", ofList [Obj 1]
        "(cons 1 (cons 2 ()))", ofList [Obj 1; Obj 2]
        "(car (cons 1 (cons 2 ())))", Obj 1
        "(cdr (cons 1 (cons 2 ())))", ofList [Obj 2]
        "(null? ())", Bool true
        "(null? (cons 1 ()))", Bool false
        "(pair? (cons 1 2))", Bool true
        "(pair? ())", Bool false
    ] |> evalSession

[<Fact>]
let ``dotted pairs`` () =
    [
        "(car (cons 1 2))", Obj 1
        "(cdr (cons 1 2))", Obj 2
    ] |> evalSession

[<Fact>]
let ``structural equality compares lists and dotted tails`` () =
    let assertResult expected left right =
        match eqv' [left; right] with
        | Choice2Of2 (Bool actual) -> Assert.Equal(expected, actual)
        | result -> failwithf "unexpected equality result: %A" result

    assertResult true (ofList [ofList [Atom "a"]]) (ofList [ofList [Atom "a"]])
    assertResult false (ofList [Atom "a"]) (ofList [Atom "a"; Atom "b"])
    assertResult false ((ofDotted [Atom "a"] (Atom "b"))) ((ofDotted [Atom "a"] (Atom "c")))
    assertResult false ((ofDotted [Atom "a"] (Atom "b"))) (ofList [Atom "a"; Atom "b"])

    match eqv' [Atom "a"] with
    | Choice1Of2 (NumArgs (2, [_])) -> ()
    | result -> failwithf "unexpected equality arity result: %A" result

[<Fact>]
let ``structural equality handles deeply nested lists`` () =
    let mutable left = Atom "leaf"
    let mutable right = Atom "leaf"
    for _ in 1..100000 do
        left <- ofList [left]
        right <- ofList [right]

    match eqv' [left; right] with
    | Choice2Of2 (Bool true) -> ()
    | result -> failwithf "unexpected deep equality result: %A" result

[<Fact>]
let ``showVal handles deeply nested lists`` () =
    let depth = 100_000
    let mutable value = Atom "leaf"
    for _ in 1..depth do
        value <- ofList [value]

    let rendered = showVal value
    Assert.Equal(depth * 2 + 4, rendered.Length)
    Assert.StartsWith(System.String('(', depth), rendered)
    Assert.EndsWith(System.String(')', depth), rendered)
    Assert.Equal("leaf", rendered.Substring(depth, 4))

[<Fact>]
let ``list library helpers`` () =
    [
        "(list 1 2 3)", ofList [Obj 1; Obj 2; Obj 3]
        "(length (list 1 2 3 4))", Obj 4
        "(map (lambda (x) (+ x 1)) (list 1 2 3))", ofList [Obj 2; Obj 3; Obj 4]
    ] |> evalSessionKernel

[<Fact>]
let ``quote preserves structure`` () =
    [
        "'(a b c)", ofList [Atom "a"; Atom "b"; Atom "c"]
        "(car '(x y))", Atom "x"
    ] |> evalSessionKernel

[<Fact>]
let ``type predicates cover the report's types`` () =
    [
        "(boolean? #t)", Bool true
        "(boolean? 1)", Bool false
        "(symbol? 'a)", Bool true
        "(symbol? 1)", Bool false
        "(inert? #inert)", Bool true
        "(applicative? car)", Bool true
        "(operative? car)", Bool false
        "(operative? vau)", Bool true
        "(combiner? car)", Bool true
        "(combiner? vau)", Bool true
        "(combiner? 1)", Bool false
        // Variadic and true for no arguments, like the report's other predicates.
        "(boolean?)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``get-list-metrics reports the shape of an improper list`` () =
    // R-1RK 5.7.1 returns (pairs nils acyclic-prefix cycle-length). The cyclic cases
    // live in PairMutationTests, beside the mutation that can build one.
    [
        "(equal? (get-list-metrics (list 1 2 3)) (list 3 1 3 0))", Bool true
        "(equal? (get-list-metrics ()) (list 0 1 0 0))", Bool true
        // A non-pair starts an improper list consisting of just itself.
        "(equal? (get-list-metrics 5) (list 0 0 0 0))", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``list accessors and constructors follow the report`` () =
    [
        "(equal? (list-tail (list 1 2 3 4) 2) (list 3 4))", Bool true
        "(=? (list-ref (list 1 2 3) 1) 2)", Bool true
        "(equal? (append (list 1 2) (list 3)) (list 1 2 3))", Bool true
        "(equal? (append) ())", Bool true
        "(equal? (append (list 1)) (list 1))", Bool true
        "(equal? (list-neighbors (list 1 2 3)) (list (list 1 2) (list 2 3)))", Bool true
        "(equal? (list-neighbors ()) ())", Bool true
        "(equal? (list-neighbors (list 1)) ())", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``list searches and folds follow the report's argument order`` () =
    // filter and for-each take the applicative first (6.3.5, 6.9.1); reduce takes the
    // list first (6.3.10). The orders differ between them in the report itself.
    [
        "(equal? (filter (lambda (x) (positive? x)) (list -1 2 -3 4)) (list 2 4))", Bool true
        "(equal? (assoc 'b (list (list 'a 1) (list 'b 2))) (list 'b 2))", Bool true
        "(equal? (assoc 'z (list (list 'a 1))) ())", Bool true
        "(member? 2 (list 1 2 3))", Bool true
        "(member? 9 (list 1 2))", Bool false
        "(=? (reduce (list 1 2 3 4) + 0) 10)", Bool true
        "(=? (reduce () + 0) 0)", Bool true
        "(=? (reduce (list 5) + 0) 5)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``for-each takes the applicative first`` () =
    // R-1RK 6.9.1 is (for-each applicative . lists). IronKernel used to take the list
    // first, which an earlier conformance check failed to catch because it passed a
    // one-element list and never depended on the order.
    [
        "(define trace (vector 0))", Inert
        "(for-each (lambda (x) (vector-set! trace 0 x)) (list 7))", Inert
        "(=? (vector-ref trace 0) 7)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``filter requires a boolean result`` () =
    withKernel (fun env ->
        match evalIn env "(filter (lambda (x) 1) (list 1 2))" with
        | Status message -> Assert.Contains("non-boolean", message)
        | value -> failwithf "expected an error, got %s" (showVal value))

[<Fact>]
let ``reduce handles a cyclic list through the six-argument form`` () =
    // R-1RK 6.3.10. The three-argument form requires an acyclic list; the six-argument
    // one takes precycle, incycle and postcycle, because an arbitrary binary operation
    // cannot be generalised to an infinite sequence in finite time and the caller has
    // to say how the cycle is handled.
    [
        "(define id (lambda (x) x))", Inert
        // encycle! returns inert, so the list has to be named first.
        "(define cyc (lambda (ls a c) (sequence (encycle! ls a c) ls)))", Inert
        // A pure cycle (a = 0, c = 3), and one behind an acyclic prefix (a = 2, c = 3).
        "(define pure (cyc (list 1 2 3) 0 3))", Inert
        "(define mixed (cyc (list 10 20 1 2 3) 2 3))", Inert
        "(=? (reduce pure + 0 id + id) 6)", Bool true
        "(=? (reduce mixed + 0 id + id) 36)", Bool true
        // precycle and postcycle are really applied, rather than the cycle just being
        // summed: doubling in postcycle moves 6 to 12, and scaling each element by ten
        // in precycle moves 6 to 60.
        "(=? (reduce mixed + 0 id + (lambda (x) (* x 2))) 42)", Bool true
        "(=? (reduce pure + 0 (lambda (x) (* x 10)) + id) 60)", Bool true
        // A one-element cycle, and the six-argument form on an acyclic list, where
        // c = 0 and the cycle applicatives go unused.
        "(=? (reduce (cyc (list 5) 0 1) + 0 id + id) 5)", Bool true
        "(=? (reduce (list 1 2 3) + 0 id + id) 6)", Bool true
        "(=? (reduce () + 7 id + id) 7)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``reduce makes exactly the calls the report specifies`` () =
    // 6.3.10 fixes the call counts: acyclic of length n calls binary n-1 times; cyclic
    // with prefix a and cycle c calls binary a times, precycle c, incycle c-1, and
    // postcycle once. Summing with + cannot check this -- + is associative and
    // commutative, so a wrong grouping still gives the right total. Counting can.
    [
        "(define top (get-current-environment))", Inert
        "(define cyc (lambda (ls a c) (sequence (encycle! ls a c) ls)))", Inert
        "(define counts (vector 0 0 0 0))", Inert
        "(define bump (lambda (i) (vector-set! counts i (+ (vector-ref counts i) 1))))", Inert
        """(define reset (lambda () (sequence (vector-set! counts 0 0) (vector-set! counts 1 0)
                                              (vector-set! counts 2 0) (vector-set! counts 3 0))))""", Inert
        "(define cbin (lambda (x y) (sequence (bump 0) (+ x y))))", Inert
        "(define cpre (lambda (x) (sequence (bump 1) x)))", Inert
        "(define cin (lambda (x y) (sequence (bump 2) (+ x y))))", Inert
        "(define cpost (lambda (x) (sequence (bump 3) x)))", Inert
        // Acyclic, n = 5.
        "(sequence (reset) (reduce (list 1 2 3 4 5) cbin 0) (=? (vector-ref counts 0) 4))", Bool true
        // Cyclic, a = 2, c = 3.
        """(sequence (reset) (reduce (cyc (list 10 20 1 2 3) 2 3) cbin 0 cpre cin cpost)
             (and? (=? (vector-ref counts 0) 2) (=? (vector-ref counts 1) 3)
                   (=? (vector-ref counts 2) 2) (=? (vector-ref counts 3) 1)))""", Bool true
        // Pure cycle, a = 0: binary is not called at all.
        """(sequence (reset) (reduce (cyc (list 1 2 3) 0 3) cbin 0 cpre cin cpost)
             (and? (=? (vector-ref counts 0) 0) (=? (vector-ref counts 1) 3)
                   (=? (vector-ref counts 2) 2)))""", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``reduce calls its applicatives in the caller's dynamic environment`` () =
    // 6.3.10: "Each call to binary, precycle, incycle, or postcycle uses the dynamic
    // environment of the call to reduce", by analogy with map (5.9.1). Without that,
    // binary would run in reduce's own environment and `local-marker` would be
    // unbound, so this distinguishes the two.
    [
        "(define peek (wrap (vau (x y) e (eval (quote local-marker) e))))", Inert
        "(=? ((lambda () (define local-marker 99) (reduce (list 1 2) peek 0))) 99)", Bool true
    ] |> evalSessionKernel
