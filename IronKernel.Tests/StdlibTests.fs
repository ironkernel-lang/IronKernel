module IronKernel.Tests.StdlibTests

open Xunit
open IronKernel.Ast
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``let let-star letrec`` () =
    evalSessionKernel [
        "(let ((x 2) (y 3)) (* x y))", Obj 6
        "(let ((x 2) (y 3)) (let ((x 7) (z (+ x y))) (* z x)))", Obj 35
        "(let* ((x 3) (y x)) (+ x y))", Obj 6
        "(let ((x 2) (y 3)) (let* ((x 7) (z (+ x y))) (* z x)))", Obj 70
        "(letrec ((sum (lambda (x) (if (zero? x) 0 (+ x (sum (- x 1))))))) (sum 5))", Obj 15
    ]

[<Fact>]
let ``cond and logic`` () =
    evalSessionKernel [
        "(cond ((<= 1 0) 'no) ((eqv? 1 1) 'hello))", Atom "hello"
        // R-1RK 6.1.4/6.1.5: $and? and $or? are the short-circuiting operatives.
        "($and? #f (/ 1 0))", Bool false
        "($or? #t (/ 1 0))", Bool true
        // R-1RK 6.1.2/6.1.3: and? and or? are applicatives over evaluated arguments.
        "(and? #t #t #t)", Bool true
        "(or? #f #f #t)", Bool true
        "(and?)", Bool true
        "(or?)", Bool false
        "(not? #f)", Bool true
        "(not? #t)", Bool false
    ]

[<Fact>]
let ``defn and compose`` () =
    evalSessionKernel [
        "(defn (square x) (* x x))", Inert
        "(square 8)", Obj 64
        "((compose square square) 2)", Obj 16
    ]

[<Fact>]
let ``apply and list-star`` () =
    evalSessionKernel [
        "(apply + (list 1 2))", Obj 3
        "(list* 1 2 (list 3))", ofList [Obj 1; Obj 2; Obj 3]
    ]

[<Fact>]
let ``promises lazy force memoize`` () =
    withKernelAndPromises (fun env ->
        ignore (evalIn env "(define a (lazy (+ 2 5)))")
        assertEqv (evalIn env "(promise? a)") (Bool true)
        assertEqv (evalIn env "(force a)") (Obj 7)
        ignore (evalIn env "(define b (memoize (* 2 21)))")
        assertEqv (evalIn env "(promise? b)") (Bool true)
        assertEqv (evalIn env "(force b)") (Obj 42))

[<Fact>]
let ``caar cadr helpers`` () =
    evalSessionKernel [
        "(caar '((a b) (c d)))", Atom "a"
        "(cadr '(a b c))", Atom "b"
    ]

[<Fact>]
let ``and? and or? evaluate every argument`` () =
    // The applicatives must not short-circuit: an argument after a decided result is
    // still evaluated. Proven by a side effect rather than by an error, because
    // (/ 1 0) currently faults the process rather than raising a Kernel error.
    evalSessionKernel [
        "(define trace (vector 0 0))", Inert
        "(and? #f (sequence (vector-set! trace 0 1) #t))", Bool false
        "(vector-ref trace 0)", Obj 1
        "(or? #t (sequence (vector-set! trace 1 1) #f))", Bool true
        "(vector-ref trace 1)", Obj 1
    ]

[<Fact>]
let ``$and? and $or? stop as soon as the result is decided`` () =
    evalSessionKernel [
        "(define trace (vector 0 0))", Inert
        "($and? #f (sequence (vector-set! trace 0 1) #t))", Bool false
        "(vector-ref trace 0)", Obj 0
        "($or? #t (sequence (vector-set! trace 1 1) #f))", Bool true
        "(vector-ref trace 1)", Obj 0
    ]

[<Fact>]
let ``sequence follows 5.1.1`` () =
    // Primitive since ADR 0007. The behaviour the report specifies is unchanged by
    // that: left to right in the dynamic environment, last value returned, inert for
    // no operands. (The tail-context half of 5.1.1 is not observable from a result,
    // and is checked structurally in CompilerTests.)
    evalSessionKernel [
        "(sequence 1 2 3)", Obj 3
        "(sequence 7)", Obj 7
        "(sequence)", Inert
        "($sequence 1 2 3)", Obj 3
        // Left to right, and every element really is evaluated.
        "(define trace (vector 0 0 0))", Inert
        "(sequence (vector-set! trace 0 1) (vector-set! trace 1 2) (vector-set! trace 2 3))", Inert
        "(vector-ref trace 0)", Obj 1
        "(vector-ref trace 2)", Obj 3
        // It is an operative: operands arrive unevaluated, so a later element can
        // depend on a definition an earlier one made.
        "(operative? sequence)", Bool true
        "((lambda () (sequence (define local 5) local)))", Obj 5
    ]

[<Fact>]
let ``a redefined sequence is used instead of the primitive`` () =
    // The compiled form is guarded on the binding still holding the primitive, so a
    // program that rebinds the name must get its own combiner rather than the
    // lowered `CSeq`. Without the guard the lowering would silently win.
    evalSessionKernel [
        "((lambda () (define sequence (lambda xs 99)) (sequence 1 2 3)))", Obj 99
        // The shadowing is local: the outer binding still means the primitive.
        "(sequence 1 2 3)", Obj 3
    ]

[<Fact>]
let ``the report's derivation of $sequence still behaves like the primitive`` () =
    // ADR 0007 replaced this derivation with a primitive, so nothing exercises it any
    // more and it could rot unnoticed. R-1RK 5.1.1's derivation, transcribed, and
    // checked against the primitive on the cases that distinguish sequencing:
    // ordering, the returned value, and the empty case.
    evalSessionKernel [
        """(define derived-sequence
              ((wrap
                 (vau (seq2) _
                      (seq2
                        (define aux
                          (vau (head & tail) env
                               (if (null? tail)
                                 (eval head env)
                                 (seq2
                                   (eval head env)
                                   (eval (cons aux tail) env)))))
                        (vau body env
                             (if (null? body)
                               #inert
                               (eval (cons aux body) env))))))
               (vau (first second) env
                    ((wrap (vau _ _ (eval second env)))
                     (eval first env)))))""", Inert
        "(derived-sequence 1 2 3)", Obj 3
        "(derived-sequence 7)", Obj 7
        "(inert? (derived-sequence))", Bool true
        "(define trace (vector 0 0))", Inert
        "(derived-sequence (vector-set! trace 0 1) (vector-set! trace 1 2))", Inert
        "(vector-ref trace 0)", Obj 1
        "(vector-ref trace 1)", Obj 2
        // Unevaluated operands, as for the primitive.
        "((lambda () (derived-sequence (define local 5) local)))", Obj 5
    ]
