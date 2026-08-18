module IronKernel.Tests.ErrorPassTests

open Xunit
open IronKernel.Ast
open IronKernel.Tests.TestHelpers

// R-1RK 7.2.7: "the signaling action consists of an abnormal pass to some
// continuation in the dynamic extent of error-continuation". These check that the
// pass actually happens. Nothing else in the suite can: a signalling action that
// quietly went back to unwinding directly would leave every other test passing,
// which is exactly the property that makes the change safe and also the property
// that makes it invisible.

/// The guard shape the report uses for $binds? (6.7.1): an exit guard selecting on
/// error-continuation, whose interceptor diverts rather than returning.
let private trying = """
    (define try
      (lambda (thunk)
        (call/cc (lambda (escape)
          (guard-dynamic-extent
            ()
            thunk
            (list (list error-continuation (lambda (obj divert) (escape "caught")))))))))"""

[<Fact>]
let ``an exit guard on error-continuation intercepts a signalled error`` () =
    [
        trying, Inert
        """(equal? (try (lambda () (car 5))) "caught")""", Bool true
        // A body that does not signal is untouched, and returns its own value.
        "(=? (try (lambda () (+ 1 2))) 3)", Bool true
        // The nearest guard wins, as for any abnormal pass.
        """(equal? (try (lambda () (try (lambda () (car 5))))) "caught")""", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the guard only intercepts errors signalled within its own extent`` () =
    withKernel (fun env ->
        match evalIn env trying with
        | Status message -> failwithf "setup failed: %s" message
        | _ -> ()
        // Signalled outside any guarded extent: still reported, not swallowed.
        match evalIn env "(car 5)" with
        | Status message -> Assert.Contains("pair", message)
        | value -> failwithf "(car 5) should still signal, got %s" (showVal value)
        // And the guard is gone once its extent is over.
        match evalIn env """(try (lambda () 0))""" with
        | Obj (:? int as n) -> Assert.Equal(0, n)
        | value -> failwithf "the guard returned %s" (showVal value)
        match evalIn env "(car 5)" with
        | Status message -> Assert.Contains("pair", message)
        | value -> failwithf "(car 5) after the guard should signal, got %s" (showVal value))

[<Fact>]
let ``an interceptor that returns normally does not cancel the error`` () =
    // 7.2.5 gives the interceptor two ways out, and only one of them handles the
    // error: returning passes the value along the chain to the destination, which
    // is in the extent of error-continuation and reports. Handling means diverting.
    withKernel (fun env ->
        let expression =
            """(guard-dynamic-extent
                 ()
                 (lambda () (car 5) "the body continued")
                 (list (list error-continuation (lambda (obj divert) obj))))"""
        match evalIn env expression with
        | Status message -> Assert.Contains("pair", message)
        | value -> failwithf "returning normally should not cancel the error, got %s" (showVal value))

[<Fact>]
let ``an error signalled inside an interceptor terminates`` () =
    // The interceptor runs while a pass to the error extent is in progress. Starting
    // a second pass from there would select the same guard again and never finish, so
    // signalling inside the error extent unwinds directly instead. The check is that
    // this returns at all -- and reports the interceptor's error, not the body's.
    withKernel (fun env ->
        let expression =
            """(guard-dynamic-extent
                 ()
                 (lambda () (car 5))
                 (list (list error-continuation (lambda (obj divert) (car 7)))))"""
        match evalIn env expression with
        | Status message -> Assert.Contains("7", message)
        | value -> failwithf "expected the interceptor's own error, got %s" (showVal value))

[<Fact>]
let ``the error's diagnostic survives the pass`` () =
    // The pass carries the original error rather than rebuilding one from the value
    // that arrives, so an intercepted-and-released error reports what it would have
    // reported with no guard at all. (Source spans are attached on the unwind by the
    // dispatch layer, not carried by the error, so they are not what this checks;
    // they were compared against master separately and are unchanged.)
    withKernel (fun env ->
        let bare =
            match evalIn env "(car 5)" with
            | Status message -> message
            | value -> failwithf "(car 5) should signal, got %s" (showVal value)
        let guarded =
            let expression =
                """(guard-dynamic-extent
                     ()
                     (lambda () (car 5))
                     (list (list error-continuation (lambda (obj divert) obj))))"""
            match evalIn env expression with
            | Status message -> message
            | value -> failwithf "the guarded form should signal, got %s" (showVal value)
        Assert.Equal(bare, guarded))

[<Fact>]
let ``errors that reach the guard are not limited to one kind`` () =
    // Phase 2 routed `signal`, but 39 sites still converted a ThrowsError to a Step
    // with `fail`, which consults no continuation -- so whether an error could be
    // intercepted depended on which primitive raised it. A guard caught (car 5) and
    // missed an unbound variable. These are the kinds that were escaping.
    [
        trying, Inert
        // Symbol lookup: Eval's bare-Atom case, the one that surfaced the gap.
        """(equal? (try (lambda () nope)) "caught")""", Bool true
        """(equal? (try (lambda () (eval (quote nope) (get-current-environment)))) "caught")""", Bool true
        // Arithmetic, through the numeric fold.
        """(equal? (try (lambda () (/ 1 0))) "caught")""", Bool true
        """(equal? (try (lambda () (+ 1 "x"))) "caught")""", Bool true
        // Vectors, through the index check.
        """(equal? (try (lambda () (vector-ref (vector 1 2) 9))) "caught")""", Bool true
        // Applying a non-combiner, and the wrong operand count.
        """(equal? (try (lambda () (car))) "caught")""", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``dynamic-wind cleans up after a failure`` () =
    // R-1RK 7.2.5's derivation of dynamic-wind, unchanged from the version in
    // ContinuationFeatureTests. What is new is the third case: before 7.2.7 routed
    // through the guards, `after` ran on a normal return and on an abnormal pass but
    // not when the body signalled -- which is most of what one wants dynamic-wind for.
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
        trying, Inert
        """(equal?
              (try (lambda ()
                     (dynamic-wind (lambda () (note 1)) (lambda () (car 5)) (lambda () (note 2)))))
              "caught")""", Bool true
        // `before` and `after` each ran once, and `after` ran last -- on the way out
        // of an extent left by signalling, not by returning or escaping.
        "(=? (length trace) 2)", Bool true
        "(=? (car trace) 2)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the report's $binds? derivation works`` () =
    // R-1RK 6.7.1 derives $binds? in Kernel: guard the lookup with an exit guard on
    // error-continuation and let the interceptor divert with #f. The report writes
    // the divert as `(apply divert #f)`, passing #f as an *atomic* operand tree.
    // IronKernel represents an operand tree as a list, so an atomic tree has no
    // spelling (the recorded 7.2.5 divergence) and `(divert #f)` delivers `(#f)`.
    // The body returns `(list #t)` to match, and the caller takes the car of either.
    // That is a transcription difference, not a semantic one: what decides the
    // predicate is still whether looking the symbol up signals.
    [
        """(define binds?
              (vau (exp & ss) dynamic
                (car
                  (guard-dynamic-extent
                    ()
                    (lambda ()
                      (let ((env (eval exp dynamic)))
                        (map (lambda (sym) (eval sym env)) ss))
                      (list #t))
                    (list (list error-continuation (lambda (_ divert) (divert #f))))))))""", Inert
        "(define here (get-current-environment))", Inert
        "(define bound 1)", Inert
        "(binds? here bound)", Bool true
        "(binds? here bound here)", Bool true
        "(not? (binds? here nope))", Bool true
        // All the symbols have to be bound, not just one of them.
        "(not? (binds? here bound nope))", Bool true
        // And it agrees with the primitive, which stays: the point of the derivation
        // is that it introduces no capability the language did not already have.
        "(eq? (binds? here bound) ($binds? here bound))", Bool true
        "(eq? (binds? here nope) ($binds? here nope))", Bool true
    ] |> evalSessionKernel
