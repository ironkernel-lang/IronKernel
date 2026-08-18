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
