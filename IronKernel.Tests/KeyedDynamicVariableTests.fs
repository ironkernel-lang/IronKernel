module IronKernel.Tests.KeyedDynamicVariableTests

open Xunit
open IronKernel.Ast
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``the accessor sees the object for the extent of the binder's call`` () =
    // R-1RK 10.1.1: the binder calls its second argument with no operands, and within
    // that call's dynamic extent the accessor returns the binder's first argument.
    [
        "(define p (make-keyed-dynamic-variable))", Inert
        "(define b (car p))", Inert
        "(define a (car (cdr p)))", Inert
        "(=? (b 42 (lambda () (a))) 42)", Bool true
        // The binder returns whatever the combiner returned, not the bound object.
        "(=? (b 42 (lambda () 99)) 99)", Bool true
        // Dynamic, not lexical: an intervening call that closes over nothing still
        // sees the binding.
        "(define peek (lambda () (a)))", Inert
        "(=? (b 7 (lambda () (peek))) 7)", Bool true
        // The nearest enclosing binding wins, and the outer one comes back.
        "(=? (b 1 (lambda () (b 2 (lambda () (a))))) 2)", Bool true
        "(=? (b 1 (lambda () (b 2 (lambda () 0)) (a))) 1)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``each call to make-keyed-dynamic-variable makes a distinct variable`` () =
    [
        "(define p (make-keyed-dynamic-variable))", Inert
        "(define q (make-keyed-dynamic-variable))", Inert
        "(define bp (car p))", Inert
        "(define ap (car (cdr p)))", Inert
        "(define bq (car q))", Inert
        "(define aq (car (cdr q)))", Inert
        "(=? (bp 1 (lambda () (bq 2 (lambda () (ap))))) 1)", Bool true
        "(=? (bp 1 (lambda () (bq 2 (lambda () (aq))))) 2)", Bool true
        // One variable's binding is invisible to the other's accessor.
        "(=? (bq 2 (lambda () 0)) 0)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the accessor signals an error outside any binding`` () =
    withKernel (fun env ->
        for expression in
            [ "(define p (make-keyed-dynamic-variable))"
              "(define b (car p))"
              "(define a (car (cdr p)))" ] do
            ignore (evalIn env expression)
        // Never bound at all.
        match evalIn env "(a)" with
        | Status message -> Assert.Contains("unbound", message)
        | value -> failwithf "(a) should signal an error, got %s" (showVal value)
        // Bound and returned from: the extent is over.
        match evalIn env "(b 3 (lambda () 0))" with
        | Obj (:? int as bound) -> Assert.Equal(0, bound)
        | value -> failwithf "the binder returned %s" (showVal value)
        match evalIn env "(a)" with
        | Status message -> Assert.Contains("unbound", message)
        | value -> failwithf "(a) after the extent should signal an error, got %s" (showVal value)
        // Escaping out of the binder ends the extent too.
        match evalIn env "(call/cc (lambda (escape) (b 3 (lambda () (escape 8)))))" with
        | Obj (:? int as escaped) -> Assert.Equal(8, escaped)
        | value -> failwithf "escaping the binder returned %s" (showVal value)
        match evalIn env "(a)" with
        | Status message -> Assert.Contains("unbound", message)
        | value -> failwithf "(a) after an escape should signal an error, got %s" (showVal value))

[<Fact>]
let ``a continuation captured inside the extent re-enters it when resumed`` () =
    // This is what a push/pop side stack gets wrong, and the reason the binding is a
    // continuation frame instead. `return` escapes with a continuation captured inside
    // the binder's call, so that call has already returned -- the extent is over -- by
    // the time the continuation is resumed. Resuming it runs (a) again, which must
    // still find 11 rather than signalling that the variable is unbound.
    [
        """(let ((p (make-keyed-dynamic-variable)) (flag (vector 0)))
             (let ((b (car p)) (a (car (cdr p))))
               (let ((k (call/cc (lambda (return)
                           (b 11 (lambda () (call/cc (lambda (c) (return c))) (a)))))))
                 (if (zero? (vector-ref flag 0))
                     (begin (vector-set! flag 0 1) (k 0))
                     k))))""", Obj 11
    ] |> evalSessionKernel

[<Fact>]
let ``a binding does not break proper tail calls`` () =
    // The binding frame sits in the continuation for the whole call, so a tail-
    // recursive loop inside it must still not grow the continuation. Two hundred
    // thousand iterations would exhaust memory if the frame defeated the tail-call
    // rule, and the accessor must still find the binding at the bottom.
    [
        "(define p (make-keyed-dynamic-variable))", Inert
        "(define b (car p))", Inert
        "(define a (car (cdr p)))", Inert
        "(define loop (lambda (n) (if (=? n 0) (a) (loop (- n 1)))))", Inert
        "(=? (b 42 (lambda () (loop 200000))) 42)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the binder rejects the wrong number of operands`` () =
    withKernel (fun env ->
        ignore (evalIn env "(define p (make-keyed-dynamic-variable))")
        for expression in [ "((car p) 1)"; "((car p) 1 (lambda () 0) 2)"; "((car (cdr p)) 1)" ] do
            match evalIn env expression with
            | Status _ -> ()
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value)
        match evalIn env "(make-keyed-dynamic-variable 1)" with
        | Status _ -> ()
        | value -> failwithf "make-keyed-dynamic-variable takes no operands, got %s" (showVal value))

[<Fact>]
let ``a binding is visible across a delimited continuation`` () =
    // The accessor walks the continuation the way the evaluator does, so it crosses a
    // prompt into the metacontinuation. Both the delimited body and the handler -- which
    // runs outside that body -- are within the binder's dynamic extent and must see it.
    [
        "(define p (make-keyed-dynamic-variable))", Inert
        "(define b (car p))", Inert
        "(define a (car (cdr p)))", Inert
        "(define tag (make-prompt-tag))", Inert
        "(=? (b 5 (lambda () (prompt tag (lambda (v k) (resume k (+ v 1))) (+ (a) (perform tag 0))))) 6)",
            Bool true
        "(=? (b 7 (lambda () (prompt tag (lambda (v k) (resume k (a))) (perform tag 0)))) 7)",
            Bool true
    ] |> evalSessionKernel
