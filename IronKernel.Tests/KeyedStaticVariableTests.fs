module IronKernel.Tests.KeyedStaticVariableTests

open Xunit
open IronKernel.Ast
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``the accessor sees the object throughout the environment the binder returns`` () =
    // R-1RK 11.1.1: the binder returns a fresh child of its second argument, and the
    // accessor called with no operands anywhere in that child or its descendants
    // returns the binder's first argument.
    [
        "(define p (make-keyed-static-variable))", Inert
        "(define b (car p))", Inert
        "(define a (car (cdr p)))", Inert
        "(define e (b 42 (get-current-environment)))", Inert
        "(environment? e)", Bool true
        "(=? (eval (list a) e) 42)", Bool true
        // Descendants of that environment see it too.
        "(=? (eval (list a) (make-environment e)) 42)", Bool true
        // The nearest such ancestor wins, and the outer one is still readable
        // through its own environment.
        "(define e1 (b 1 (get-current-environment)))", Inert
        "(define e2 (b 2 e1))", Inert
        "(=? (eval (list a) e2) 2)", Bool true
        "(=? (eval (list a) e1) 1)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the binding is static, not dynamic`` () =
    // The contrast with 10.1.1 is the whole point. A procedure whose body is written
    // inside the environment reads the object wherever it is called from; one written
    // outside it does not, even when called from inside. A keyed *dynamic* variable
    // behaves the other way round in both cases.
    [
        "(define p (make-keyed-static-variable))", Inert
        "(define b (car p))", Inert
        "(define a (car (cdr p)))", Inert
        "(define e (b 42 (get-current-environment)))", Inert
        // Closed over the environment: reads 42 from anywhere.
        "(define inside (eval (list lambda (list) (list a)) e))", Inert
        "(=? (inside) 42)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``a procedure written outside cannot read the binding even when called inside`` () =
    withKernel (fun env ->
        for expression in
            [ "(define p (make-keyed-static-variable))"
              "(define b (car p))"
              "(define a (car (cdr p)))"
              "(define e (b 42 (get-current-environment)))"
              // `outside` is written here, so (a) in its body resolves against this
              // environment's chain -- which the binder's result is a child of, not a
              // parent of -- however the procedure is later called.
              "(define outside (lambda () (a)))" ] do
            match evalIn env expression with
            | Status message -> failwithf "setup failed: %s" message
            | _ -> ()
        match evalIn env "(eval (list outside) e)" with
        | Status message -> Assert.Contains("unbound", message)
        | value -> failwithf "calling from inside e should still fail, got %s" (showVal value)
        // And plainly outside any such environment.
        match evalIn env "(a)" with
        | Status message -> Assert.Contains("unbound", message)
        | value -> failwithf "(a) should signal an error, got %s" (showVal value))

[<Fact>]
let ``each call to make-keyed-static-variable makes a distinct variable`` () =
    [
        "(define p (make-keyed-static-variable))", Inert
        "(define q (make-keyed-static-variable))", Inert
        "(define bp (car p))", Inert
        "(define ap (car (cdr p)))", Inert
        "(define bq (car q))", Inert
        "(define aq (car (cdr q)))", Inert
        "(define e (bq 99 (bp 42 (get-current-environment))))", Inert
        // One variable's binder does not disturb the other's, and neither accessor
        // reads the other's object.
        "(=? (eval (list ap) e) 42)", Bool true
        "(=? (eval (list aq) e) 99)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the binder requires an environment and the right operand count`` () =
    withKernel (fun env ->
        ignore (evalIn env "(define p (make-keyed-static-variable))")
        let cases =
            [ "((car p) 1 2)", "environment"
              "((car p) 1)", "args"
              "((car p) 1 (get-current-environment) 3)", "args"
              "(make-keyed-static-variable 1)", "args" ]
        for expression, fragment in cases do
            match evalIn env expression with
            | Status message -> Assert.Contains(fragment, message)
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value)
        // The accessor takes none.
        match evalIn env "((car (cdr p)) 1)" with
        | Status _ -> ()
        | value -> failwithf "the accessor takes no operands, got %s" (showVal value))

[<Fact>]
let ``the key is held under a name the reader cannot produce`` () =
    // The key's name contains spaces, so no source text can name it: a spaced name
    // reads as several data, never as one symbol. That is not by itself privacy --
    // string->symbol (13.1.1) will build any name asked of it -- so what actually
    // keeps the key private is the fresh GUID in it, which is never handed out. This
    // checks the half that is checkable.
    match parseOk "(keyed static variable)" with
    | List [Atom "keyed"; Atom "static"; Atom "variable"] -> ()
    | value -> failwithf "a spaced name read as a single datum: %s" (showVal value)

[<Fact>]
let ``the environment the binder returns is otherwise ordinary`` () =
    // The key rides along in the environment's own bindings, so the check that it does
    // not disturb them: defining in the child shadows the parent as usual, and the
    // accessor keeps working afterwards.
    [
        "(define p (make-keyed-static-variable))", Inert
        "(define b (car p))", Inert
        "(define a (car (cdr p)))", Inert
        "(define x 1)", Inert
        "(define e (b 42 (get-current-environment)))", Inert
        "(=? (eval (quote x) e) 1)", Bool true
        "(eval (list define (quote x) 2) e)", Inert
        "(=? (eval (quote x) e) 2)", Bool true
        "(=? x 1)", Bool true
        "(=? (eval (list a) e) 42)", Bool true
    ] |> evalSessionKernel
