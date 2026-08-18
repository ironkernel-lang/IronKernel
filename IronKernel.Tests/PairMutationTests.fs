module IronKernel.Tests.PairMutationTests

open Xunit
open IronKernel.Ast
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``assq and memq? search by eq?`` () =
    // R-1RK 6.4.3 / 6.4.4: assoc and member? with eq? in place of equal?.
    [
        "(define al (list (list 1 'a) (list 2 'b)))", Inert
        "(=? (car (assq 2 al)) 2)", Bool true
        "(eqv? (car (cdr (assq 2 al))) 'b)", Bool true
        // Nil when there is no such element, not an error.
        "(null? (assq 9 al))", Bool true
        "(null? (assq 1 (list)))", Bool true
        "(memq? 2 (list 1 2 3))", Bool true
        "(eqv? (memq? 9 (list 1 2 3)) #f)", Bool true
        // memq? of anything in the empty list is false.
        "(eqv? (memq? 1 (list)) #f)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``copy-es copies the evaluation structure and leaves non-pairs alone`` () =
    // R-1RK 6.4.2: a non-pair is returned as is; a pair gives a structure that is
    // initially equal? to the argument, with non-pair referents eq? to the originals.
    [
        "(=? (copy-es 5) 5)", Bool true
        "(eqv? (copy-es 'a) 'a)", Bool true
        "(define nested (list (list 1 2) (list 3 (list 4))))", Inert
        "(equal? (copy-es nested) nested)", Bool true
        "(pair? (copy-es nested))", Bool true
        // The structure is walked to the leaves, not copied one level deep.
        "(=? (car (car (cdr nested))) 3)", Bool true
        "(=? (car (car (cdr (copy-es nested)))) 3)", Bool true
        // and to the leaf below that.
        "(=? (car (car (cdr (car (cdr nested))))) 4)", Bool true
        "(=? (car (car (cdr (car (cdr (copy-es nested)))))) 4)", Bool true
        // Non-pair referents come through as themselves.
        "(eq? (car (car (copy-es (list (list 'a))))) 'a)", Bool true
        // The evaluation structure includes the cdr of an improper pair.
        "(=? (cdr (copy-es (cons 1 2))) 2)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``copy-es-immutable returns something equal? with an immutable structure`` () =
    // R-1RK 4.7.2. Every IronKernel pair is already immutable, and the report allows
    // the result to be eq? to the argument in exactly that case, so returning the
    // argument satisfies the entry rather than approximating it.
    [
        "(=? (copy-es-immutable 5) 5)", Bool true
        "(define nested (list (list 1 2) 3))", Inert
        "(equal? (copy-es-immutable nested) nested)", Bool true
        "(pair? (copy-es-immutable nested))", Bool true
        "(equal? (copy-es-immutable nested) (copy-es nested))", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the mutating half of the module is genuinely absent`` () =
    // Guarding the claim in the 4.7 divergence: these are not quietly bound to
    // something that does nothing. A later change that adds them should have to
    // update this test deliberately.
    withKernel (fun env ->
        for name in [ "set-car!"; "set-cdr!"; "encycle!"; "append!" ] do
            match evalIn env name with
            | Status message -> Assert.Contains("unbound", message.ToLowerInvariant())
            | value -> failwithf "%s should be unbound, got %s" name (showVal value))

[<Fact>]
let ``copy-es-immutable and copy-es take exactly one argument`` () =
    withKernel (fun env ->
        for expression in [ "(copy-es-immutable)"; "(copy-es-immutable 1 2)" ] do
            match evalIn env expression with
            | Status _ -> ()
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value))

[<Fact>]
let ``a memoised body keeps answering as the body that was captured`` () =
    // OperativeRecord.compiledBody memoises the compiled form of a body after first
    // application, so the second call runs the memo rather than the captured forms.
    // That is sound only while the body cannot change after $vau captured it, which
    // is what immutable acquisition guarantees (R-1RK 4.10.3 / 4.7.2, ADR 0005
    // phase 0). Applying an operative repeatedly, and through both the interpreted
    // and the compiled construction paths, has to keep giving the captured answer.
    [
        "(define f (vau (x) _ (+ 1 2)))", Inert
        "(=? (f 0) 3)", Bool true
        "(=? (f 0) 3)", Bool true
        "(=? (f 0) 3)", Bool true
        // A wrapped one, whose body runs through the same memo.
        "(define g (wrap (vau (x) _ (* x 2))))", Inert
        "(=? (g 21) 42)", Bool true
        "(=? (g 21) 42)", Bool true
        // Rebinding a name the body mentions is lexical, not a change to the body:
        // the operative keeps its closure and the memo stays correct.
        "(define n 1)", Inert
        "(define h (wrap (vau () _ n)))", Inert
        "(=? (h) 1)", Bool true
        "(set! (get-current-environment) n 2)", Inert
        "(=? (h) 2)", Bool true
        "(=? (h) 2)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the empty list has one spelling that a program can observe`` () =
    // The type carries both `Nil` and `List []`, and only the second was recognised.
    // Applying #inert produced the bare case, which was neither `null?` nor `eqv?` to
    // itself -- a value not equal to itself breaks the reflexivity R-1RK 4.3.1
    // requires of an equivalence predicate. ADR 0005 phase 1 removes the duplicate
    // case; until then the producers normalise and the predicates accept both.
    [
        "(null? (#inert))", Bool true
        "(eqv? (#inert) (#inert))", Bool true
        "(equal? (#inert) (#inert))", Bool true
        // and it is the same empty list as one built at runtime
        "(eqv? (#inert) (list))", Bool true
        "(eqv? (#inert) (cdr (list 1)))", Bool true
        "(eqv? (list) (list))", Bool true
        // still not a pair, and still counts as a list
        "(eqv? (pair? (#inert)) #f)", Bool true
        "(=? (length (#inert)) 0)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``eq? distinguishes pairs that equal? does not`` () =
    // R-1RK 4.2.1: eq? is "effectively the same object, even in the presence of
    // mutation", and the report is explicit that "two pairs returned by different
    // calls to cons are not eq?, even if they have the same car and cdr and the
    // implementation doesn't support pair mutation". equal? is the weaker predicate
    // (4.3.1) and still says they look alike.
    [
        "(eqv? (eq? (list 1) (list 1)) #f)", Bool true
        "(eqv? (eq? (cons 1 2) (cons 1 2)) #f)", Bool true
        "(equal? (list 1) (list 1))", Bool true
        // The same pair, reached two different ways, is the same pair.
        "(define p (list 1 2))", Inert
        "(eq? p p)", Bool true
        "(eq? p (car (list p)))", Bool true
        // cdr shares the tail rather than copying it, so the tail is one object.
        "(eq? (cdr p) (cdr p))", Bool true
        "(eq? (car (cdr (list 0 p))) p)", Bool true
        // Environments have identity for the same reason the report gives.
        "(eqv? (eq? (make-environment) (make-environment)) #f)", Bool true
        "(define e (make-environment))", Inert
        "(eq? e e)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``both equivalence predicates are reflexive on every kind of object`` () =
    // The structural walk covered only the types with a structural comparison and let
    // everything else fall through to false, so an environment, a vector and even a
    // primitive combiner were not equal to themselves. Reflexivity is rule 1 of both
    // 4.2.1 and 4.3.1.
    [
        "(define e (get-current-environment))", Inert
        "(define v (vector 1 2))", Inert
        "(eq? e e)", Bool true
        "(equal? e e)", Bool true
        "(eq? v v)", Bool true
        "(equal? v v)", Bool true
        "(eq? car car)", Bool true
        "(equal? car car)", Bool true
        "(define f (lambda (x) x))", Inert
        "(eq? f f)", Bool true
        "(call/cc (lambda (k) (eq? k k)))", Bool true
        // and on the values that already had a comparison
        "(eq? 'a 'a)", Bool true
        "(eq? 1 1)", Bool true
        "(eq? () ())", Bool true
        "(eq? #t #t)", Bool true
        "(eq? #inert #inert)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``eq? and equal? take zero or more arguments`` () =
    // R-1RK 6.5.1 and 6.6.1 generalize both to zero or more: true unless some two of
    // the arguments differ. Both used to require exactly two.
    [
        "(eq?)", Bool true
        "(eq? 'a)", Bool true
        "(eq? 'a 'a 'a)", Bool true
        "(eqv? (eq? 'a 'a 'b) #f)", Bool true
        "(equal?)", Bool true
        "(equal? 1)", Bool true
        "(equal? (list 1) (list 1) (list 1))", Bool true
        "(eqv? (equal? (list 1) (list 1) (list 2)) #f)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``copy-es returns a pair that is not eq? to its argument`` () =
    // R-1RK 6.4.2 promises this outright. It was unobservable while eq? compared
    // structurally, which is why the 4.7 divergence used to say so.
    [
        "(define p (list 1 (list 2)))", Inert
        "(eqv? (eq? (copy-es p) p) #f)", Bool true
        "(equal? (copy-es p) p)", Bool true
        // The copy goes all the way down: the nested pair is fresh too.
        "(eqv? (eq? (car (cdr (copy-es p))) (car (cdr p))) #f)", Bool true
        // Non-pair referents come through as themselves (4.7.2's "corresponding
        // non-pair referents being eq?").
        "(eq? (car (copy-es (list 'a))) 'a)", Bool true
        // copy-es-immutable may return its argument, and does.
        "(eq? (copy-es-immutable p) p)", Bool true
    ] |> evalSessionKernel
