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
let ``every entry of module Pair mutation is bound`` () =
    // This began as a guard on the 4.7 divergence's claim that the mutating entries
    // were absent, and forced a deliberate update each time one arrived: set-car! and
    // set-cdr! in ADR 0005 phase 3, encycle! and append! in phase 5. The module is
    // complete now, so it asserts the opposite of what it started as.
    withKernel (fun env ->
        for name in
            [ "set-car!"; "set-cdr!"; "copy-es-immutable"; "copy-es"
              "assq"; "memq?"; "encycle!"; "append!" ] do
            match evalIn env name with
            | Status message -> failwithf "%s should be bound: %s" name message
            | _ -> ())

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
        // 4.7.2: "if object is a mutable pair, then the result is not eq? to object".
        // p was built by `list`, so it is mutable and the copy is fresh.
        "(eqv? (eq? (copy-es-immutable p) p) #f)", Bool true
        "(equal? (copy-es-immutable p) p)", Bool true
        // An already-immutable argument may come back as itself, and does.
        "(eq? (copy-es-immutable (copy-es-immutable p)) (copy-es-immutable (copy-es-immutable p)))",
            Bool false
    ] |> evalSessionKernel

[<Fact>]
let ``set-car! and set-cdr! mutate a pair that other references see`` () =
    // R-1RK 4.7.1. The result is inert, and the mutation is visible through every
    // reference to the pair -- which is the whole reason the representation changed.
    [
        "(define p (list 1 2 3))", Inert
        "(define q p)", Inert
        "(inert? (set-car! p 99))", Bool true
        "(=? (car p) 99)", Bool true
        "(=? (car q) 99)", Bool true
        "(inert? (set-cdr! p (list 7)))", Bool true
        "(=? (car (cdr p)) 7)", Bool true
        "(=? (length p) 2)", Bool true
        // The tail cdr handed out earlier is the same object, so it sees it too.
        "(define r (list 1 2))", Inert
        "(define tail (cdr r))", Inert
        "(set-car! tail 42)", Inert
        "(=? (car (cdr r)) 42)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``mutating an immutable pair signals an error`` () =
    // R-1RK 3.8 requires the error, and 4.7.2 is why a captured algorithm is immutable
    // in the first place: an operative must not be rewritable under the combiner that
    // captured it. A quoted literal is structure the reader produced, so it is
    // immutable; `list` and `cons` build data the program made, so it is not.
    withKernel (fun env ->
        for expression in [ "(set-car! (quote (1 2)) 0)"; "(set-cdr! (quote (1 2)) 0)" ] do
            match evalIn env expression with
            | Status message -> Assert.Contains("immutable", message)
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value)
        // and copy-es-immutable produces structure that refuses the same way
        match evalIn env "(set-car! (copy-es-immutable (list 1 2)) 0)" with
        | Status message -> Assert.Contains("immutable", message)
        | value -> failwithf "mutating an immutable copy should fail, got %s" (showVal value)
        for expression in [ "(set-car! 5 0)"; "(set-car! (list 1))" ] do
            match evalIn env expression with
            | Status _ -> ()
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value))

[<Fact>]
let ``mutability follows where the structure came from`` () =
    [
        "(immutable-pair? (quote (1 2)))", Bool true
        "(eqv? (immutable-pair? (list 1 2)) #f)", Bool true
        "(eqv? (immutable-pair? (cons 1 2)) #f)", Bool true
        "(immutable-pair? (copy-es-immutable (list 1 2)))", Bool true
        // copy-es makes a mutable copy (6.4.2), copy-es-immutable an immutable one.
        "(eqv? (immutable-pair? (copy-es (quote (1 2)))) #f)", Bool true
        // Immutability is deep: there is no way for a mutable pair to be inside an
        // immutable one (4.7.2).
        "(immutable-pair? (car (copy-es-immutable (list (list 1) 2))))", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``cyclic structure does not hang the traversals`` () =
    // set-cdr! makes cycles reachable, so the walks that assumed finite structure have
    // to cope now rather than in a later phase. equal? terminates because a pair of
    // cells already under comparison is taken as equal, which is also the right answer
    // -- two structurally identical cycles are equal.
    [
        "(define p (list 1 2 3))", Inert
        "(set-cdr! (cdr (cdr p)) p)", Inert
        "(pair? p)", Bool true
        "(=? (car p) 1)", Bool true
        "(eq? p p)", Bool true
        "(equal? p p)", Bool true
        "(define q (list 1 2 3))", Inert
        "(set-cdr! (cdr (cdr q)) q)", Inert
        "(equal? p q)", Bool true
        "(eqv? (eq? p q) #f)", Bool true
        // A cycle is not a proper list, so the list predicates say so rather than
        // walking forever.
        "(eqv? (null? p) #f)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``an operative keeps the body it captured even if the source is mutated`` () =
    // This is what ADR 0005 phase 0's acquisition seam was for, and the first point at
    // which it does real work: the compiled-body memo is only sound because $vau took
    // an immutable copy, so rewriting the list the body was built from cannot change
    // what the operative does.
    [
        "(define body (list (list + 1 2)))", Inert
        "(define f (eval (list* vau (list) (quote _) body) (get-current-environment)))", Inert
        "(=? (f) 3)", Bool true
        "(set-car! (car body) *)", Inert
        // The source list changed; the operative did not.
        "(=? (f) 3)", Bool true
        "(=? (f) 3)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``get-list-metrics measures a cycle rather than walking into one`` () =
    // R-1RK 5.7.1: (p n a c) -- pairs, nils, acyclic prefix length, cycle length --
    // with a + c = p, and n and c never both non-zero. It used to answer "acyclic, of
    // this length" unconditionally, which was true only because no list could be
    // cyclic.
    [
        "(define metrics (lambda (x) (get-list-metrics x)))", Inert
        "(equal? (metrics ()) (list 0 1 0 0))", Bool true
        // "if a = c = 0, object is not a pair"
        "(equal? (metrics 5) (list 0 0 0 0))", Bool true
        "(equal? (metrics (list 1 2 3)) (list 3 1 3 0))", Bool true
        // "if n = c = 0, the improper list is not a list"
        "(equal? (metrics (cons 1 2)) (list 1 0 1 0))", Bool true
        // A list that is all cycle.
        "(define p (list 1 2 3))", Inert
        "(set-cdr! (cdr (cdr p)) p)", Inert
        "(equal? (metrics p) (list 3 0 0 3))", Bool true
        // A cycle behind an acyclic prefix: a + c = p still holds.
        "(define q (list 1 2 3 4 5))", Inert
        "(set-cdr! (cdr (cdr (cdr (cdr q)))) (cdr (cdr q)))", Inert
        "(equal? (metrics q) (list 5 0 2 3))", Bool true
        // A pair whose cdr is itself.
        "(define r (list 1))", Inert
        "(set-cdr! r r)", Inert
        "(equal? (metrics r) (list 1 0 0 1))", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``length and the list predicates read the shape rather than walking it`` () =
    // R-1RK 6.3.1: length is "the number of consecutive cdr references that can be
    // followed", zero for a non-pair and positive infinity for a cyclic list. 6.3.8
    // and 6.3.9: finite-list? is the acyclic lists, countable-list? the lists at all.
    // All three would run forever on a cyclic argument if they cdr'd down it.
    [
        "(define p (list 1 2 3))", Inert
        "(set-cdr! (cdr (cdr p)) p)", Inert
        "(=? (length (list 1 2 3)) 3)", Bool true
        "(=? (length ()) 0)", Bool true
        "(=? (length 5) 0)", Bool true
        "(=? (length (cons 1 2)) 1)", Bool true
        "(eqv? (length p) #e+infinity)", Bool true
        "(finite-list? (list 1 2))", Bool true
        "(finite-list? ())", Bool true
        "(eqv? (finite-list? p) #f)", Bool true
        "(eqv? (finite-list? (cons 1 2)) #f)", Bool true
        "(countable-list? (list 1 2))", Bool true
        // A cyclic list is a list; an improper one is not.
        "(countable-list? p)", Bool true
        "(eqv? (countable-list? (cons 1 2)) #f)", Bool true
        // Both are variadic and true for no arguments.
        "(finite-list?)", Bool true
        "(countable-list?)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``encycle! gives a list the prefix and cycle it is asked for`` () =
    // R-1RK 5.8.1: sets the cdr of the (prefix + cycle)th pair to refer to the
    // (prefix + 1)th, so the list ends up with exactly those metrics.
    [
        "(define a (list 1 2 3 4 5))", Inert
        "(inert? (encycle! a 2 3))", Bool true
        "(equal? (get-list-metrics a) (list 5 0 2 3))", Bool true
        // A cycle covering the whole list.
        "(define b (list 1 2 3))", Inert
        "(encycle! b 0 3)", Inert
        "(equal? (get-list-metrics b) (list 3 0 0 3))", Bool true
        "(eqv? (length b) #e+infinity)", Bool true
        // "If integer2 = 0, the applicative does nothing."
        "(define c (list 1 2 3))", Inert
        "(encycle! c 1 0)", Inert
        "(equal? (get-list-metrics c) (list 3 1 3 0))", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``encycle! rejects counts it cannot use`` () =
    withKernel (fun env ->
        // A negative count would count down past zero for ever rather than signal.
        for expression in
            [ "(encycle! (list 1 2 3) -1 1)"; "(encycle! (list 1 2 3) 1 -1)"
              "(encycle! (list 1 2 3) 1.5 1)" ] do
            match evalIn env expression with
            | Status _ -> ()
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value)
        // "The improper list starting at object must contain at least integer1 +
        // integer2 pairs."
        match evalIn env "(encycle! (list 1 2) 2 3)" with
        | Status _ -> ()
        | value -> failwithf "too few pairs should signal an error, got %s" (showVal value))

[<Fact>]
let ``append! links the lists by mutating the first`` () =
    // R-1RK 6.4.1. Only the first argument is ever the mutation target, which falls
    // out of the report's own equivalence: appending v to u leaves u's last pair
    // inside v, so appending w next reaches the end of both.
    [
        "(define u (list 1 2))", Inert
        "(define v (list 3 4))", Inert
        "(inert? (append! u v))", Bool true
        "(equal? u (list 1 2 3 4))", Bool true
        // It links rather than copies: the tail *is* v.
        "(eq? (cdr (cdr u)) v)", Bool true
        // Three arguments chain left to right.
        "(define x (list 1))", Inert
        "(append! x (list 2) (list 3))", Inert
        "(equal? x (list 1 2 3))", Bool true
        // "the next non-nil argument": a nil argument is skipped.
        "(define y (list 1))", Inert
        "(append! y () (list 9))", Inert
        "(equal? y (list 1 9))", Bool true
        // (append! v) is inert and does nothing.
        "(define z (list 1))", Inert
        "(inert? (append! z))", Bool true
        "(equal? z (list 1))", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``append! rejects arguments it cannot mutate`` () =
    withKernel (fun env ->
        // The first argument must be a nonempty acyclic list.
        for expression in [ "(append!)"; "(append! () (list 1))" ] do
            match evalIn env expression with
            | Status _ -> ()
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value)
        // A cyclic first argument has no last pair to write into, and is refused
        // rather than walked for ever.
        match evalIn env "(let ((p (list 1 2))) (encycle! p 0 2) (append! p (list 3)))" with
        | Status message -> Assert.Contains("acyclic", message)
        | value -> failwithf "a cyclic argument should signal an error, got %s" (showVal value))
