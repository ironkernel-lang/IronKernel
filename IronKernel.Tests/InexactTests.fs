module IronKernel.Tests.InexactTests

open Xunit
open IronKernel.Ast
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``the exact infinities are exact reals that are not finite`` () =
    // R-1RK 12.3.2: "Every implementation of Kernel must support the two exact real
    // infinity objects, positive and negative." They are part of the required
    // baseline, not of an optional module.
    [
        "(number? #e+infinity)", Bool true
        "(real? #e+infinity)", Bool true
        "(exact? #e+infinity)", Bool true
        "(robust? #e+infinity)", Bool true
        "(eqv? (finite? #e+infinity) #f)", Bool true
        // 12.5.14 calls an integer-or-infinity an *improper* integer, so an infinity
        // is neither an integer nor a rational.
        "(eqv? (integer? #e+infinity) #f)", Bool true
        "(eqv? (rational? #e+infinity) #f)", Bool true
        "(eqv? (zero? #e+infinity) #f)", Bool true
        "(positive? #e+infinity)", Bool true
        "(negative? #e-infinity)", Bool true
        // There are two of them, and each is one object.
        "(eq? #e+infinity #e+infinity)", Bool true
        "(eqv? (eqv? #e+infinity #e-infinity) #f)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``arithmetic on the exact infinities follows the report`` () =
    [
        "(eqv? (+ #e+infinity 5) #e+infinity)", Bool true
        "(eqv? (+ #e+infinity #e+infinity) #e+infinity)", Bool true
        "(eqv? (- #e+infinity 5) #e+infinity)", Bool true
        "(eqv? (- 5 #e+infinity) #e-infinity)", Bool true
        "(eqv? (- #e+infinity #e-infinity) #e+infinity)", Bool true
        "(eqv? (* #e+infinity 5) #e+infinity)", Bool true
        "(eqv? (* #e+infinity -5) #e-infinity)", Bool true
        "(eqv? (* #e-infinity #e-infinity) #e+infinity)", Bool true
        "(eqv? (/ #e+infinity 5) #e+infinity)", Bool true
        // A finite real over an infinity is the one case with a finite answer.
        "(eqv? (/ 5 #e+infinity) 0)", Bool true
        // Every finite real lies strictly between the two, whatever its exact type.
        "(<? 5 #e+infinity)", Bool true
        "(<? 1/3 #e+infinity)", Bool true
        "(<? 123456789012345678901234567890 #e+infinity)", Bool true
        "(<? #e-infinity #e+infinity)", Bool true
        "(eqv? (<? #e+infinity 5) #f)", Bool true
        "(<=? #e+infinity #e+infinity)", Bool true
        "(eqv? (abs #e-infinity) #e+infinity)", Bool true
        "(eqv? (floor #e+infinity) #e+infinity)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the indeterminate infinity combinations have no primary value`` () =
    // R-1RK 12.2: the result of these has no primary value, and whether that signals
    // is the strict-arithmetic variable's decision (12.6.6). Strict is the default.
    withKernel (fun env ->
        for expression in
            [ "(- #e+infinity #e+infinity)"      // no answer: any finite difference fits
              "(+ #e+infinity #e-infinity)"
              "(* 0 #e+infinity)"                // nothing times zero is infinite
              "(/ #e+infinity #e+infinity)" ] do
            match evalIn env expression with
            | Status message -> Assert.Contains("no primary value", message)
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value)
        // Dividing by zero is still a division by zero, not a no-primary-value.
        match evalIn env "(/ #e+infinity 0)" with
        | Status message -> Assert.Contains("division by zero", message)
        | value -> failwithf "dividing an infinity by zero returned %s" (showVal value))

[<Fact>]
let ``max min gcd and lcm take the report's values at their edges`` () =
    // These were all divergences until the exact infinities existed to return.
    [
        "(eqv? (max) #e-infinity)", Bool true
        "(eqv? (min) #e+infinity)", Bool true
        "(eqv? (gcd) #e+infinity)", Bool true
        "(=? (lcm) 1)", Bool true
        // "if gcd is called with at least one finite non-zero argument, its result is
        // the same as if all zero and infinite arguments were deleted" -- which is why
        // gcd cannot be folded pairwise: (gcd #e+infinity 0) alone is indeterminate.
        "(=? (gcd 0 5) 5)", Bool true
        "(=? (gcd #e+infinity 6) 6)", Bool true
        "(=? (gcd #e+infinity 0 5) 5)", Bool true
        "(eqv? (gcd #e+infinity #e-infinity) #e+infinity)", Bool true
        "(eqv? (lcm 3 #e+infinity) #e+infinity)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``gcd and lcm signal where the report has no primary value`` () =
    withKernel (fun env ->
        // A zero argument with nothing finite and non-zero beside it.
        for expression in [ "(gcd 0)"; "(gcd 0 #e+infinity)"; "(lcm 0 5)" ] do
            match evalIn env expression with
            | Status message -> Assert.Contains("no primary value", message)
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value))

[<Fact>]
let ``exactness is partitioned the way the report describes`` () =
    // R-1RK 12.6.1. The tag distinguishing exact from inexact is the internal
    // representation: float32 and double are inexact, every other real is exact.
    [
        "(exact? 1)", Bool true
        "(exact? 1/2)", Bool true
        "(exact? 123456789012345678901234567890)", Bool true
        "(eqv? (exact? 0.5) #f)", Bool true
        "(inexact? 0.5)", Bool true
        "(eqv? (inexact? 1) #f)", Bool true
        // 12.2: "an exact real is considered to be robust". Inexact reals here claim
        // no bounds, so none of them is robust.
        "(robust? 1 1/2 #e+infinity)", Bool true
        "(eqv? (robust? 0.5) #f)", Bool true
        // The undefined number arises only from a lower bound above an upper bound,
        // which infinite bounds never allow.
        "(eqv? (undefined? 0.5) #f)", Bool true
        // All four are variadic and true for the empty argument list.
        "(exact?)", Bool true
        "(inexact?)", Bool true
        "(robust?)", Bool true
        "(undefined?)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the predicates take numbers rather than arbitrary objects`` () =
    // 12.6.1's rationale: these are not type predicates, so a non-number is an error
    // rather than false. They do not depend on a primary value, though, which is why
    // a NaN argument is answered instead of signalled.
    withKernel (fun env ->
        for expression in [ "(exact? 'a)"; "(inexact? \"s\")"; "(robust? #t)"; "(undefined? ())" ] do
            match evalIn env expression with
            | Status _ -> ()
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value)
        match evalIn env "(with-strict-arithmetic #f (lambda () (undefined? (- #e+infinity #e+infinity))))" with
        | Bool false -> ()
        | value -> failwithf "undefined? on a no-primary-value real gave %s" (showVal value))

[<Fact>]
let ``bounds and primary values report the sanctioned model`` () =
    // R-1RK 12.6.2 and 12.6.3. An exact real is its own bounds and its own primary
    // value; an inexact real is bounded only by the infinities.
    [
        "(eqv? (car (get-real-internal-bounds 5)) 5)", Bool true
        "(eqv? (car (cdr (get-real-internal-bounds 5))) 5)", Bool true
        "(eqv? (car (get-real-exact-bounds 0.5)) #e-infinity)", Bool true
        "(eqv? (car (cdr (get-real-exact-bounds 0.5))) #e+infinity)", Bool true
        // The internal bounds keep the format of the primary value, so they are the
        // inexact infinities rather than the exact ones.
        "(inexact? (car (get-real-internal-bounds 0.5)))", Bool true
        "(eqv? (finite? (car (get-real-internal-bounds 0.5))) #f)", Bool true
        "(eqv? (get-real-internal-primary 0.5) 0.5)", Bool true
        // The exact value of a finite double is exact, because a double is a dyadic
        // rational and exact ratios hold it in full.
        "(eqv? (get-real-exact-primary 0.5) 1/2)", Bool true
        "(eqv? (get-real-exact-primary 0.1) 3602879701896397/36028797018963968)", Bool true
        // Which is the same conversion real->exact performs (12.6.5).
        "(eqv? (real->exact 0.1) (get-real-exact-primary 0.1))", Bool true
        "(exact? (real->exact 0.5))", Bool true
        "(inexact? (real->inexact 1))", Bool true
        "(=? (real->inexact 1) 1)", Bool true
        "(eqv? (real->inexact 0.5) 0.5)", Bool true
        // 12.6.4: the primary value comes from the middle argument.
        "(inexact? (make-inexact 0 1/2 1))", Bool true
        "(=? (make-inexact 0 1/2 1) 0.5)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``the bounds applicatives take a real and a defined primary value`` () =
    withKernel (fun env ->
        // A complex is not a real; 12.6.3's rationale leaves those out for now.
        for expression in
            [ "(get-real-internal-bounds (make-rectangular 1 1))"
              "(get-real-exact-bounds 'a)"
              "(get-real-internal-primary \"s\")"
              "(make-inexact 0 1)" ] do
            match evalIn env expression with
            | Status _ -> ()
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value)
        // 12.6.3: both signal when there is no primary value, which keeps
        // get-real-exact-primary's promise to return an exact real.
        for expression in
            [ "(with-strict-arithmetic #f (lambda () (get-real-internal-primary (- #e+infinity #e+infinity))))"
              "(with-strict-arithmetic #f (lambda () (get-real-exact-primary (- #e+infinity #e+infinity))))" ] do
            match evalIn env expression with
            | Status message -> Assert.Contains("no primary value", message)
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value))

[<Fact>]
let ``strict arithmetic is a keyed dynamic variable with a default`` () =
    // R-1RK 12.6.6: "These applicatives are the binder and accessor of the
    // strict-arithmetic keyed dynamic variable." The report leaves the initial value
    // open; true is what IronKernel has always done.
    [
        "(get-strict-arithmetic?)", Bool true
        "(with-strict-arithmetic #f (lambda () (get-strict-arithmetic?)))", Bool false
        "(with-strict-arithmetic #t (lambda () (get-strict-arithmetic?)))", Bool true
        // It nests and unwinds like the keyed dynamic variable it is.
        "(with-strict-arithmetic #f (lambda () (with-strict-arithmetic #t (lambda () (get-strict-arithmetic?)))))",
            Bool true
        "(with-strict-arithmetic #f (lambda () (with-strict-arithmetic #t (lambda () 0)) (get-strict-arithmetic?)))",
            Bool false
        "(get-strict-arithmetic?)", Bool true
        // Cleared, a result with no primary value is returned instead of signalled --
        // it is a number, and neither robust nor undefined.
        "(with-strict-arithmetic #f (lambda () (number? (- #e+infinity #e+infinity))))", Bool true
        "(with-strict-arithmetic #f (lambda () (robust? (* 0 #e+infinity))))", Bool false
        // And the setting follows the dynamic extent, so a procedure called inside it
        // is affected even though it was written outside.
        "(define blows-up (lambda () (- #e+infinity #e+infinity)))", Inert
        "(with-strict-arithmetic #f (lambda () (number? (blows-up))))", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``with-strict-arithmetic requires a boolean and a combiner`` () =
    withKernel (fun env ->
        for expression in
            [ "(with-strict-arithmetic 1 (lambda () 0))"
              "(with-strict-arithmetic #f)"
              "(get-strict-arithmetic? 1)" ] do
            match evalIn env expression with
            | Status _ -> ()
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value))

[<Fact>]
let ``narrow arithmetic is a keyed dynamic variable that starts cleared`` () =
    // R-1RK 12.7.1. Narrowing is advice the client asks for, so it starts off.
    [
        "(eqv? (get-narrow-arithmetic?) #f)", Bool true
        "(with-narrow-arithmetic #t (lambda () (get-narrow-arithmetic?)))", Bool true
        "(with-narrow-arithmetic #t (lambda () (with-narrow-arithmetic #f (lambda () (get-narrow-arithmetic?)))))",
            Bool false
        "(with-narrow-arithmetic #t (lambda () (with-narrow-arithmetic #f (lambda () 0)) (get-narrow-arithmetic?)))",
            Bool true
        "(eqv? (get-narrow-arithmetic?) #f)", Bool true
        // The two arithmetic variables of 12.6.6 and 12.7.1 are separate.
        "(with-narrow-arithmetic #t (lambda () (get-strict-arithmetic?)))", Bool true
        "(with-strict-arithmetic #f (lambda () (get-narrow-arithmetic?)))", Bool false
    ] |> evalSessionKernel

[<Fact>]
let ``the bounds are no less restrictive when narrow arithmetic is set`` () =
    // This is the report's only hard constraint on the information maintained, besides
    // correctness: it "cannot be less restrictive when the variable is true than when
    // the variable is false". IronKernel narrows nothing, so the two intervals are
    // equal, which satisfies containment -- and the check would catch a later change
    // that made the narrow bounds *wider* rather than tighter.
    [
        "(define wide (with-narrow-arithmetic #f (lambda () (get-real-exact-bounds 0.5))))", Inert
        "(define narrow (with-narrow-arithmetic #t (lambda () (get-real-exact-bounds 0.5))))", Inert
        "(<=? (car wide) (car narrow))", Bool true
        "(<=? (car (cdr narrow)) (car (cdr wide)))", Bool true
        // And robustness cannot go backwards either.
        "(define robust-wide (with-narrow-arithmetic #f (lambda () (robust? 0.5))))", Inert
        "(define robust-narrow (with-narrow-arithmetic #t (lambda () (robust? 0.5))))", Inert
        "(if robust-wide robust-narrow #t)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``with-narrow-arithmetic requires a boolean and a combiner`` () =
    withKernel (fun env ->
        for expression in
            [ "(with-narrow-arithmetic 1 (lambda () 0))"
              "(with-narrow-arithmetic #t)"
              "(get-narrow-arithmetic? 1)" ] do
            match evalIn env expression with
            | Status _ -> ()
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value))

[<Fact>]
let ``strict arithmetic signals on overflow`` () =
    // R-1RK 12.3.3: "A numeric overflow occurs when the primary value of an inexact
    // result would exceed the largest magnitude representable by its restricted
    // format." Under a cleared strict-arithmetic that gives an infinity, which is what
    // the report says for that case; set, it is one of the events that signal.
    [
        "(with-strict-arithmetic #f (lambda () (eqv? (finite? (* 1e308 10)) #f)))", Bool true
        "(with-strict-arithmetic #f (lambda () (positive? (* 1e308 10))))", Bool true
        // An infinite operand going in is not an overflow, whatever comes out --
        // detecting it needs the operands, not just the result.
        "(eqv? (+ #e+infinity 1) #e+infinity)", Bool true
        "(eqv? (* #e+infinity 2) #e+infinity)", Bool true
        // Ordinary arithmetic is untouched.
        "(=? (* 2 3) 6)", Bool true
        "(=? (* 2.0 3.0) 6.0)", Bool true
        "(=? (+ 1e300 1e300) 2e300)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``an overflow under strict arithmetic is an error`` () =
    withKernel (fun env ->
        for expression in [ "(* 1e308 10)"; "(+ 1e308 1e308)"; "(- (- 0 1e308) 1e308)" ] do
            match evalIn env expression with
            | Status message -> Assert.Contains("overflow", message)
            | value -> failwithf "%s should signal an error, got %s" expression (showVal value)
        // Underflow is not detected, and is recorded as a divergence rather than
        // guessed at: a zero result from non-zero operands is an underflow for
        // multiplication and an exact answer for subtraction.
        match evalIn env "(* 1e-300 1e-300)" with
        | Obj (:? double as value) -> Assert.Equal(0.0, value)
        | value -> failwithf "underflow gave %s" (showVal value))
