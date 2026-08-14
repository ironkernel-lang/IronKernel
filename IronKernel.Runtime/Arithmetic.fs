namespace IronKernel

    open Ast
    open Choice
    open Errors
    open System

    module Arithmetic =

        /// Operand pair widened to a common numeric representation.
        /// Promotion rank: byte < int32 < int64 < float32 < double < complex, except
        /// that int64 paired with float32 widens to double, because float32 cannot
        /// represent every int64. Complex sits at the top because every real is a
        /// complex with zero imaginary part (R-1RK 12.10).
        type private Widened =
            | Bytes of byte * byte
            | Ints of int32 * int32
            | Longs of int64 * int64
            | Bigs of Numerics.BigInteger * Numerics.BigInteger
            | Ratios of ExactRatio * ExactRatio
            | Singles of float32 * float32
            | Doubles of double * double
            | Complexes of Numerics.Complex * Numerics.Complex

        type private BadOperand =
            | FirstOperand
            | SecondOperand

        let private rankOf (value: obj) =
            match value with
            | :? byte -> 0
            | :? int32 -> 1
            | :? int64 -> 2
            // Exact integers of arbitrary size (R-1RK 12.3.2) rank above the fixed
            // widths and below the inexact reals.
            | :? Numerics.BigInteger -> 3
            // Exact ratios of exact integers (R-1RK 12.8) are still exact, so they
            // rank above the integers and below the inexact reals.
            | :? ExactRatio -> 4
            | :? float32 -> 5
            | :? double -> 6
            | :? Numerics.Complex -> 7
            | _ -> -1

        let private rankName = function
            | 0 -> "byte"
            | 1 -> "int32"
            | 2 -> "int64"
            | 3 -> "integer"
            | 4 -> "rational"
            | 5 -> "float32"
            | 6 -> "float"
            | _ -> "complex"

        let private toInt (value: obj) =
            match value with
            | :? byte as v -> int v
            | _ -> value :?> int

        let private toLong (value: obj) =
            match value with
            | :? byte as v -> int64 v
            | :? int32 as v -> int64 v
            | _ -> value :?> int64

        let private toBig (value: obj) =
            match value with
            | :? byte as v -> Numerics.BigInteger(int v)
            | :? int32 as v -> Numerics.BigInteger v
            | :? int64 as v -> Numerics.BigInteger v
            | _ -> value :?> Numerics.BigInteger

        let private toRatio (value: obj) =
            match value with
            | :? ExactRatio as r -> r
            | other -> makeExactRatio (toBig other) Numerics.BigInteger.One

        let private toSingle (value: obj) =
            match value with
            | :? byte as v -> float32 v
            | :? int32 as v -> float32 v
            | :? int64 as v -> float32 v
            | :? Numerics.BigInteger as v -> float32 v
            | :? ExactRatio as r -> float32 (double r.Numerator / double r.Denominator)
            | _ -> value :?> float32

        let private toDouble (value: obj) =
            match value with
            | :? byte as v -> double v
            | :? int32 as v -> double v
            | :? int64 as v -> double v
            | :? Numerics.BigInteger as v -> double v
            | :? ExactRatio as r -> double r.Numerator / double r.Denominator
            | :? float32 as v -> double v
            | _ -> value :?> double

        let private toComplex (value: obj) =
            match value with
            | :? Numerics.Complex as v -> v
            | other -> Numerics.Complex(toDouble other, 0.0)

        let private widen (a: obj) (b: obj) =
            let rankA = rankOf a
            let rankB = rankOf b
            if rankA < 0 then Choice1Of2 FirstOperand
            elif rankB < 0 then Choice1Of2 SecondOperand
            else
                let target =
                    // float32 cannot represent every wide exact value, so pairing one
                    // with an exact type above int32 widens to double instead.
                    if min rankA rankB >= 2 && min rankA rankB <= 4 && max rankA rankB = 5 then 6
                    else max rankA rankB
                Choice2Of2(
                    match target with
                    | 0 -> Bytes(a :?> byte, b :?> byte)
                    | 1 -> Ints(toInt a, toInt b)
                    | 2 -> Longs(toLong a, toLong b)
                    | 3 -> Bigs(toBig a, toBig b)
                    | 4 -> Ratios(toRatio a, toRatio b)
                    | 5 -> Singles(toSingle a, toSingle b)
                    | 6 -> Doubles(toDouble a, toDouble b)
                    | _ -> Complexes(toComplex a, toComplex b))

        /// No exception handler and no validation hook on this path. F# addition,
        /// subtraction and multiplication are unchecked and wrap rather than raise, so
        /// a handler would guard against nothing while sitting on the hottest operation
        /// in the language; division is the only arithmetic that can raise, and it is
        /// implemented separately below with its own checks.
        /// R-1RK 12.3.2's exact infinities sit outside the widening tower: an infinity
        /// paired with a finite number has no common representation, so each operation
        /// takes the infinite cases apart first and widens only what is left.
        ///
        /// A combination with no answer -- infinity minus infinity, zero times
        /// infinity, infinity over infinity -- produces a result with no primary value
        /// (12.2), which is NaN here. Whether that signals is not arithmetic's
        /// decision: it depends on the strict-arithmetic keyed dynamic variable
        /// (12.6.6), which needs the continuation, so the primitives resolve it.
        let private noPrimaryValue : obj = box System.Double.NaN

        let private signOf = function
            | ExactPositiveInfinity -> 1
            | ExactNegativeInfinity -> -1

        let private infinityOfSign sign =
            if sign >= 0 then ExactPositiveInfinity else ExactNegativeInfinity

        /// The sign of a finite real, or None when it is not a real at all. Complex
        /// numbers have no order, so they have no sign for an infinity to combine with.
        let private finiteSign (value: obj) =
            match value with
            | :? byte as v -> Some(compare v 0uy)
            | :? int32 as v -> Some(compare v 0)
            | :? int64 as v -> Some(compare v 0L)
            | :? Numerics.BigInteger as v -> Some v.Sign
            | :? ExactRatio as v -> Some v.Numerator.Sign
            | :? float32 as v -> if Single.IsNaN v then None else Some(compare v 0.0f)
            | :? double as v -> if Double.IsNaN v then None else Some(compare v 0.0)
            | _ -> None

        let private numericBinaryOp apply (a': LispVal) (b': LispVal) =
            match a', b' with
            | Obj a, Obj b ->
                match widen a b with
                | Choice2Of2 widened -> returnM (Obj(apply widened))
                | Choice1Of2 FirstOperand ->
                    throwError (ClrTypeMismatch("number", a.GetType().Name))
                | Choice1Of2 SecondOperand ->
                    throwError (ClrTypeMismatch(rankName (rankOf a), b.GetType().Name))
            | Obj _, found -> throwError (TypeMismatch("object", found))
            | found, _ -> throwError (TypeMismatch("object", found))

        /// `apply` returns `None` when the comparison is undefined for the operands.
        /// Complex numbers are not ordered, and R-1RK confines <? and friends to reals
        /// (12.5.3), so ordering a complex is an error rather than some default.
        let private comparisonBinaryOp apply (a': LispVal) (b': LispVal) =
            match a', b' with
            | Obj a, Obj b ->
                match widen a b with
                | Choice2Of2 widened ->
                    match apply widened with
                    | Some result -> returnM (Bool result)
                    | None -> throwError (Default "complex numbers are not ordered")
                | Choice1Of2 FirstOperand ->
                    throwError (TypeMismatch(b.GetType().Name, Obj a))
                | Choice1Of2 SecondOperand ->
                    throwError (TypeMismatch(a.GetType().Name, Obj b))
            | Obj _, found -> throwError (TypeMismatch("object", found))
            | found, _ -> throwError (TypeMismatch("object", found))

        /// A complex result with a zero imaginary part collapses back to a real, so
        /// arithmetic that happens to leave the imaginary axis does not leave every
        /// later operation working in complex.
        let private ofComplex (value: Numerics.Complex) : obj =
            if value.Imaginary = 0.0 then box value.Real else box value

        /// An exact integer result that no longer fits its fixed width promotes to
        /// BigInteger instead of wrapping. R-1RK 12.3.2 requires exact integers of
        /// arbitrary size, and silent wraparound returns a wrong answer:
        /// (* 2147483647 2147483647) used to be 1.
        ///
        /// The narrow cases compute in the next width up and only allocate a
        /// BigInteger when that overflows too, so ordinary arithmetic stays on the
        /// fixed-width path.
        /// Public so that primitives outside this module -- the rounding family and
        /// numerator/denominator -- return exact integers in the same narrowest form
        /// arithmetic produces, keeping results eqv? to the obvious literal.
        let ofBig (value: Numerics.BigInteger) : obj =
            if value >= Numerics.BigInteger(System.Int32.MinValue)
               && value <= Numerics.BigInteger(System.Int32.MaxValue) then box (int value)
            elif value >= Numerics.BigInteger(System.Int64.MinValue)
                 && value <= Numerics.BigInteger(System.Int64.MaxValue) then box (int64 value)
            else box value

        let private ofLong (value: int64) : obj =
            if value >= int64 System.Int32.MinValue && value <= int64 System.Int32.MaxValue then
                box (int value)
            else box value

        /// Byte arithmetic widens like the other exact integers rather than wrapping
        /// at 255, so (+ 200uy 100uy) is 300 and not 44.
        let private ofByteResult (value: int) : obj =
            if value >= 0 && value <= 255 then box (byte value) else box value

        /// A ratio whose denominator reduces to one collapses back to an integer, so
        /// (+ 1/2 1/2) is the integer 1 rather than 1/1. R-1RK 12.8.1 makes integer? a
        /// refinement of rational?, and keeping the narrowest exact type means later
        /// operations stay on the fixed-width path.
        let private ofExactRatio (ratio: ExactRatio) : obj =
            if ratio.Denominator.IsOne then ofBig ratio.Numerator else box ratio

        /// Public alongside ofBig, for primitives that produce exact results outside
        /// this module. The caller must have rejected a zero denominator.
        let ofRatio numerator denominator =
            ofExactRatio (makeExactRatio numerator denominator)

        let private longChecked operation (x: int64) (y: int64) fallback =
            try ofLong (operation x y) with :? System.OverflowException -> fallback ()

        let private addWidened = function
            | Bytes(x, y) -> ofByteResult (int x + int y)
            | Ints(x, y) -> ofLong (int64 x + int64 y)
            | Longs(x, y) ->
                longChecked (Microsoft.FSharp.Core.Operators.Checked.(+)) x y
                    (fun () -> ofBig (Numerics.BigInteger x + Numerics.BigInteger y))
            | Bigs(x, y) -> ofBig (x + y)
            | Ratios(x, y) ->
                ofRatio
                    (x.Numerator * y.Denominator + y.Numerator * x.Denominator)
                    (x.Denominator * y.Denominator)
            | Singles(x, y) -> box (x + y)
            | Doubles(x, y) -> box (x + y)
            | Complexes(x, y) -> ofComplex (x + y)

        let private subtractWidened = function
            | Bytes(x, y) -> ofByteResult (int x - int y)
            | Ints(x, y) -> ofLong (int64 x - int64 y)
            | Longs(x, y) ->
                longChecked (Microsoft.FSharp.Core.Operators.Checked.(-)) x y
                    (fun () -> ofBig (Numerics.BigInteger x - Numerics.BigInteger y))
            | Bigs(x, y) -> ofBig (x - y)
            | Ratios(x, y) ->
                ofRatio
                    (x.Numerator * y.Denominator - y.Numerator * x.Denominator)
                    (x.Denominator * y.Denominator)
            | Singles(x, y) -> box (x - y)
            | Doubles(x, y) -> box (x - y)
            | Complexes(x, y) -> ofComplex (x - y)

        let private multiplyWidened = function
            | Bytes(x, y) -> ofByteResult (int x * int y)
            | Ints(x, y) -> ofLong (int64 x * int64 y)
            | Longs(x, y) ->
                longChecked (Microsoft.FSharp.Core.Operators.Checked.(*)) x y
                    (fun () -> ofBig (Numerics.BigInteger x * Numerics.BigInteger y))
            | Bigs(x, y) -> ofBig (x * y)
            | Ratios(x, y) ->
                ofRatio (x.Numerator * y.Numerator) (x.Denominator * y.Denominator)
            | Singles(x, y) -> box (x * y)
            | Doubles(x, y) -> box (x * y)
            | Complexes(x, y) -> ofComplex (x * y)

        /// R-1RK 12.8.2 makes `/` ordinary division, not the truncating quotient, and
        /// 12.3.2 requires the result of dividing two exact integers to be exact: (/ 1 3)
        /// is an exact third, not zero and not the nearest double. Truncation is
        /// available separately as `div` (12.5.8).
        ///
        /// Each exact case keeps its fixed-width fast path for the even division that
        /// dominates real programs, and only builds a ratio when the division does not
        /// come out whole. Int32 divides in int64 and an int64 divisor of -1 is taken
        /// apart, because MinValue / -1 -- and the remainder that decides which path to
        /// take -- overflow rather than producing a result.
        let private divideWidened = function
            | Bytes(x, y) ->
                if x % y = 0uy then box (x / y)
                else ofRatio (Numerics.BigInteger(int x)) (Numerics.BigInteger(int y))
            | Ints(x, y) ->
                let x, y = int64 x, int64 y
                if x % y = 0L then ofLong (x / y)
                else ofRatio (Numerics.BigInteger x) (Numerics.BigInteger y)
            | Longs(x, y) ->
                if y = -1L then ofBig (-(Numerics.BigInteger x))
                elif x % y = 0L then ofLong (x / y)
                else ofRatio (Numerics.BigInteger x) (Numerics.BigInteger y)
            | Bigs(x, y) -> ofRatio x y
            | Ratios(x, y) ->
                ofRatio (x.Numerator * y.Denominator) (x.Denominator * y.Numerator)
            | Singles(x, y) -> box (x / y)
            | Doubles(x, y) -> box (x / y)
            | Complexes(x, y) -> ofComplex (x / y)

        let private lessThanWidened = function
            | Bytes(x, y) -> Some(x < y)
            | Ints(x, y) -> Some(x < y)
            | Longs(x, y) -> Some(x < y)
            | Singles(x, y) -> Some(x < y)
            | Bigs(x, y) -> Some(x < y)
            // Both denominators are positive by construction, so cross-multiplying
            // compares the ratios without leaving exact arithmetic.
            | Ratios(x, y) ->
                Some(x.Numerator * y.Denominator < y.Numerator * x.Denominator)
            | Doubles(x, y) -> Some(x < y)
            | Complexes _ -> None

        let private lessThanOrEqualWidened = function
            | Bytes(x, y) -> Some(x <= y)
            | Ints(x, y) -> Some(x <= y)
            | Longs(x, y) -> Some(x <= y)
            | Singles(x, y) -> Some(x <= y)
            | Bigs(x, y) -> Some(x <= y)
            | Ratios(x, y) ->
                Some(x.Numerator * y.Denominator <= y.Numerator * x.Denominator)
            | Doubles(x, y) -> Some(x <= y)
            | Complexes _ -> None

        /// Dispatches a binary operation when either operand is an exact infinity.
        /// `combine` gets the two signs when both are infinite, `mixed` gets the
        /// infinity's sign and the finite operand. Returns None when neither is
        /// infinite, leaving the caller on its ordinary path.
        let private withInfinities combine mixed (a: obj) (b: obj) : obj option option =
            match a, b with
            | (:? ExactInfinity as x), (:? ExactInfinity as y) ->
                Some(Some(combine (signOf x) (signOf y)))
            | (:? ExactInfinity as x), finite ->
                match finiteSign finite with
                // A NaN or complex operand has no sign to combine with; NaN already
                // means "no primary value", so the result has none either.
                | None -> Some(Some noPrimaryValue)
                | Some sign -> Some(mixed (signOf x) sign false finite)
            | finite, (:? ExactInfinity as y) ->
                match finiteSign finite with
                | None -> Some(Some noPrimaryValue)
                | Some sign -> Some(mixed (signOf y) sign true finite)
            | _ -> None


        /// Adding like infinities gives that infinity; adding opposite ones has no
        /// answer. An infinity plus any finite real is that infinity.
        let private addCombine x y = if x = y then box (infinityOfSign x) else noPrimaryValue
        let private addMixed infinite _ _ _ = Some(box (infinityOfSign infinite))

        // a - b with both infinite: opposite signs keep a's, like signs cancel.
        let private subtractCombine x y =
            if x = y then noPrimaryValue else box (infinityOfSign x)
        // finite - infinity flips the sign; infinity - finite keeps it.
        let private subtractMixed infinite _ finiteIsFirst _ =
            Some(box (infinityOfSign (if finiteIsFirst then -infinite else infinite)))

        /// Multiplying by an infinity keeps the sign product, except that zero times
        /// infinity has no answer: no finite multiple of zero is infinite.
        let private multiplyCombine x y = box (infinityOfSign (x * y))
        let private multiplyMixed infinite finite _ _ =
            if finite = 0 then Some noPrimaryValue
            else Some(box (infinityOfSign (infinite * finite)))

        /// The infinite cases are checked inline rather than by handing the finite path
        /// to a combinator: partially applying it allocated a closure on every
        /// arithmetic operation, which showed up as a tenth of the cost of a call.
        let inline private dispatchInfinities combine mixed (a: obj) (b: obj) onFinite =
            // Two type tests settle the common case. Sorting out *which* operand is
            // infinite costs more, and only runs when one of them actually is.
            if not (a :? ExactInfinity) && not (b :? ExactInfinity) then onFinite ()
            else
                match withInfinities combine mixed a b with
                | None -> onFinite ()
                | Some (Some result) -> returnM (Obj result)
                | Some None -> throwError (Default "division by zero")

        let opAdd a' b' =
            match a', b' with
            | Obj (:? DateTime as date), Obj b ->
                match b with
                | :? TimeSpan as span -> returnM (Obj(date + span))
                | _ -> throwError (ClrTypeMismatch("TimeSpan", b.GetType().Name))
            | Obj a, Obj b ->
                dispatchInfinities addCombine addMixed a b (fun () ->
                    numericBinaryOp addWidened a' b')
            | Obj _, found -> throwError (TypeMismatch("object", found))
            | found, _ -> throwError (TypeMismatch("object", found))

        let opMinus a' b' =
            match a', b' with
            | Obj (:? DateTime as date), Obj b ->
                match b with
                | :? DateTime as other -> returnM (Obj(date - other))
                | _ -> throwError (ClrTypeMismatch("DateTime", b.GetType().Name))
            | Obj a, Obj b ->
                dispatchInfinities subtractCombine subtractMixed a b (fun () ->
                    numericBinaryOp subtractWidened a' b')
            | Obj _, found -> throwError (TypeMismatch("object", found))
            | found, _ -> throwError (TypeMismatch("object", found))

        let opMultiply a' b' =
            match a', b' with
            | Obj a, Obj b ->
                dispatchInfinities multiplyCombine multiplyMixed a b (fun () ->
                    numericBinaryOp multiplyWidened a' b')
            | Obj _, found -> throwError (TypeMismatch("object", found))
            | found, _ -> throwError (TypeMismatch("object", found))

        let private divisorIsZero = function
            | Bytes(_, y) -> y = 0uy
            | Ints(_, y) -> y = 0
            | Longs(_, y) -> y = 0L
            | Bigs(_, y) -> y = Numerics.BigInteger.Zero
            | Ratios(_, y) -> y.Numerator.IsZero
            | Singles(_, y) -> y = 0.0f
            | Doubles(_, y) -> y = 0.0
            | Complexes(_, y) -> y = Numerics.Complex.Zero

        /// R-1RK 12.8.2: dividing by zero signals an error. The check is explicit
        /// because .NET disagrees with the report in both directions -- integer
        /// division throws, and floating-point division quietly yields an infinity,
        /// which the report rejects because the limit depends on the direction zero
        /// is approached from.
        /// Division is the one arithmetic operation the CLR can still raise from once a
        /// zero divisor is excluded: Int32.MinValue / -1 has no representable result.
        /// An escaping exception would fault the process, so this path keeps a handler.
        let private guardedDivide widened =
            try Choice2Of2(divideWidened widened)
            with ex -> Choice1Of2 ex

        /// Infinity over infinity has no answer. An infinity over a finite real is an
        /// infinity of the sign product, except over zero, which R-1RK 12.8.2 makes an
        /// error like any other division by zero. A finite real over an infinity is
        /// exact zero -- the one case where an infinite operand gives a finite result.
        let private divideCombine _ _ = noPrimaryValue
        let private divideMixed infinite finite finiteIsFirst _ =
            if finiteIsFirst then Some(box 0)
            elif finite = 0 then None
            else Some(box (infinityOfSign (infinite * finite)))

        let private opDivideFinite a' b' =
            match a', b' with
            | Obj a, Obj b ->
                match widen a b with
                | Choice2Of2 widened when divisorIsZero widened ->
                    throwError (Default "division by zero")
                | Choice2Of2 widened ->
                    match guardedDivide widened with
                    | Choice2Of2 result -> returnM (Obj result)
                    | Choice1Of2 ex -> throwError (ClrException ex)
                | Choice1Of2 FirstOperand ->
                    throwError (ClrTypeMismatch("number", a.GetType().Name))
                | Choice1Of2 SecondOperand ->
                    throwError (ClrTypeMismatch(rankName (rankOf a), b.GetType().Name))
            | Obj _, found -> throwError (TypeMismatch("object", found))
            | found, _ -> throwError (TypeMismatch("object", found))

        let opDivide a' b' =
            match a', b' with
            | Obj a, Obj b ->
                dispatchInfinities divideCombine divideMixed a b (fun () ->
                    opDivideFinite a' b')
            | Obj _, found -> throwError (TypeMismatch("object", found))
            | found, _ -> throwError (TypeMismatch("object", found))

        /// R-1RK 12.5.8, as its own operation rather than something derived from `/`.
        /// `/` is ordinary division (12.8.2) and no longer truncates, and `div` belongs
        /// to the required Numbers module, which may not depend on the optional
        /// Rational module that supplies `truncate`. The remainder satisfies
        /// 0 <= mod < |divisor| for either sign of divisor.
        let private divAndModWidened widened =
            let adjust (q: float) (r: float) (y: float) =
                if r < 0.0 then (if y > 0.0 then (q - 1.0, r + y) else (q + 1.0, r - y))
                else (q, r)
            match widened with
            | Bytes(x, y) ->
                let q = x / y
                box (int q), box (int (x - y * q))
            | Ints(x, y) ->
                let q0 = x / y
                let r0 = x - y * q0
                let q, r = if r0 < 0 then (if y > 0 then (q0 - 1, r0 + y) else (q0 + 1, r0 - y)) else (q0, r0)
                box q, box r
            | Longs(x, y) ->
                let q0 = x / y
                let r0 = x - y * q0
                let q, r = if r0 < 0L then (if y > 0L then (q0 - 1L, r0 + y) else (q0 + 1L, r0 - y)) else (q0, r0)
                box q, box r
            | Bigs(x, y) ->
                let q0 = Numerics.BigInteger.Divide(x, y)
                let r0 = x - y * q0
                let q, r =
                    if r0.Sign < 0 then
                        if y.Sign > 0 then (q0 - Numerics.BigInteger.One, r0 + y)
                        else (q0 + Numerics.BigInteger.One, r0 - y)
                    else (q0, r0)
                ofBig q, ofBig r
            | Ratios(x, y) ->
                // x/y as a single fraction gives the truncated quotient; the remainder
                // is then nudged into 0 <= mod < |divisor| exactly as the integers are.
                let subtractMultiple (k: Numerics.BigInteger) =
                    makeExactRatio
                        (x.Numerator * y.Denominator - y.Numerator * k * x.Denominator)
                        (x.Denominator * y.Denominator)
                let q0 =
                    Numerics.BigInteger.Divide(
                        x.Numerator * y.Denominator, x.Denominator * y.Numerator)
                let r0 = subtractMultiple q0
                let q =
                    if r0.Numerator.Sign >= 0 then q0
                    elif y.Numerator.Sign > 0 then q0 - Numerics.BigInteger.One
                    else q0 + Numerics.BigInteger.One
                ofBig q, ofExactRatio (subtractMultiple q)
            | Singles(x, y) ->
                let q0 = System.Math.Truncate(float x / float y)
                let q, r = adjust q0 (float x - float y * q0) (float y)
                box (float32 q), box (float32 r)
            | Doubles(x, y) ->
                let q0 = System.Math.Truncate(x / y)
                let q, r = adjust q0 (x - y * q0) y
                box q, box r
            | Complexes _ ->
                // Unreachable: opDivAndMod rejects complex operands before widening
                // reaches here. R-1RK 12.5.8 defines div and mod on reals.
                failwith "div and mod are defined on reals"

        let private isComplexWidened = function
            | Complexes _ -> true
            | _ -> false

        let opDivAndMod a' b' =
            match a', b' with
            | Obj a, Obj b ->
                match widen a b with
                | Choice2Of2 widened when isComplexWidened widened ->
                    throwError (Default "div and mod are defined on reals")
                | Choice2Of2 widened when divisorIsZero widened ->
                    throwError (Default "division by zero")
                | Choice2Of2 widened ->
                    let quotient, remainder = divAndModWidened widened
                    returnM (Obj quotient, Obj remainder)
                | Choice1Of2 FirstOperand ->
                    throwError (ClrTypeMismatch("number", a.GetType().Name))
                | Choice1Of2 SecondOperand ->
                    throwError (ClrTypeMismatch(rankName (rankOf a), b.GetType().Name))
            | Obj _, found -> throwError (TypeMismatch("object", found))
            | found, _ -> throwError (TypeMismatch("object", found))

        /// Every finite real lies strictly between the two infinities, and each
        /// infinity is equal to itself. A NaN operand has no primary value, so R-1RK
        /// 12.2 makes ordering it an error rather than a guess -- the same rule that
        /// already rejects ordering a complex.
        let private compareWithInfinity strict (a: obj) (b: obj) =
            match a, b with
            | (:? ExactInfinity as x), (:? ExactInfinity as y) ->
                Some(if strict then signOf x < signOf y else signOf x <= signOf y)
            | (:? ExactInfinity as x), finite ->
                match finiteSign finite with
                | None -> None
                | Some _ -> Some(signOf x < 0)
            | finite, (:? ExactInfinity as y) ->
                match finiteSign finite with
                | None -> None
                | Some _ -> Some(signOf y > 0)
            | _ -> None

        let private comparisonWithInfinities strict finite (a': LispVal) (b': LispVal) =
            match a', b' with
            | Obj ((:? ExactInfinity) as a), Obj b
            | Obj a, Obj ((:? ExactInfinity) as b) ->
                match compareWithInfinity strict a b with
                | Some result -> returnM (Bool result)
                | None -> throwError (Default "a number with no primary value is not ordered")
            | _ -> finite a' b'

        let opLessThan a' b' =
            comparisonWithInfinities true (comparisonBinaryOp lessThanWidened) a' b'

        let opLessThanOrEqual a' b' =
            comparisonWithInfinities false (comparisonBinaryOp lessThanOrEqualWidened) a' b'
        let opGreaterThan a b = opLessThan b a
        let opGreaterThanOrEqual a b = opLessThanOrEqual b a
