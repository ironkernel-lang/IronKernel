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
            | :? float32 -> 4
            | :? double -> 5
            | :? Numerics.Complex -> 6
            | _ -> -1

        let private rankName = function
            | 0 -> "byte"
            | 1 -> "int32"
            | 2 -> "int64"
            | 3 -> "integer"
            | 4 -> "float32"
            | 5 -> "float"
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

        let private toSingle (value: obj) =
            match value with
            | :? byte as v -> float32 v
            | :? int32 as v -> float32 v
            | :? int64 as v -> float32 v
            | :? Numerics.BigInteger as v -> float32 v
            | _ -> value :?> float32

        let private toDouble (value: obj) =
            match value with
            | :? byte as v -> double v
            | :? int32 as v -> double v
            | :? int64 as v -> double v
            | :? Numerics.BigInteger as v -> double v
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
                    // float32 cannot represent every int64 or big integer, so pairing
                    // one with an exact integer wider than its mantissa widens to double.
                    if min rankA rankB >= 2 && min rankA rankB <= 3 && max rankA rankB = 4 then 5
                    else max rankA rankB
                Choice2Of2(
                    match target with
                    | 0 -> Bytes(a :?> byte, b :?> byte)
                    | 1 -> Ints(toInt a, toInt b)
                    | 2 -> Longs(toLong a, toLong b)
                    | 3 -> Bigs(toBig a, toBig b)
                    | 4 -> Singles(toSingle a, toSingle b)
                    | 5 -> Doubles(toDouble a, toDouble b)
                    | _ -> Complexes(toComplex a, toComplex b))

        /// No exception handler and no validation hook on this path. F# addition,
        /// subtraction and multiplication are unchecked and wrap rather than raise, so
        /// a handler would guard against nothing while sitting on the hottest operation
        /// in the language; division is the only arithmetic that can raise, and it is
        /// implemented separately below with its own checks.
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
        let private ofBig (value: Numerics.BigInteger) : obj =
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

        let private longChecked operation (x: int64) (y: int64) fallback =
            try ofLong (operation x y) with :? System.OverflowException -> fallback ()

        let private addWidened = function
            | Bytes(x, y) -> ofByteResult (int x + int y)
            | Ints(x, y) -> ofLong (int64 x + int64 y)
            | Longs(x, y) ->
                longChecked (Microsoft.FSharp.Core.Operators.Checked.(+)) x y
                    (fun () -> ofBig (Numerics.BigInteger x + Numerics.BigInteger y))
            | Bigs(x, y) -> ofBig (x + y)
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
            | Singles(x, y) -> box (x * y)
            | Doubles(x, y) -> box (x * y)
            | Complexes(x, y) -> ofComplex (x * y)

        /// Integer division only stays integral when it divides evenly. R-1RK 12.8.2
        /// makes `/` ordinary division, not the truncating quotient: (/ 1 3) is a third,
        /// not zero. Truncation is available as `div` (12.5.8), which is a separate
        /// feature. Without an exact rational type the inexact quotient is the closest
        /// available result; recorded as a divergence.
        let private divideWidened = function
            | Bytes(x, y) -> if x % y = 0uy then box (x / y) else box (float x / float y)
            | Ints(x, y) -> if x % y = 0 then box (x / y) else box (float x / float y)
            | Longs(x, y) -> if x % y = 0L then ofLong (x / y) else box (float x / float y)
            | Bigs(x, y) ->
                if Numerics.BigInteger.Remainder(x, y) = Numerics.BigInteger.Zero then
                    ofBig (Numerics.BigInteger.Divide(x, y))
                else box (double x / double y)
            | Singles(x, y) -> box (x / y)
            | Doubles(x, y) -> box (x / y)
            | Complexes(x, y) -> ofComplex (x / y)

        let private lessThanWidened = function
            | Bytes(x, y) -> Some(x < y)
            | Ints(x, y) -> Some(x < y)
            | Longs(x, y) -> Some(x < y)
            | Singles(x, y) -> Some(x < y)
            | Bigs(x, y) -> Some(x < y)
            | Doubles(x, y) -> Some(x < y)
            | Complexes _ -> None

        let private lessThanOrEqualWidened = function
            | Bytes(x, y) -> Some(x <= y)
            | Ints(x, y) -> Some(x <= y)
            | Longs(x, y) -> Some(x <= y)
            | Singles(x, y) -> Some(x <= y)
            | Bigs(x, y) -> Some(x <= y)
            | Doubles(x, y) -> Some(x <= y)
            | Complexes _ -> None

        let opAdd a' b' =
            match a', b' with
            | Obj (:? DateTime as date), Obj b ->
                match b with
                | :? TimeSpan as span -> returnM (Obj(date + span))
                | _ -> throwError (ClrTypeMismatch("TimeSpan", b.GetType().Name))
            | _ -> numericBinaryOp addWidened a' b'

        let opMinus a' b' =
            match a', b' with
            | Obj (:? DateTime as date), Obj b ->
                match b with
                | :? DateTime as other -> returnM (Obj(date - other))
                | _ -> throwError (ClrTypeMismatch("DateTime", b.GetType().Name))
            | _ -> numericBinaryOp subtractWidened a' b'

        let opMultiply a' b' = numericBinaryOp multiplyWidened a' b'

        let private divisorIsZero = function
            | Bytes(_, y) -> y = 0uy
            | Ints(_, y) -> y = 0
            | Longs(_, y) -> y = 0L
            | Bigs(_, y) -> y = Numerics.BigInteger.Zero
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

        let opDivide a' b' =
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

        let opLessThan a' b' = comparisonBinaryOp lessThanWidened a' b'
        let opLessThanOrEqual a' b' = comparisonBinaryOp lessThanOrEqualWidened a' b'
        let opGreaterThan a b = opLessThan b a
        let opGreaterThanOrEqual a b = opLessThanOrEqual b a
