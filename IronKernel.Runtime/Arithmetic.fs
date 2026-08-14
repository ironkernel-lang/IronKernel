namespace IronKernel

    open Ast
    open Choice
    open Errors
    open System

    module Arithmetic =

        /// Operand pair widened to a common numeric representation.
        /// Promotion rank: byte < int32 < int64 < float32 < double, except that
        /// int64 paired with float32 widens to double, because float32 cannot
        /// represent every int64.
        type private Widened =
            | Bytes of byte * byte
            | Ints of int32 * int32
            | Longs of int64 * int64
            | Singles of float32 * float32
            | Doubles of double * double

        type private BadOperand =
            | FirstOperand
            | SecondOperand

        let private rankOf (value: obj) =
            match value with
            | :? byte -> 0
            | :? int32 -> 1
            | :? int64 -> 2
            | :? float32 -> 3
            | :? double -> 4
            | _ -> -1

        let private rankName = function
            | 0 -> "byte"
            | 1 -> "int32"
            | 2 -> "int64"
            | 3 -> "float32"
            | _ -> "float"

        let private toInt (value: obj) =
            match value with
            | :? byte as v -> int v
            | _ -> value :?> int

        let private toLong (value: obj) =
            match value with
            | :? byte as v -> int64 v
            | :? int32 as v -> int64 v
            | _ -> value :?> int64

        let private toSingle (value: obj) =
            match value with
            | :? byte as v -> float32 v
            | :? int32 as v -> float32 v
            | _ -> value :?> float32

        let private toDouble (value: obj) =
            match value with
            | :? byte as v -> double v
            | :? int32 as v -> double v
            | :? int64 as v -> double v
            | :? float32 as v -> double v
            | _ -> value :?> double

        let private widen (a: obj) (b: obj) =
            let rankA = rankOf a
            let rankB = rankOf b
            if rankA < 0 then Choice1Of2 FirstOperand
            elif rankB < 0 then Choice1Of2 SecondOperand
            else
                let target =
                    if min rankA rankB = 2 && max rankA rankB = 3 then 4
                    else max rankA rankB
                Choice2Of2(
                    match target with
                    | 0 -> Bytes(a :?> byte, b :?> byte)
                    | 1 -> Ints(toInt a, toInt b)
                    | 2 -> Longs(toLong a, toLong b)
                    | 3 -> Singles(toSingle a, toSingle b)
                    | _ -> Doubles(toDouble a, toDouble b))

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

        let private comparisonBinaryOp apply (a': LispVal) (b': LispVal) =
            match a', b' with
            | Obj a, Obj b ->
                match widen a b with
                | Choice2Of2 widened -> returnM (Bool(apply widened))
                | Choice1Of2 FirstOperand ->
                    throwError (TypeMismatch(b.GetType().Name, Obj a))
                | Choice1Of2 SecondOperand ->
                    throwError (TypeMismatch(a.GetType().Name, Obj b))
            | Obj _, found -> throwError (TypeMismatch("object", found))
            | found, _ -> throwError (TypeMismatch("object", found))

        let private addWidened = function
            | Bytes(x, y) -> box (x + y)
            | Ints(x, y) -> box (x + y)
            | Longs(x, y) -> box (x + y)
            | Singles(x, y) -> box (x + y)
            | Doubles(x, y) -> box (x + y)

        let private subtractWidened = function
            | Bytes(x, y) -> box (x - y)
            | Ints(x, y) -> box (x - y)
            | Longs(x, y) -> box (x - y)
            | Singles(x, y) -> box (x - y)
            | Doubles(x, y) -> box (x - y)

        let private multiplyWidened = function
            | Bytes(x, y) -> box (x * y)
            | Ints(x, y) -> box (x * y)
            | Longs(x, y) -> box (x * y)
            | Singles(x, y) -> box (x * y)
            | Doubles(x, y) -> box (x * y)

        let private divideWidened = function
            | Bytes(x, y) -> box (x / y)
            | Ints(x, y) -> box (x / y)
            | Longs(x, y) -> box (x / y)
            | Singles(x, y) -> box (x / y)
            | Doubles(x, y) -> box (x / y)

        let private lessThanWidened = function
            | Bytes(x, y) -> x < y
            | Ints(x, y) -> x < y
            | Longs(x, y) -> x < y
            | Singles(x, y) -> x < y
            | Doubles(x, y) -> x < y

        let private lessThanOrEqualWidened = function
            | Bytes(x, y) -> x <= y
            | Ints(x, y) -> x <= y
            | Longs(x, y) -> x <= y
            | Singles(x, y) -> x <= y
            | Doubles(x, y) -> x <= y

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
        let opDivide a' b' = numericBinaryOp divideWidened a' b'

        let opLessThan a' b' = comparisonBinaryOp lessThanWidened a' b'
        let opLessThanOrEqual a' b' = comparisonBinaryOp lessThanOrEqualWidened a' b'
        let opGreaterThan a b = opLessThan b a
        let opGreaterThanOrEqual a b = opLessThanOrEqual b a
