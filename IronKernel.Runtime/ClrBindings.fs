namespace IronKernel

module ClrBindings =

    open Ast
    open Choice
    open Errors
    open Eval
    open Capabilities

    type ClrParameterType =
        | ClrString
        | ClrBoolean
        | ClrInt32
        | ClrDouble

    let private convert expected value =
        match expected, value with
        | ClrString, Obj (:? string as result) -> returnM (result :> obj)
        | ClrBoolean, Bool result -> returnM (result :> obj)
        | ClrInt32, Obj (:? int as result) -> returnM (result :> obj)
        | ClrDouble, Obj (:? double as result) -> returnM (result :> obj)
        | ClrDouble, Obj (:? int as result) -> returnM (float result :> obj)
        | ClrString, found -> throwError (TypeMismatch("string", found))
        | ClrBoolean, found -> throwError (TypeMismatch("boolean", found))
        | ClrInt32, found -> throwError (TypeMismatch("int32", found))
        | ClrDouble, found -> throwError (TypeMismatch("double", found))

    let convertArguments
        (expected: ClrParameterType list)
        (args: LispVal list)
        : ThrowsError<obj list> =
        if List.length expected <> List.length args then
            throwError (NumArgs(List.length expected, args))
        else
            List.zip expected args
            |> List.map (fun (parameterType, value) -> convert parameterType value)
            |> fun conversions -> sequence conversions []

    let requireGenerated manifestId env =
        if has (GeneratedClr manifestId) env then returnM ()
        else throwError (CapabilityDenied("generated CLR binding set '" + manifestId + "'"))

    let returnObject env cont (value: obj) =
        bounceContinue env cont (if isNull value then Inert else Obj value)
