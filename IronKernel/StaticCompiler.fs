namespace IronKernel

/// Generates ordinary F# source for persisted managed artifacts.
/// Unsupported dynamic forms fail during artifact construction instead of
/// silently embedding source for parsing or expression compilation at startup.
module StaticCompiler =

    open System
    open System.Globalization
    open System.Text
    open Ast
    open Ir

    let private stringLiteralOptions =
        let options = Text.Json.JsonSerializerOptions()
        options.Encoder <- Text.Encodings.Web.JavaScriptEncoder.UnsafeRelaxedJsonEscaping
        options

    let private quote (value: string) = Text.Json.JsonSerializer.Serialize(value, stringLiteralOptions)

    let private doubleLiteral (value: double) =
        if Double.IsNaN value then "System.Double.NaN"
        elif Double.IsPositiveInfinity value then "System.Double.PositiveInfinity"
        elif Double.IsNegativeInfinity value then "System.Double.NegativeInfinity"
        else
            let literal = value.ToString("R", CultureInfo.InvariantCulture)
            if literal.Contains('.') then literal
            else
                let exponentIndex = literal.IndexOfAny([|'E'; 'e'|])
                if exponentIndex >= 0 then literal.Insert(exponentIndex, ".0")
                else literal + ".0"

    let private sequenceOptions values =
        let mutable result = Some []
        for value in List.rev values do
            match value, result with
            | Some item, Some items -> result <- Some(item :: items)
            | _ -> result <- None
        result

    let rec private emitValue = function
        | Atom value -> Some("Atom " + quote value)
        | List values ->
            values
            |> List.map emitValue
            |> sequenceOptions
            |> Option.map (fun emitted -> "List [" + String.concat "; " emitted + "]")
        | DottedList(head, tail) ->
            match head |> List.map emitValue |> sequenceOptions, emitValue tail with
            | Some emittedHead, Some emittedTail ->
                Some("DottedList([" + String.concat "; " emittedHead + "], " + emittedTail + ")")
            | _ -> None
        | Bool value -> Some(if value then "Bool true" else "Bool false")
        | Inert -> Some "Inert"
        | Nil -> Some "Nil"
        | Keyword value -> Some("Keyword " + quote value)
        | Obj null -> Some "Obj null"
        | Obj (:? string as value) -> Some("Obj(box " + quote value + ")")
        | Obj (:? byte as value) -> Some(sprintf "Obj(box %uy)" value)
        | Obj (:? int as value) -> Some(sprintf "Obj(box %d)" value)
        | Obj (:? int64 as value) -> Some(sprintf "Obj(box %dL)" value)
        // Exact numbers wider than the fixed-width types are rebuilt from their decimal
        // text, which is exact for both and avoids depending on a literal syntax.
        | Obj (:? System.Numerics.BigInteger as value) ->
            Some("Obj(box (System.Numerics.BigInteger.Parse " + quote (string value) + "))")
        | Obj (:? ExactRatio as value) ->
            Some(
                "Obj(box (makeExactRatio (System.Numerics.BigInteger.Parse "
                + quote (string value.Numerator) + ") (System.Numerics.BigInteger.Parse "
                + quote (string value.Denominator) + ")))")
        | Obj (:? float32 as value) ->
            Some("Obj(box " + value.ToString("R", CultureInfo.InvariantCulture) + "f)")
        | Obj (:? double as value) ->
            Some("Obj(box " + doubleLiteral value + ")")
        | Vector values ->
            values
            |> Array.map emitValue
            |> Array.toList
            |> sequenceOptions
            |> Option.map (fun emitted -> "Vector [|" + String.concat "; " emitted + "|]")
        | _ -> None

    let private emitPosition position =
        sprintf
            "{ offset = %dL; line = %dL; column = %dL }"
            position.offset
            position.line
            position.column

    let private emitSpan span =
        "{ sourceName = " + quote span.sourceName
        + "; startPosition = " + emitPosition span.startPosition
        + "; endPosition = " + emitPosition span.endPosition + " }"

    let private emitSourceLine = function
        | Some line -> "(Some " + quote line + ")"
        | None -> "None"

    let private emitExpression expression =
        let generated body = "GeneratedFunc(fun env cont -> " + body + ")"
        let rec namedOperator = function
            | CVar name -> Some name
            | CLocated(_, _, inner) -> namedOperator inner
            | _ -> None
        let rec emit = function
            | CLit value
            | CQuote value ->
                emitValue value
                |> Option.map (fun emitted -> generated ("bounceContinue env cont (" + emitted + ")"))
            | CVar name ->
                Some(
                    generated(
                    "match getVar env " + quote name
                    + " with | Choice1Of2 error -> Done(throwError error)"
                    + " | Choice2Of2 value -> bounceContinue env cont value"))
            | COperate(operator, operands) ->
                match operands |> List.map emitValue |> sequenceOptions with
                | Some emitted ->
                    match namedOperator operator with
                    | Some name ->
                        Some(
                        generated(
                            "appNamed env cont " + quote name + " [|"
                            + String.concat "; " emitted + "|]"))
                    | None ->
                        emit operator
                        |> Option.map (fun operatorFunc ->
                            generated(
                                "runOperate env cont (" + operatorFunc + ") [|"
                                + String.concat "; " emitted + "|]"))
                | None -> None
            | CIf(condition, consequent, alternative) ->
                match emit condition, emit consequent, emit alternative with
                | Some conditionFunc, Some consequentFunc, Some alternativeFunc ->
                    Some(
                        generated(
                            "runIf env cont (" + conditionFunc + ") ("
                            + consequentFunc + ") (" + alternativeFunc + ")"))
                | _ -> None
            | CDefine(CVar name, rhs) ->
                emit rhs
                |> Option.map (fun rhsFunc ->
                    generated("runDefine env cont " + quote name + " (" + rhsFunc + ")"))
            | CSeq expressions ->
                expressions
                |> List.map emit
                |> sequenceOptions
                |> Option.map (fun forms ->
                    generated("runSequence env cont [|" + String.concat "; " forms + "|]"))
            | CGuarded(guard, specialized, fallback) ->
                match emit specialized, emit fallback with
                | Some specializedFunc, Some fallbackFunc ->
                    let identity =
                        match guard.expectedIdentity with
                        | PrimitiveIf -> "PrimitiveIf"
                        | PrimitiveDefine -> "PrimitiveDefine"
                    Some(
                        generated(
                            "runGuard env cont " + quote guard.name + " " + identity
                            + " (" + specializedFunc + ") (" + fallbackFunc + ")"))
                | _ -> None
            | CIntrinsicOperate(PrimitiveIf, operands) ->
                operands
                |> List.map emitValue
                |> sequenceOptions
                |> Option.map (fun values ->
                    generated("if_then_else env cont [" + String.concat "; " values + "]") )
            | CIntrinsicOperate(PrimitiveDefine, operands) ->
                operands
                |> List.map emitValue
                |> sequenceOptions
                |> Option.map (fun values ->
                    generated("define env cont [" + String.concat "; " values + "]") )
            | CLocated(span, sourceLine, inner) ->
                emit inner
                |> Option.map (fun innerFunc ->
                    generated(
                        "runLocated env cont (" + emitSpan span + ") "
                        + emitSourceLine sourceLine + " (" + innerFunc + ")"))
            | _ -> None
        emit expression

    let generateProgram profile expressions =
        let emitted = expressions |> List.map emitExpression
        if emitted |> List.exists Option.isNone then
            Error "The program contains a form or constant unsupported by the static backend"
        else
            let forms = emitted |> List.choose id
            let profileName =
                match profile with
                | Minimal -> "Minimal"
                | Safe -> "Safe"
                | Unrestricted -> "Unrestricted"
            let output = StringBuilder()
            output.AppendLine("open System") |> ignore
            output.AppendLine("open IronKernel.Ast") |> ignore
            output.AppendLine("open IronKernel.Choice") |> ignore
            output.AppendLine("open IronKernel.Errors") |> ignore
            output.AppendLine("open IronKernel.Eval") |> ignore
            output.AppendLine("open IronKernel.Runtime") |> ignore
            output.AppendLine("open IronKernel.RuntimeDispatch") |> ignore
            output.AppendLine("open IronKernel.SymbolTable") |> ignore
            output.AppendLine() |> ignore
            for index, body in List.indexed forms do
                output.Append("let private form").Append(index).Append(" = ").AppendLine(body) |> ignore
            output.AppendLine("[<EntryPoint>]") |> ignore
            output.AppendLine("let main _ =") |> ignore
            output.Append("    let env = makePrimitiveBindingsForProfile ").AppendLine(profileName) |> ignore
            output.AppendLine("    let cont = newContinuation env") |> ignore
            output.AppendLine("    let forms = [|") |> ignore
            for index in 0 .. forms.Length - 1 do
                output.Append("        form").Append(index).AppendLine() |> ignore
            output.AppendLine("    |]") |> ignore
            output.AppendLine("    let mutable result = returnM Inert") |> ignore
            output.AppendLine("    let mutable index = 0") |> ignore
            output.AppendLine("    let mutable running = true") |> ignore
            output.AppendLine("    while index < forms.Length && running do") |> ignore
            output.AppendLine("        result <- run (forms.[index].Invoke(env, cont))") |> ignore
            output.AppendLine("        running <- match result with Choice2Of2 _ -> true | Choice1Of2 _ -> false") |> ignore
            output.AppendLine("        index <- index + 1") |> ignore
            output.AppendLine("    match result with") |> ignore
            output.AppendLine("    | Choice1Of2 error ->") |> ignore
            output.AppendLine("        eprintfn \"%s\" (showError error)") |> ignore
            output.AppendLine("        1") |> ignore
            output.AppendLine("    | Choice2Of2 Inert -> 0") |> ignore
            output.AppendLine("    | Choice2Of2 value ->") |> ignore
            output.AppendLine("        printfn \"%s\" (showVal value)") |> ignore
            output.AppendLine("        0") |> ignore
            Ok(output.ToString())