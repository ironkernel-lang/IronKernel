namespace IronKernel

module Errors =
    
    open Ast
    open System

    let throwError error = Choice1Of2(error)
    let succeed p = Choice2Of2(p)

    let catchError action (f: LispError -> ThrowsError<LispVal>) = 
        match action with
        |Choice1Of2(error) -> f error
        |Choice2Of2(result) -> action

    let showError error =
        let mutable current = error
        let mutable locations = []
        let mutable collecting = true

        while collecting do
            match current with
            | LocatedError(span, sourceLine, inner) ->
                locations <- (span, sourceLine) :: locations
                current <- inner
            | _ -> collecting <- false

        let message =
            match current with
            | UnboundVar(msg,varname) -> msg + ": '" + varname + "' "
            | BadSpecialForm(msg,form) -> msg + ": " + showVal form
            | NotFunction(msg,func) -> msg + ": " + func
            | NumArgs(expected,found) -> "Expected " + expected.ToString()  + " args, found values " + unwordsList found
            | TypeMismatch(expected,found) -> "Invalid type: expected " + expected  + ", found " + showVal found
            | ClrTypeMismatch(expected,found) -> "Invalid type: expected " + expected  + ", found " + found
            | Parser(parseError) -> "Parse error: " + parseError
            | Default(msg) -> msg
            | ClrException ex -> ex.Message
            | CapabilityDenied text -> "Capability denied: " + text
            | ContractViolation text -> "Contract violation: " + text
            | LocatedError _ -> invalidOp "Located error traversal is incomplete"

        let output = Text.StringBuilder()
        for span, _ in List.rev locations do
            let source =
                if String.IsNullOrWhiteSpace span.sourceName then "<input>"
                else span.sourceName
            let position = span.startPosition
            output.AppendFormat("{0}:{1}:{2}: ", source, position.line, position.column) |> ignore

        output.Append(message) |> ignore
        for span, sourceLine in locations do
            let position = span.startPosition
            match sourceLine with
            | None -> ()
            | Some line ->
                let indent = String(' ', max 0 (int position.column - 1))
                let requestedWidth =
                    if span.endPosition.line = position.line then
                        int (span.endPosition.column - position.column)
                    else 1
                let availableWidth = max 1 (line.Length - indent.Length)
                let width = min availableWidth (max 1 requestedWidth)
                output
                    .Append(Environment.NewLine)
                    .Append(line)
                    .Append(Environment.NewLine)
                    .Append(indent)
                    .Append(String('^', width))
                |> ignore
        output.ToString()

    let trapError (action:ThrowsError<LispVal>) : ThrowsError<LispVal> = 
        catchError action (fun x -> succeed (Ast.Status(showError x)))
    
    let extractValue : ThrowsError<LispVal> -> LispVal = function
        | Choice2Of2 value -> value
        | Choice1Of2 error -> Status(showError error)

    let rec sequence lst result =
        match lst with
        |[] -> succeed (result |> List.rev)
        |Choice2Of2(p)::tail -> sequence tail (p::result)
        |Choice1Of2(p)::_    -> throwError p 

    let mapM f a = sequence (List.map f a)

    let bind p rest =
        match p with
            | Choice1Of2 r  -> rest r
            | Choice2Of2 e -> p

    let (>>=) a b = fun x -> bind (a x) b


