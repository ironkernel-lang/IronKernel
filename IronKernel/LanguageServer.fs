namespace IronKernel

/// `ik lsp`: a Language Server Protocol server over stdio, in-process with the
/// runtime (ADR 0009 phase 3). Diagnostics reuse the `check` pipeline on the
/// live buffer; completion and hover come from a bootstrapped environment,
/// contracts, and the phase-2 enumeration; semantic tokens classify operatives
/// and applicatives by resolving the binding, which no lexical grammar can do.
///
/// The protocol layer is deliberately a hand-rolled subset -- framing, JSON-RPC
/// dispatch, and the handful of requests the features need -- so the server
/// stays dependency-free and testable against in-memory streams.
module LanguageServer =

    open System
    open System.Collections.Generic
    open System.IO
    open System.Text
    open System.Text.Json
    open Ast
    open Errors

    // ---- Framing ----------------------------------------------------------

    let private readFramed (input: Stream) : JsonDocument option =
        let readLine () =
            let builder = StringBuilder()
            let mutable eof = false
            let mutable finished = false
            while not finished do
                match input.ReadByte() with
                | -1 ->
                    eof <- true
                    finished <- true
                | 10 -> finished <- true
                | 13 -> ()
                | b -> builder.Append(char b) |> ignore
            if eof && builder.Length = 0 then None else Some(builder.ToString())
        let mutable contentLength = -1
        let rec readHeaders () =
            match readLine () with
            | None -> false
            | Some "" -> true
            | Some line ->
                if line.StartsWith("Content-Length:", StringComparison.OrdinalIgnoreCase) then
                    match Int32.TryParse(line.Substring("Content-Length:".Length).Trim()) with
                    | true, length -> contentLength <- length
                    | _ -> ()
                readHeaders ()
        if not (readHeaders ()) || contentLength < 0 then None
        else
            let buffer = Array.zeroCreate contentLength
            let mutable filled = 0
            let mutable ok = true
            while ok && filled < contentLength do
                let count = input.Read(buffer, filled, contentLength - filled)
                if count <= 0 then ok <- false else filled <- filled + count
            if ok then Some(JsonDocument.Parse(ReadOnlyMemory buffer)) else None

    let private writeFramed (output: Stream) (json: string) =
        let bytes = Encoding.UTF8.GetBytes json
        let header = Encoding.ASCII.GetBytes(sprintf "Content-Length: %d\r\n\r\n" bytes.Length)
        output.Write(header, 0, header.Length)
        output.Write(bytes, 0, bytes.Length)
        output.Flush()

    let private toJson (write: Utf8JsonWriter -> unit) =
        use stream = new MemoryStream()
        use writer = new Utf8JsonWriter(stream)
        write writer
        writer.Flush()
        Encoding.UTF8.GetString(stream.ToArray())

    let private respond output (id: JsonElement) (writeResult: Utf8JsonWriter -> unit) =
        toJson (fun writer ->
            writer.WriteStartObject()
            writer.WriteString("jsonrpc", "2.0")
            writer.WritePropertyName "id"
            id.WriteTo writer
            writer.WritePropertyName "result"
            writeResult writer
            writer.WriteEndObject())
        |> writeFramed output

    let private respondError output (id: JsonElement) code (message: string) =
        toJson (fun writer ->
            writer.WriteStartObject()
            writer.WriteString("jsonrpc", "2.0")
            writer.WritePropertyName "id"
            id.WriteTo writer
            writer.WritePropertyName "error"
            writer.WriteStartObject()
            writer.WriteNumber("code", (code: int))
            writer.WriteString("message", message)
            writer.WriteEndObject()
            writer.WriteEndObject())
        |> writeFramed output

    let private notify output (method: string) (writeParams: Utf8JsonWriter -> unit) =
        toJson (fun writer ->
            writer.WriteStartObject()
            writer.WriteString("jsonrpc", "2.0")
            writer.WriteString("method", method)
            writer.WritePropertyName "params"
            writeParams writer
            writer.WriteEndObject())
        |> writeFramed output

    // ---- Positions --------------------------------------------------------

    /// LSP positions are 0-based line/character; runtime spans are 1-based.
    let private writePosition (writer: Utf8JsonWriter) (position: SourcePosition) =
        writer.WriteStartObject()
        writer.WriteNumber("line", max 0L (position.line - 1L))
        writer.WriteNumber("character", max 0L (position.column - 1L))
        writer.WriteEndObject()

    let private writeRange (writer: Utf8JsonWriter) (span: SourceSpan) =
        writer.WriteStartObject()
        writer.WritePropertyName "start"
        writePosition writer span.startPosition
        writer.WritePropertyName "end"
        if span.endPosition.offset > span.startPosition.offset then
            writePosition writer span.endPosition
        else
            // A point span still needs a visible extent.
            writePosition writer
                { span.startPosition with column = span.startPosition.column + 1L }
        writer.WriteEndObject()

    /// Character offset of a 0-based LSP line/character in `text`.
    let offsetAt (text: string) (line: int) (character: int) =
        let mutable offset = 0
        let mutable currentLine = 0
        while currentLine < line && offset < text.Length do
            if text.[offset] = '\n' then currentLine <- currentLine + 1
            offset <- offset + 1
        min text.Length (offset + max 0 character)

    // ---- Classification ---------------------------------------------------

    type SymbolClass =
        | OperativeSymbol
        | ApplicativeSymbol
        | ValueSymbol

    let classifyValue value =
        match value with
        | Applicative _ | IOFunc _ -> ApplicativeSymbol
        | PrimitiveOperative _ | Operative _ | CompiledCombiner _ -> OperativeSymbol
        | ContractedCombiner record ->
            match record.contract.mode with
            | RawOperands -> OperativeSymbol
            | EvaluatedArguments -> ApplicativeSymbol
        | _ -> ValueSymbol

    let private classifyForm (form: Source.LocatedValue) =
        match form.kind with
        | Source.LList (head :: _) ->
            match head.kind with
            | Source.LAtom "vau" | Source.LAtom "$vau" -> OperativeSymbol
            | Source.LAtom "lambda" | Source.LAtom "wrap" -> ApplicativeSymbol
            | _ -> ValueSymbol
        | _ -> ValueSymbol

    /// `(define name form)` at any nesting depth, classified by the form's
    /// syntactic head. Quoted structure defines nothing.
    let rec private collectDefines acc (form: Source.LocatedValue) =
        match form.kind with
        | Source.LList (head :: rest as items) ->
            let acc =
                match head.kind, rest with
                | Source.LAtom "define", nameForm :: valueForm :: _ ->
                    match nameForm.kind with
                    | Source.LAtom name -> Map.add name (classifyForm valueForm) acc
                    | _ -> acc
                | _ -> acc
            List.fold collectDefines acc items
        | Source.LDottedList (items, tail) ->
            collectDefines (List.fold collectDefines acc items) tail
        | Source.LVector items -> Array.fold collectDefines acc items
        | _ -> acc

    let private parsedForms sourceName text =
        match Parser.readLocatedExprList sourceName text with
        | Choice2Of2 forms -> forms
        | Choice1Of2 _ -> []


    // ---- Contracts and hover text -----------------------------------------

    let private renderClass = function
        | OperativeSymbol -> "operative"
        | ApplicativeSymbol -> "applicative"
        | ValueSymbol -> "value"

    let renderContract (contract: OperativeContract) =
        let operands = contract.operands |> List.map Contracts.shapeName
        let operandText =
            let text = String.concat " " operands
            match contract.minimumOperands with
            | Some _ -> text + " ..."
            | None -> text
        let effect =
            match contract.effect with
            | Pure -> "pure"
            | Effectful -> "effectful"
        let trust =
            match contract.trust with
            | Certified -> "certified"
            | Asserted -> "asserted"
        sprintf
            "(%s%s) → %s — %s, %s"
            contract.name
            (if operandText = "" then "" else " " + operandText)
            (Contracts.shapeName contract.result)
            effect
            trust

    let private isSymbolChar (c: char) =
        Char.IsLetterOrDigit c || "!#$%|*+-/:<=>?@^_~.&".Contains c

    /// The symbol spanning `offset` in `text`, if any.
    let symbolAt (text: string) (offset: int) =
        let offset = max 0 (min offset text.Length)
        let mutable start = offset
        while start > 0 && isSymbolChar text.[start - 1] do
            start <- start - 1
        let mutable finish = offset
        while finish < text.Length && isSymbolChar text.[finish] do
            finish <- finish + 1
        if finish > start then Some(text.Substring(start, finish - start)) else None

    // ---- Session ----------------------------------------------------------

    type private Session = {
        documents : Dictionary<string, string>
        /// Buffer defines from each document's last *successful* parse. A
        /// half-typed buffer does not parse (the reader has no error
        /// recovery, ADR 0009 phase 4), and completion mid-edit is exactly
        /// when the buffer is broken -- so the last good parse serves until
        /// the next one.
        defines : Dictionary<string, Map<string, SymbolClass>>
        /// Bootstrapped kernel environment: symbol source for completion,
        /// hover, and semantic classification. Never evaluated into by the
        /// server -- buffers are parsed and analyzed, not run.
        env : LispVal
        /// Fresh primitive environment for analysis, matching what `check`
        /// and `compile` validate against.
        checkEnv : LispVal
    }

    let private uriToPath (uri: string) =
        try
            let parsed = Uri uri
            if parsed.IsFile then parsed.LocalPath else uri
        with _ -> uri

    let private refreshDefines session (uri: string) text =
        match Parser.readLocatedExprList (uriToPath uri) text with
        | Choice2Of2 forms ->
            session.defines.[uri] <- List.fold collectDefines Map.empty forms
        | Choice1Of2 _ -> ()

    let private definesFor session (uri: string) =
        match session.defines.TryGetValue uri with
        | true, value -> value
        | _ -> Map.empty

    let private classifySymbol session defines name =
        match Map.tryFind name defines with
        | Some OperativeSymbol -> OperativeSymbol
        | Some ApplicativeSymbol -> ApplicativeSymbol
        | Some ValueSymbol ->
            // A buffer define of unknown shape may still shadow a combiner;
            // fall back to the environment only when the buffer says nothing.
            ValueSymbol
        | None ->
            match SymbolTable.getVar' session.env name with
            | Some value -> classifyValue value
            | None -> ValueSymbol

    // ---- Features ---------------------------------------------------------

    let private publishDiagnostics output session (uri: string) =
        let text =
            match session.documents.TryGetValue uri with
            | true, value -> value
            | _ -> ""
        let sourceName = uriToPath uri
        notify output "textDocument/publishDiagnostics" (fun writer ->
            writer.WriteStartObject()
            writer.WriteString("uri", uri)
            writer.WritePropertyName "diagnostics"
            writer.WriteStartArray()
            match Emit.checkSourceInEnv session.checkEnv sourceName text with
            | Choice2Of2 () -> ()
            | Choice1Of2 error ->
                let locations, core = errorLocations error
                writer.WriteStartObject()
                writer.WritePropertyName "range"
                let wholeDocument =
                    { sourceName = sourceName
                      startPosition = { offset = 0L; line = 1L; column = 1L }
                      endPosition = { offset = 1L; line = 1L; column = 2L } }
                let innermost, enclosing =
                    match List.rev locations with
                    | (span, _) :: rest -> span, List.map fst rest
                    | [] -> wholeDocument, []
                writeRange writer innermost
                writer.WriteNumber("severity", 1)
                writer.WriteString("source", "IronKernel")
                writer.WriteString("message", errorMessage core)
                if not (List.isEmpty enclosing) then
                    writer.WritePropertyName "relatedInformation"
                    writer.WriteStartArray()
                    for span in enclosing do
                        writer.WriteStartObject()
                        writer.WritePropertyName "location"
                        writer.WriteStartObject()
                        writer.WriteString("uri", uri)
                        writer.WritePropertyName "range"
                        writeRange writer span
                        writer.WriteEndObject()
                        writer.WriteString("message", "in this enclosing form")
                        writer.WriteEndObject()
                    writer.WriteEndArray()
                writer.WriteEndObject()
            writer.WriteEndArray()
            writer.WriteEndObject())

    let private completionKind = function
        | OperativeSymbol -> 14   // Keyword
        | ApplicativeSymbol -> 3  // Function
        | ValueSymbol -> 6        // Variable

    let private handleCompletion output session (id: JsonElement) uri line character =
        let text =
            match session.documents.TryGetValue (uri: string) with
            | true, value -> value
            | _ -> ""
        let offset = offsetAt text line character
        let prefix, envMatches = Repl.completionCandidates session.env text offset
        let defines = definesFor session uri
        let fromBuffer =
            if prefix = "" then []
            else
                defines
                |> Map.toList
                |> List.map fst
                |> List.filter (fun name -> name.StartsWith(prefix, StringComparison.Ordinal))
        let names = List.distinct (fromBuffer @ envMatches) |> List.sort
        respond output id (fun writer ->
            writer.WriteStartArray()
            for name in names do
                writer.WriteStartObject()
                writer.WriteString("label", (name: string))
                let symbolClass = classifySymbol session defines name
                writer.WriteNumber("kind", completionKind symbolClass)
                match SymbolTable.getVar' session.env name with
                | Some value ->
                    match Contracts.tryGetContract value with
                    | Some contract -> writer.WriteString("detail", renderContract contract)
                    | None -> writer.WriteString("detail", renderClass symbolClass)
                | None -> writer.WriteString("detail", renderClass symbolClass)
                writer.WriteEndObject()
            writer.WriteEndArray())

    let private handleHover output session (id: JsonElement) uri line character =
        let text =
            match session.documents.TryGetValue (uri: string) with
            | true, value -> value
            | _ -> ""
        let offset = offsetAt text line character
        match symbolAt text offset with
        | None -> respond output id (fun writer -> writer.WriteNullValue())
        | Some name ->
            let defines = definesFor session uri
            let lines =
                match SymbolTable.getVar' session.env name with
                | Some value ->
                    let heading = sprintf "`%s` — %s" name (renderClass (classifyValue value))
                    match Contracts.tryGetContract value with
                    | Some contract -> [ heading; ""; "```"; renderContract contract; "```" ]
                    | None -> [ heading ]
                | None ->
                    match Map.tryFind name defines with
                    | Some symbolClass ->
                        [ sprintf "`%s` — %s, defined in this file" name (renderClass symbolClass) ]
                    | None -> []
            match lines with
            | [] -> respond output id (fun writer -> writer.WriteNullValue())
            | lines ->
                respond output id (fun writer ->
                    writer.WriteStartObject()
                    writer.WritePropertyName "contents"
                    writer.WriteStartObject()
                    writer.WriteString("kind", "markdown")
                    writer.WriteString("value", String.concat "\n" lines)
                    writer.WriteEndObject()
                    writer.WriteEndObject())

    let rec private collectAtoms acc (form: Source.LocatedValue) =
        match form.kind with
        | Source.LAtom name -> (form.span, name) :: acc
        | Source.LList items -> List.fold collectAtoms acc items
        | Source.LDottedList (items, tail) ->
            collectAtoms (List.fold collectAtoms acc items) tail
        | Source.LVector items -> Array.fold collectAtoms acc items
        // Quoted atoms are data, not references; classifying them would lie.
        | Source.LQuote _ | Source.LLiteral _ -> acc

    /// LSP semantic token encoding: (deltaLine, deltaStartChar, length, type, 0)
    /// per token, sorted by position. Types index the legend: 0 operative,
    /// 1 applicative.
    let semanticTokenData classify sourceName text =
        let atoms =
            parsedForms sourceName text
            |> List.fold collectAtoms []
            |> List.choose (fun (span, name) ->
                match classify name with
                | OperativeSymbol -> Some(span, 0)
                | ApplicativeSymbol -> Some(span, 1)
                | ValueSymbol -> None)
            |> List.sortBy (fun (span, _) -> span.startPosition.line, span.startPosition.column)
        let mutable previousLine = 1L
        let mutable previousColumn = 1L
        [ for span, tokenType in atoms do
            let line = span.startPosition.line
            let column = span.startPosition.column
            let deltaLine = line - previousLine
            let deltaColumn = if deltaLine = 0L then column - previousColumn else column - 1L
            let length = span.endPosition.offset - span.startPosition.offset
            previousLine <- line
            previousColumn <- column
            yield! [ deltaLine; deltaColumn; length; int64 tokenType; 0L ] ]

    let private handleSemanticTokens output session (id: JsonElement) uri =
        let text =
            match session.documents.TryGetValue (uri: string) with
            | true, value -> value
            | _ -> ""
        let sourceName = uriToPath uri
        let data = semanticTokenData (classifySymbol session (definesFor session uri)) sourceName text
        respond output id (fun writer ->
            writer.WriteStartObject()
            writer.WritePropertyName "data"
            writer.WriteStartArray()
            for value in data do
                writer.WriteNumberValue value
            writer.WriteEndArray()
            writer.WriteEndObject())

    // ---- Dispatch ---------------------------------------------------------

    let private textDocumentUri (parameters: JsonElement) =
        parameters.GetProperty("textDocument").GetProperty("uri").GetString()

    let private positionOf (parameters: JsonElement) =
        let position = parameters.GetProperty "position"
        position.GetProperty("line").GetInt32(), position.GetProperty("character").GetInt32()

    /// Run the server over the given streams until `exit` or end of input.
    let runOn (input: Stream) (output: Stream) profile : int =
        match Emit.bootstrapEnvForProfile profile with
        | Choice1Of2 error ->
            eprintfn "Startup error: %s" (showError error)
            1
        | Choice2Of2 env ->
            let session = {
                documents = Dictionary()
                defines = Dictionary()
                env = env
                checkEnv = Runtime.makePrimitiveBindingsForProfile profile
            }
            let mutable running = true
            let mutable exitCode = 0
            while running do
                match readFramed input with
                | None -> running <- false
                | Some document ->
                    use document = document
                    let root = document.RootElement
                    let methodName =
                        match root.TryGetProperty "method" with
                        | true, value -> value.GetString()
                        | _ -> ""
                    let hasId, id = root.TryGetProperty "id"
                    let parameters =
                        match root.TryGetProperty "params" with
                        | true, value -> value
                        | _ -> JsonDocument.Parse("null").RootElement
                    match methodName with
                    | "initialize" ->
                        respond output id (fun writer ->
                            writer.WriteStartObject()
                            writer.WritePropertyName "capabilities"
                            writer.WriteStartObject()
                            writer.WriteNumber("textDocumentSync", 1)
                            writer.WritePropertyName "completionProvider"
                            writer.WriteStartObject()
                            writer.WriteEndObject()
                            writer.WriteBoolean("hoverProvider", true)
                            writer.WritePropertyName "semanticTokensProvider"
                            writer.WriteStartObject()
                            writer.WritePropertyName "legend"
                            writer.WriteStartObject()
                            writer.WritePropertyName "tokenTypes"
                            writer.WriteStartArray()
                            writer.WriteStringValue "operative"
                            writer.WriteStringValue "applicative"
                            writer.WriteEndArray()
                            writer.WritePropertyName "tokenModifiers"
                            writer.WriteStartArray()
                            writer.WriteEndArray()
                            writer.WriteEndObject()
                            writer.WriteBoolean("full", true)
                            writer.WriteEndObject()
                            writer.WriteEndObject()
                            writer.WritePropertyName "serverInfo"
                            writer.WriteStartObject()
                            writer.WriteString("name", "IronKernel")
                            writer.WriteString("version", Repl.version)
                            writer.WriteEndObject()
                            writer.WriteEndObject())
                    | "initialized" -> ()
                    | "shutdown" ->
                        respond output id (fun writer -> writer.WriteNullValue())
                    | "exit" -> running <- false
                    | "textDocument/didOpen" ->
                        let textDocument = parameters.GetProperty "textDocument"
                        let uri = textDocument.GetProperty("uri").GetString()
                        session.documents.[uri] <- textDocument.GetProperty("text").GetString()
                        refreshDefines session uri session.documents.[uri]
                        publishDiagnostics output session uri
                    | "textDocument/didChange" ->
                        let uri = textDocumentUri parameters
                        let changes = parameters.GetProperty "contentChanges"
                        // Full sync: the last change carries the whole document.
                        let mutable text = None
                        for change in changes.EnumerateArray() do
                            text <- Some(change.GetProperty("text").GetString())
                        match text with
                        | Some value ->
                            session.documents.[uri] <- value
                            refreshDefines session uri value
                            publishDiagnostics output session uri
                        | None -> ()
                    | "textDocument/didClose" ->
                        let uri = textDocumentUri parameters
                        session.documents.Remove uri |> ignore
                        session.defines.Remove uri |> ignore
                        notify output "textDocument/publishDiagnostics" (fun writer ->
                            writer.WriteStartObject()
                            writer.WriteString("uri", uri)
                            writer.WritePropertyName "diagnostics"
                            writer.WriteStartArray()
                            writer.WriteEndArray()
                            writer.WriteEndObject())
                    | "textDocument/completion" ->
                        let line, character = positionOf parameters
                        handleCompletion output session id (textDocumentUri parameters) line character
                    | "textDocument/hover" ->
                        let line, character = positionOf parameters
                        handleHover output session id (textDocumentUri parameters) line character
                    | "textDocument/semanticTokens/full" ->
                        handleSemanticTokens output session id (textDocumentUri parameters)
                    | other when hasId ->
                        respondError output id -32601 (sprintf "method not found: %s" other)
                    | _ -> ()
            exitCode

    let run profile : int =
        runOn (Console.OpenStandardInput()) (Console.OpenStandardOutput()) profile
