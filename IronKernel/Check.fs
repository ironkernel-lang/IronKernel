namespace IronKernel

/// `ik check`: parse and analyze source without evaluating it or writing output.
/// Findings keep the location chain the runtime already attaches; `--json` emits
/// them in the stable machine format editors consume (ADR 0009).
module Check =

    open System
    open System.IO
    open System.Text
    open System.Text.Json
    open Ast
    open Errors

    /// One reported problem: the file the check was asked about -- spans inside
    /// the error may name other files -- and the error, locations intact.
    type Finding = {
        path : string
        error : LispError
    }

    let checkFile profile (path: string) : Finding list =
        match Emit.checkSourceFileForProfile profile path with
        | Choice1Of2 error -> [ { path = path; error = error } ]
        | Choice2Of2 () -> []

    /// The files the project's author edits: sources, main, tests. Dependency
    /// sources are published artifacts and are not this project's to fix.
    let private projectFiles (project: Project.IkProject) =
        project.sources @ [ project.main ] @ project.tests
        |> List.distinctBy (fun (path: string) -> path.ToUpperInvariant())

    let checkProject (project: Project.IkProject) : Finding list =
        projectFiles project |> List.collect (checkFile project.profile)

    let private writeLocation (writer: Utf8JsonWriter) fallbackPath (span: SourceSpan) =
        let file =
            if String.IsNullOrWhiteSpace span.sourceName then fallbackPath
            else span.sourceName
        writer.WriteString("file", (file: string))
        writer.WritePropertyName "range"
        writer.WriteStartObject()
        for name, position in [ "start", span.startPosition; "end", span.endPosition ] do
            writer.WritePropertyName (name: string)
            writer.WriteStartObject()
            writer.WriteNumber("line", position.line)
            writer.WriteNumber("column", position.column)
            writer.WriteEndObject()
        writer.WriteEndObject()

    /// Lines and columns are 1-based, matching the human diagnostics; `end` is
    /// exclusive. A finding without a span carries only `file`, no `range`.
    let toJson (findings: Finding list) : string =
        use stream = new MemoryStream()
        use writer = new Utf8JsonWriter(stream)
        writer.WriteStartObject()
        writer.WriteNumber("version", 1)
        writer.WritePropertyName "diagnostics"
        writer.WriteStartArray()
        for finding in findings do
            let locations, core = errorLocations finding.error
            writer.WriteStartObject()
            writer.WriteString("severity", "error")
            writer.WriteString("message", errorMessage core)
            match List.rev locations with
            | [] -> writer.WriteString("file", finding.path)
            | (innermost, _) :: enclosing ->
                writeLocation writer finding.path innermost
                if not (List.isEmpty enclosing) then
                    writer.WritePropertyName "related"
                    writer.WriteStartArray()
                    for span, _ in enclosing do
                        writer.WriteStartObject()
                        writeLocation writer finding.path span
                        writer.WriteEndObject()
                    writer.WriteEndArray()
            writer.WriteEndObject()
        writer.WriteEndArray()
        writer.WriteEndObject()
        writer.Flush()
        Encoding.UTF8.GetString(stream.ToArray())

    /// Print findings -- JSON to stdout or human text to stderr -- and return
    /// the exit code: 0 clean, 1 findings.
    let report json (findings: Finding list) =
        if json then printfn "%s" (toJson findings)
        else
            for finding in findings do
                eprintfn "Check error: %s" (showError finding.error)
        if List.isEmpty findings then 0 else 1
