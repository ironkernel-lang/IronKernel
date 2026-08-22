namespace IronKernel

/// `ik session`: a persistent evaluation session over Content-Length framed
/// JSON-RPC on stdio -- the protocol ADR 0009 phase 6 puts underneath
/// everything interactive: editor eval, the inspector's remote-eval, and
/// eventually the debug adapter. The point phase 6 opens with: results and
/// errors are separate, structured values on the channel, which the human
/// REPL never offered -- it folds errors into stdout as `error : ...` text.
///
/// One session is one client. Evaluation runs on the loop, so a
/// non-terminating program blocks the session; the client owns the timeout
/// and restarts the process, which is also the interrupt story until the
/// trampoline learns cancellation.
module Session =

    open System
    open System.IO
    open System.Text.Json
    open Ast
    open Errors
    open Jsonrpc

    let private profileName = function
        | Minimal -> "minimal"
        | Safe -> "safe"
        | Unrestricted -> "unrestricted"

    let private writePosition (writer: Utf8JsonWriter) (position: SourcePosition) =
        writer.WriteStartObject()
        writer.WriteNumber("line", position.line)
        writer.WriteNumber("column", position.column)
        writer.WriteEndObject()

    /// Locations use the same 1-based, end-exclusive shape as `ik check --json`.
    let private writeLocations (writer: Utf8JsonWriter) locations =
        writer.WritePropertyName "locations"
        writer.WriteStartArray()
        for span, _ in locations do
            writer.WriteStartObject()
            writer.WriteString("file", (span: SourceSpan).sourceName)
            writer.WritePropertyName "range"
            writer.WriteStartObject()
            writer.WritePropertyName "start"
            writePosition writer span.startPosition
            writer.WritePropertyName "end"
            writePosition writer span.endPosition
            writer.WriteEndObject()
            writer.WriteEndObject()
        writer.WriteEndArray()

    /// Evaluate every form in `code`, capturing what the program prints so it
    /// travels in the response instead of corrupting the framed channel.
    /// Raw standard-output ports still bypass the capture -- a limitation the
    /// debug adapter's stdio discipline will have to close.
    let private evaluate env (code: string) =
        let previousOut = Console.Out
        use captured = new StringWriter()
        Console.SetOut captured
        let outcome =
            try
                try
                    Emit.runSource env "session" code
                with ex ->
                    Choice1Of2(ClrException ex)
            finally
                Console.SetOut previousOut
        outcome, captured.ToString()

    let runOn (input: Stream) (output: Stream) profile : int =
        match Emit.bootstrapEnvForProfile profile with
        | Choice1Of2 error ->
            eprintfn "Startup error: %s" (showError error)
            1
        | Choice2Of2 initialEnv ->
            let mutable env = initialEnv
            let mutable running = true
            while running do
                match readFramed input with
                | None -> running <- false
                | Some document ->
                    use document = document
                    let methodName, hasId, id, parameters = envelope document
                    match methodName with
                    | "initialize" ->
                        respond output id (fun writer ->
                            writer.WriteStartObject()
                            writer.WriteString("name", "IronKernel")
                            writer.WriteString("version", Repl.version)
                            writer.WriteString("profile", profileName profile)
                            writer.WriteEndObject())
                    | "eval" ->
                        let code = parameters.GetProperty("code").GetString()
                        let outcome, printed = evaluate env code
                        respond output id (fun writer ->
                            writer.WriteStartObject()
                            writer.WriteString("output", printed)
                            (match outcome with
                             | Choice2Of2 value ->
                                 let inert =
                                     match value with
                                     | Inert -> true
                                     | _ -> false
                                 writer.WriteBoolean("inert", inert)
                                 writer.WriteString("value", showVal value)
                             | Choice1Of2 error ->
                                 let locations, core = errorLocations error
                                 writer.WritePropertyName "error"
                                 writer.WriteStartObject()
                                 writer.WriteString("message", errorMessage core)
                                 writer.WriteString("rendered", showError error)
                                 writeLocations writer locations
                                 writer.WriteEndObject())
                            writer.WriteEndObject())
                    | "reset" ->
                        match Emit.bootstrapEnvForProfile profile with
                        | Choice2Of2 fresh ->
                            env <- fresh
                            respond output id (fun writer ->
                                writer.WriteStartObject()
                                writer.WriteEndObject())
                        | Choice1Of2 error ->
                            respondError output id -32000 (showError error)
                    | "exit" -> running <- false
                    | other when hasId ->
                        respondError output id -32601 (sprintf "method not found: %s" other)
                    | _ -> ()
            0

    let run profile : int =
        runOn (Console.OpenStandardInput()) (Console.OpenStandardOutput()) profile
