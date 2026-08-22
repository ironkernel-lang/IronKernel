namespace IronKernel

/// Content-Length framed JSON-RPC over streams: the transport the language
/// server (`ik lsp`) and the session protocol (`ik session`) share. A
/// deliberately small hand-rolled layer -- framing, requests, responses,
/// notifications -- kept dependency-free and testable against in-memory
/// streams (ADR 0009 phases 3 and 6).
module Jsonrpc =

    open System
    open System.IO
    open System.Text
    open System.Text.Json

    let readFramed (input: Stream) : JsonDocument option =
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

    let writeFramed (output: Stream) (json: string) =
        let bytes = Encoding.UTF8.GetBytes json
        let header = Encoding.ASCII.GetBytes(sprintf "Content-Length: %d\r\n\r\n" bytes.Length)
        output.Write(header, 0, header.Length)
        output.Write(bytes, 0, bytes.Length)
        output.Flush()

    let toJson (write: Utf8JsonWriter -> unit) =
        use stream = new MemoryStream()
        use writer = new Utf8JsonWriter(stream)
        write writer
        writer.Flush()
        Encoding.UTF8.GetString(stream.ToArray())

    let respond output (id: JsonElement) (writeResult: Utf8JsonWriter -> unit) =
        toJson (fun writer ->
            writer.WriteStartObject()
            writer.WriteString("jsonrpc", "2.0")
            writer.WritePropertyName "id"
            id.WriteTo writer
            writer.WritePropertyName "result"
            writeResult writer
            writer.WriteEndObject())
        |> writeFramed output

    let respondError output (id: JsonElement) code (message: string) =
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

    let notify output (method: string) (writeParams: Utf8JsonWriter -> unit) =
        toJson (fun writer ->
            writer.WriteStartObject()
            writer.WriteString("jsonrpc", "2.0")
            writer.WriteString("method", method)
            writer.WritePropertyName "params"
            writeParams writer
            writer.WriteEndObject())
        |> writeFramed output

    /// The method name, id (when present), and params of one message.
    let envelope (document: JsonDocument) =
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
        methodName, hasId, id, parameters
