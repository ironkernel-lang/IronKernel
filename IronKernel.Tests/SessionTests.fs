module IronKernel.Tests.SessionTests

open System.IO
open System.Text
open System.Text.Json
open Xunit

open IronKernel.Ast
open IronKernel.Session

let private frame (stream: Stream) (json: string) =
    let bytes = Encoding.UTF8.GetBytes json
    let header = Encoding.ASCII.GetBytes(sprintf "Content-Length: %d\r\n\r\n" bytes.Length)
    stream.Write(header, 0, header.Length)
    stream.Write(bytes, 0, bytes.Length)

let private readFrames (data: byte[]) =
    let text = Encoding.UTF8.GetString data
    let mutable index = 0
    let frames = ResizeArray()
    while index < text.Length do
        let headerEnd = text.IndexOf("\r\n\r\n", index, System.StringComparison.Ordinal)
        let length =
            text.Substring(index, headerEnd - index).Split("\r\n")
            |> Array.pick (fun line ->
                if line.StartsWith("Content-Length:", System.StringComparison.OrdinalIgnoreCase) then
                    Some(int (line.Substring("Content-Length:".Length).Trim()))
                else None)
        let bodyStart = Encoding.UTF8.GetByteCount(text.Substring(0, headerEnd)) + 4
        frames.Add(JsonDocument.Parse(Encoding.UTF8.GetString(data, bodyStart, length)))
        index <- (Encoding.UTF8.GetString(data, 0, bodyStart + length)).Length
    List.ofSeq frames

let private session profile (messages: string list) =
    use input = new MemoryStream()
    messages |> List.iter (frame input)
    input.Position <- 0L
    use output = new MemoryStream()
    let exitCode = runOn input output profile
    Assert.Equal(0, exitCode)
    readFrames (output.ToArray())

let private request id method' parameters =
    sprintf """{"jsonrpc":"2.0","id":%d,"method":"%s","params":%s}""" (id: int) (method': string) (parameters: string)

let private evalRequest id (code: string) =
    request id "eval" (sprintf """{"code":%s}""" (JsonSerializer.Serialize code))

let private resultOf id (frames: JsonDocument list) =
    frames
    |> List.pick (fun frameDocument ->
        let root = frameDocument.RootElement
        match root.TryGetProperty "id" with
        | true, value when value.ValueKind = JsonValueKind.Number && value.GetInt32() = id ->
            match root.TryGetProperty "result" with
            | true, result -> Some result
            | _ -> Some(root.GetProperty "error")
        | _ -> None)

[<Fact>]
let ``a session evaluates persistently and separates errors from values`` () =
    let frames =
        session Unrestricted
            [ request 1 "initialize" "{}"
              evalRequest 2 "(define x 40)\n(+ x 2)"
              evalRequest 3 "x"
              evalRequest 4 "(car 5)"
              request 5 "reset" "{}"
              evalRequest 6 "x" ]
    Assert.Equal("unrestricted", (resultOf 1 frames).GetProperty("profile").GetString())

    // A multi-form eval returns the last value; the define persists.
    Assert.Equal("42", (resultOf 2 frames).GetProperty("value").GetString())
    Assert.Equal("40", (resultOf 3 frames).GetProperty("value").GetString())

    // The phase-6 point: an error is a structured field, not stdout text.
    let error = (resultOf 4 frames).GetProperty "error"
    Assert.Contains("expected pair", error.GetProperty("message").GetString())
    let location = error.GetProperty("locations").[0]
    Assert.Equal("session", location.GetProperty("file").GetString())
    Assert.Equal(1, location.GetProperty("range").GetProperty("start").GetProperty("line").GetInt32())
    let mutable value = Unchecked.defaultof<JsonElement>
    Assert.False((resultOf 4 frames).TryGetProperty("value", &value))

    // Reset restores the bootstrap: the definition is gone.
    let afterReset = resultOf 6 frames
    Assert.Contains("unbound variable", afterReset.GetProperty("error").GetProperty("message").GetString())

[<Fact>]
let ``printed output travels in the response not the channel`` () =
    let frames =
        session Unrestricted
            [ evalRequest 1 "(print \"hello, session\")" ]
    let result = resultOf 1 frames
    Assert.Equal("hello, session", result.GetProperty("output").GetString())
    Assert.True(result.GetProperty("inert").GetBoolean())

[<Fact>]
let ``the session honours the capability profile`` () =
    let frames =
        session Minimal
            [ request 1 "initialize" "{}"
              evalRequest 2 "(print \"denied\")" ]
    Assert.Equal("minimal", (resultOf 1 frames).GetProperty("profile").GetString())
    // Under minimal there is no print binding at all: host output is authority.
    let error = (resultOf 2 frames).GetProperty "error"
    Assert.Contains("print", error.GetProperty("message").GetString())

[<Fact>]
let ``unknown session requests get a method-not-found error`` () =
    let frames =
        session Unrestricted [ request 1 "step" "{}" ]
    let root = frames.Head.RootElement
    Assert.Equal(-32601, root.GetProperty("error").GetProperty("code").GetInt32())
