module IronKernel.Tests.LspTests

open System
open System.IO
open System.Text
open System.Text.Json
open Xunit

open IronKernel.Ast
open IronKernel.LanguageServer

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
        let headerEnd = text.IndexOf("\r\n\r\n", index, StringComparison.Ordinal)
        let headers = text.Substring(index, headerEnd - index)
        let length =
            headers.Split("\r\n")
            |> Array.pick (fun line ->
                if line.StartsWith("Content-Length:", StringComparison.OrdinalIgnoreCase) then
                    Some(int (line.Substring("Content-Length:".Length).Trim()))
                else None)
        // Content-Length counts bytes; the payload is ASCII-safe JSON in these
        // tests except for escaped sequences, so slice the byte array instead.
        let bodyStart = Encoding.UTF8.GetByteCount(text.Substring(0, headerEnd)) + 4
        let body = Encoding.UTF8.GetString(data, bodyStart, length)
        frames.Add(JsonDocument.Parse body)
        let consumed = Encoding.UTF8.GetString(data, 0, bodyStart + length)
        index <- consumed.Length
    List.ofSeq frames

/// Run one scripted session against the in-process server.
let private session (messages: string list) =
    use input = new MemoryStream()
    messages |> List.iter (frame input)
    input.Position <- 0L
    use output = new MemoryStream()
    let exitCode = runOn input output Unrestricted
    Assert.Equal(0, exitCode)
    readFrames (output.ToArray())

let private request id method' parameters =
    sprintf """{"jsonrpc":"2.0","id":%d,"method":"%s","params":%s}""" (id: int) (method': string) (parameters: string)

let private notification method' parameters =
    sprintf """{"jsonrpc":"2.0","method":"%s","params":%s}""" (method': string) (parameters: string)

let private didOpen (text: string) =
    let escaped = JsonSerializer.Serialize text
    notification
        "textDocument/didOpen"
        (sprintf """{"textDocument":{"uri":"file:///probe.ikr","languageId":"ironkernel","version":1,"text":%s}}""" escaped)

let private resultOf id (frames: JsonDocument list) =
    frames
    |> List.pick (fun frameDocument ->
        let root = frameDocument.RootElement
        match root.TryGetProperty "id" with
        | true, value when value.ValueKind = JsonValueKind.Number && value.GetInt32() = id ->
            Some(root.GetProperty "result")
        | _ -> None)

let private diagnosticsOf (frames: JsonDocument list) =
    frames
    |> List.choose (fun frameDocument ->
        let root = frameDocument.RootElement
        match root.TryGetProperty "method" with
        | true, value when value.GetString() = "textDocument/publishDiagnostics" ->
            Some(root.GetProperty("params").GetProperty "diagnostics")
        | _ -> None)

[<Fact>]
let ``initialize reports the semantic token legend and features`` () =
    let frames = session [ request 1 "initialize" "{}" ]
    let capabilities = (resultOf 1 frames).GetProperty "capabilities"
    Assert.True(capabilities.GetProperty("hoverProvider").GetBoolean())
    Assert.Equal(1, capabilities.GetProperty("textDocumentSync").GetInt32())
    let legend =
        capabilities.GetProperty("semanticTokensProvider").GetProperty("legend").GetProperty "tokenTypes"
    let tokenTypes = legend.EnumerateArray() |> Seq.map (fun t -> t.GetString()) |> List.ofSeq
    Assert.Equal<string list>([ "operative"; "applicative" ], tokenTypes)

[<Fact>]
let ``diagnostics follow the buffer through open and change`` () =
    let frames =
        session
            [ request 1 "initialize" "{}"
              didOpen "(define whole 1)\n"
              notification
                  "textDocument/didChange"
                  """{"textDocument":{"uri":"file:///probe.ikr"},"contentChanges":[{"text":"(broken\n"}]}""" ]
    match diagnosticsOf frames with
    | [ clean; broken ] ->
        Assert.Equal(0, clean.GetArrayLength())
        Assert.Equal(1, broken.GetArrayLength())
        let diagnostic = broken.[0]
        Assert.Contains("Parse error", diagnostic.GetProperty("message").GetString())
        Assert.Equal(1, diagnostic.GetProperty("severity").GetInt32())
        let start = diagnostic.GetProperty("range").GetProperty "start"
        Assert.Equal(1, start.GetProperty("line").GetInt32())
        Assert.Equal(0, start.GetProperty("character").GetInt32())
    | published -> failwithf "expected two diagnostic publications, got %d" published.Length

[<Fact>]
let ``completion merges buffer defines with environment symbols`` () =
    let frames =
        session
            [ request 1 "initialize" "{}"
              // The buffer does not parse mid-edit; the recovering reader
              // still serves its defines -- no didChange, no cache.
              didOpen "(define completion-probe 1)\n(completion-pr"
              request 2 "textDocument/completion"
                  """{"textDocument":{"uri":"file:///probe.ikr"},"position":{"line":1,"character":14}}"""
              notification
                  "textDocument/didChange"
                  """{"textDocument":{"uri":"file:///probe.ikr"},"contentChanges":[{"text":"(vector-r"}]}"""
              request 3 "textDocument/completion"
                  """{"textDocument":{"uri":"file:///probe.ikr"},"position":{"line":0,"character":9}}""" ]
    let labels id =
        (resultOf id frames).EnumerateArray()
        |> Seq.map (fun item -> item.GetProperty("label").GetString())
        |> List.ofSeq
    Assert.Contains("completion-probe", labels 2)
    Assert.Contains("vector-ref", labels 3)
    let vectorRef =
        (resultOf 3 frames).EnumerateArray()
        |> Seq.find (fun item -> item.GetProperty("label").GetString() = "vector-ref")
    // 3 = Function: applicatives complete as functions, by resolution.
    Assert.Equal(3, vectorRef.GetProperty("kind").GetInt32())

[<Fact>]
let ``hover renders contracts and buffer definitions`` () =
    let frames =
        session
            [ request 1 "initialize" "{}"
              didOpen "(define twice (vau (x) e x))\n(+ 1 2)\n"
              request 2 "textDocument/hover"
                  """{"textDocument":{"uri":"file:///probe.ikr"},"position":{"line":1,"character":1}}"""
              request 3 "textDocument/hover"
                  """{"textDocument":{"uri":"file:///probe.ikr"},"position":{"line":0,"character":9}}""" ]
    let hoverText id =
        (resultOf id frames).GetProperty("contents").GetProperty("value").GetString()
    let plus = hoverText 2
    Assert.Contains("`+`", plus)
    Assert.Contains("number", plus)
    Assert.Contains("certified", plus)
    let twice = hoverText 3
    Assert.Contains("`twice`", twice)
    Assert.Contains("operative", twice)
    Assert.Contains("defined in this file", twice)

[<Fact>]
let ``semantic tokens classify by resolution including buffer operatives`` () =
    let frames =
        session
            [ request 1 "initialize" "{}"
              didOpen "(define twice (vau (x) e x))\n(twice 1)\n(vector-ref (vector 1) 0)\n"
              request 2 "textDocument/semanticTokens/full"
                  """{"textDocument":{"uri":"file:///probe.ikr"}}""" ]
    let data =
        (resultOf 2 frames).GetProperty("data").EnumerateArray()
        |> Seq.map (fun value -> value.GetInt32())
        |> List.ofSeq
    // (deltaLine, deltaStart, length, type, modifiers) per token; type 0 is
    // operative, 1 applicative. `twice` classifying as 0 on both lines is the
    // capability no lexical grammar has: it is a *user-defined* operative.
    Assert.Equal<int list>(
        [ 0; 1; 6; 0; 0      // define
          0; 7; 5; 0; 0      // twice (definition)
          0; 7; 3; 0; 0      // vau
          1; 1; 5; 0; 0      // twice (use)
          1; 1; 10; 1; 0     // vector-ref
          0; 12; 6; 1; 0 ],  // vector
        data)

[<Fact>]
let ``quoted atoms are data and get no semantic token`` () =
    let data =
        semanticTokenData
            (fun _ -> OperativeSymbol)
            "quoted.ikr"
            "(aa b)\n'cc\n"
    // Only the two atoms in the combination; the quoted one is data.
    Assert.Equal<int64 list>([ 0L; 1L; 2L; 0L; 0L; 0L; 3L; 1L; 0L; 0L ], data)

[<Fact>]
let ``unknown requests get a method-not-found error`` () =
    let frames =
        session
            [ request 1 "initialize" "{}"
              request 2 "textDocument/definition"
                  """{"textDocument":{"uri":"file:///probe.ikr"},"position":{"line":0,"character":0}}""" ]
    let error =
        frames
        |> List.pick (fun frameDocument ->
            let root = frameDocument.RootElement
            match root.TryGetProperty "error" with
            | true, value -> Some value
            | _ -> None)
    Assert.Equal(-32601, error.GetProperty("code").GetInt32())

[<Fact>]
let ``a broken buffer still gets tokens defines and every error`` () =
    let frames =
        session
            [ request 1 "initialize" "{}"
              didOpen "(define twice (vau (x) e x))\n)\n(twice"
              request 2 "textDocument/semanticTokens/full"
                  """{"textDocument":{"uri":"file:///probe.ikr"}}""" ]
    // Every broken region publishes its own diagnostic.
    match diagnosticsOf frames with
    | [ published ] -> Assert.Equal(2, published.GetArrayLength())
    | published -> failwithf "expected one publication, got %d" published.Length
    // The recovered tree still classifies the trailing `(twice` use as an
    // operative -- the buffer's own vau define survives the breakage.
    let data =
        (resultOf 2 frames).GetProperty("data").EnumerateArray()
        |> Seq.map (fun value -> value.GetInt32())
        |> List.ofSeq
    Assert.Equal<int list>(
        [ 0; 1; 6; 0; 0      // define
          0; 7; 5; 0; 0      // twice (definition)
          0; 7; 3; 0; 0      // vau
          2; 1; 5; 0; 0 ],   // twice (use, on the completed trailing form)
        data)
