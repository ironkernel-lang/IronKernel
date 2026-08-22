module IronKernel.Tests.CheckTests

open System
open System.IO
open System.Text.Json
open Xunit

open IronKernel.Ast
open IronKernel.Check

let private tempPath extension =
    Path.Combine(Path.GetTempPath(), "ironkernel-check-" + Guid.NewGuid().ToString("N") + extension)

let private withSource (contents: string) body =
    let path = tempPath ".ikr"
    try
        File.WriteAllText(path, contents)
        body path
    finally
        File.Delete path

let private parseReport (json: string) =
    use document = JsonDocument.Parse json
    let root = document.RootElement
    Assert.Equal(1, root.GetProperty("version").GetInt32())
    root.GetProperty("diagnostics").EnumerateArray()
    |> Seq.map (fun d -> d.Clone())
    |> Seq.toList

[<Fact>]
let ``check reports nothing for a clean file`` () =
    withSource "(define f (lambda (x) (+ x 1)))\n" (fun path ->
        Assert.Empty(checkFile Unrestricted path))

[<Fact>]
let ``check reports a parse error with its span`` () =
    withSource "(define f\n  (lambda (x)\n    (+ x 1))\n" (fun path ->
        match checkFile Unrestricted path with
        | [ finding ] ->
            Assert.Equal(path, finding.path)
            match IronKernel.Errors.errorLocations finding.error with
            | [ span, _ ], IronKernel.Ast.Parser _ ->
                Assert.Equal(path, span.sourceName)
                Assert.Equal(4L, span.startPosition.line)
                Assert.Equal(1L, span.startPosition.column)
            | locations, core -> failwithf "unexpected shape: %A / %A" locations core
        | findings -> failwithf "expected one finding, got %A" findings)

[<Fact>]
let ``check json carries file range and message`` () =
    withSource "(foo))\n" (fun path ->
        let diagnostics = parseReport (toJson (checkFile Unrestricted path))
        let diagnostic = Assert.Single diagnostics
        Assert.Equal("error", diagnostic.GetProperty("severity").GetString())
        Assert.Contains("Parse error", diagnostic.GetProperty("message").GetString())
        Assert.Equal(path, diagnostic.GetProperty("file").GetString())
        let start = diagnostic.GetProperty("range").GetProperty("start")
        Assert.Equal(1L, start.GetProperty("line").GetInt64())
        Assert.Equal(6L, start.GetProperty("column").GetInt64()))

[<Fact>]
let ``check json for a clean file is an empty diagnostics array`` () =
    withSource "(define x 1)\n" (fun path ->
        Assert.Empty(parseReport (toJson (checkFile Unrestricted path))))

[<Fact>]
let ``a finding without a span carries the checked path and no range`` () =
    let path = tempPath ".ikr"
    let diagnostics = parseReport (toJson (checkFile Unrestricted path))
    let diagnostic = Assert.Single diagnostics
    Assert.Equal(path, diagnostic.GetProperty("file").GetString())
    let mutable range = Unchecked.defaultof<JsonElement>
    Assert.False(diagnostic.TryGetProperty("range", &range))

let private withProject body =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-check-project-" + Guid.NewGuid().ToString("N"))
    Directory.CreateDirectory root |> ignore
    try
        Assert.Equal(0, IronKernel.Project.create "app" "demo" root)
        let directory = Path.Combine(root, "demo")
        body directory (Path.Combine(directory, "demo.ikproj"))
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``project check walks sources main and tests`` () =
    withProject (fun directory projectPath ->
        let load () =
            match IronKernel.Project.load projectPath with
            | Choice2Of2 project -> project
            | Choice1Of2 error -> failwithf "project load failed: %A" error
        Assert.Empty(checkProject (load ()))
        let brokenSource = Path.Combine(directory, "src", "extra.ikr")
        File.WriteAllText(brokenSource, "(define broken\n")
        let brokenTest = Path.Combine(directory, "test", "extra_test.ikr")
        File.WriteAllText(brokenTest, "(assert-true\n")
        let findings = checkProject (load ())
        Assert.Equal(2, List.length findings)
        Assert.Contains(findings, fun finding -> finding.path = brokenSource)
        Assert.Contains(findings, fun finding -> finding.path = brokenTest))

[<Fact>]
let ``check reports every broken region in one file`` () =
    withSource ")\n(ok 1)\n)\n(ok2 2)\n" (fun path ->
        let findings = checkFile Unrestricted path
        Assert.Equal(2, List.length findings)
        Assert.Equal(2, List.length (parseReport (toJson findings))))
