module IronKernel.Tests.ExampleTests

open System
open System.IO
open Xunit
open IronKernel.Ast
open IronKernel.Emit
open IronKernel.Errors
open IronKernel.Tests.TestHelpers

let private examplesDir () =
    [ "Examples"
      Path.Combine("..", "Examples")
      Path.Combine("..", "..", "Examples")
      Path.Combine(Directory.GetCurrentDirectory(), "Examples") ]
    |> List.tryFind Directory.Exists
    |> Option.defaultWith (fun () -> failwith "Examples directory not found")

[<Fact>]
let ``hello.ikr packages without execution`` () =
    let path = Path.Combine(examplesDir (), "hello.ikr")
    let outp = Path.Combine(Path.GetTempPath(), "hello-ci.ikc")
    match compileFileToPackage path outp with
    | Choice1Of2 e -> failwith (showError e)
    | Choice2Of2 p -> Assert.True(File.Exists p)

[<Fact>]
let ``vau-dotnet.ikr packages without execution`` () =
    let path = Path.Combine(examplesDir (), "vau-dotnet.ikr")
    let outp = Path.Combine(Path.GetTempPath(), "vau-dotnet-ci.ikc")
    match compileFileToPackage path outp with
    | Choice1Of2 e -> failwith (showError e)
    | Choice2Of2 p -> Assert.True(File.Exists p)

[<Fact>]
let ``samples.ikr packages without execution`` () =
    let path = Path.Combine(examplesDir (), "samples.ikr")
    let outp = Path.Combine(Path.GetTempPath(), "samples-ci.ikc")
    match compileFileToPackage path outp with
    | Choice1Of2 e -> failwith (showError e)
    | Choice2Of2 p -> Assert.True(File.Exists p)

/// Runs an example in-process and returns whatever it wrote to stdout.
/// Continuation-heavy examples only fail when actually executed, so packaging
/// them is not enough to keep them working.
let private runExampleCapturingOutput name =
    let path = Path.Combine(examplesDir (), name)
    let original = Console.Out
    use writer = new StringWriter()
    Console.SetOut writer
    try
        match bootstrapEnv () with
        | Choice1Of2 e -> failwith (showError e)
        | Choice2Of2 env ->
            match runSourceFile env path with
            | Choice1Of2 e -> failwith (showError e)
            | Choice2Of2 _ -> ()
    finally
        Console.SetOut original
    writer.ToString().Replace("\r\n", "\n")

[<Fact>]
let ``coroutines.ikr interleaves both computations and terminates`` () =
    let output = runExampleCapturingOutput "coroutines.ikr"

    // Both coroutines must run, alternating rather than one draining first.
    Assert.Contains("Hefty computation: 5", output)
    Assert.Contains("Hefty computation (b)", output)
    Assert.Contains("Hefty computation (c)", output)
    Assert.Contains("Straight up.", output)
    Assert.Contains("Quarter til.", output)

    // The countdown must reach 0, proving the exchanged continuation survives
    // across iterations instead of being lost to a shadowing binding.
    Assert.Contains("Hefty computation: 0", output)

    let lines = output.Split('\n') |> Array.filter (fun line -> line.Trim() <> "")
    let hefty = lines |> Array.filter (fun l -> l.StartsWith "Hefty computation: ")
    Assert.Equal(6, hefty.Length)
    Assert.Equal<string[]>(
        [| "Hefty computation: 5"; "Hefty computation: 4"; "Hefty computation: 3"
           "Hefty computation: 2"; "Hefty computation: 1"; "Hefty computation: 0" |],
        hefty)
