module IronKernel.Tests.CliTests

open System
open System.Diagnostics
open System.IO
open System.Reflection
open System.Runtime.InteropServices
open Xunit

open IronKernel
open IronKernel.Ast
open IronKernel.Errors
open IronKernel.Emit
open IronKernel.StaticEmit
open IronKernel.Repl

let private tempPath extension =
    Path.Combine(Path.GetTempPath(), "ironkernel-" + Guid.NewGuid().ToString("N") + extension)

let private repoRoot =
    let dir = Directory.GetCurrentDirectory()
    if File.Exists(Path.Combine(dir, "IronKernel.sln")) then dir
    else Path.GetFullPath(Path.Combine(dir, "..", "..", "..", ".."))

let private buildConfiguration =
    let attr = Assembly.GetExecutingAssembly().GetCustomAttribute<AssemblyConfigurationAttribute>()
    if isNull attr then "Release" else attr.Configuration

let private runCli (args: string list) =
    let startInfo = ProcessStartInfo("dotnet")
    startInfo.WorkingDirectory <- repoRoot
    startInfo.UseShellExecute <- false
    startInfo.RedirectStandardError <- true
    startInfo.RedirectStandardOutput <- true
    startInfo.ArgumentList.Add "run"
    startInfo.ArgumentList.Add "--project"
    startInfo.ArgumentList.Add "IronKernel"
    startInfo.ArgumentList.Add "-c"
    startInfo.ArgumentList.Add buildConfiguration
    startInfo.ArgumentList.Add "--no-build"
    startInfo.ArgumentList.Add "--"
    for arg in args do
        startInfo.ArgumentList.Add arg
    use child = Process.Start startInfo
    let stderr = child.StandardError.ReadToEnd()
    let stdout = child.StandardOutput.ReadToEnd()
    child.WaitForExit()
    child.ExitCode, stdout, stderr

let private kernelString (value: string) =
    "\"" + value.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\""

[<Fact>]
let ``script mode bootstraps the standard library`` () =
    let script = tempPath ".ikr"
    try
        File.WriteAllText(script, "((lambda (x) x) 42)")
        Assert.Equal(0, runOne script [])
    finally
        File.Delete(script)

[<Fact>]
let ``script mode reports evaluation failure through exit code`` () =
    let script = tempPath ".ikr"
    try
        File.WriteAllText(script, "(missing-combiner 42)")
        Assert.Equal(1, runOne script [])
    finally
        File.Delete(script)

[<Fact>]
let ``packaging validates but does not execute source`` () =
    let script = tempPath ".ikr"
    let package = tempPath ".ikc"
    let marker = tempPath ".txt"
    try
        let source =
            sprintf "(. System.IO.File WriteAllText %s \"executed\")" (kernelString marker)
        File.WriteAllText(script, source)

        match compileFileToPackage script package with
        | Choice1Of2 error -> failwithf "packaging failed: %A" error
        | Choice2Of2 _ -> ()

        Assert.False(File.Exists(marker), "packaging executed user code")

        match loadIkc package with
        | Choice1Of2 error -> failwithf "package execution failed: %A" error
        | Choice2Of2 _ -> ()

        Assert.Equal("executed", File.ReadAllText(marker))
    finally
        File.Delete(script)
        File.Delete(package)
        File.Delete(marker)

[<Fact>]
let ``package API requires honest ikc extension`` () =
    let script = tempPath ".ikr"
    let output = tempPath ".dll"
    try
        File.WriteAllText(script, "42")
        match compileFileToPackage script output with
        | Choice1Of2 _ -> ()
        | Choice2Of2 _ -> failwith "accepted a misleading .dll package name"
    finally
        File.Delete(script)
        File.Delete(output)

[<Fact>]
let ``managed artifact runs without Kernel source or runtime compilation`` () =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-managed-test-" + Guid.NewGuid().ToString("N"))
    let script = Path.Combine(root, "answer.ikr")
    let output = Path.Combine(root, "publish")
    Directory.CreateDirectory(root) |> ignore
    try
        File.WriteAllText(
            script,
            "(letrec ((sum (lambda (x) (if (zero? x) 0 (+ x (sum (- x 1))))))) (sum 5))")
        let artifact =
            match compileFileToManagedArtifact Minimal script output with
            | Choice1Of2 error -> failwith (showError error)
            | Choice2Of2 path -> path
        Assert.True(File.Exists artifact)
        Assert.Empty(Directory.GetFiles(output, "*.ikr", SearchOption.AllDirectories))
        Assert.True(File.Exists(Path.Combine(output, "IronKernel.Runtime.dll")))
        Assert.False(File.Exists(Path.Combine(output, "IronKernel.dll")))
        Assert.False(File.Exists(Path.Combine(output, "FParsec.dll")))

        let startInfo = ProcessStartInfo("dotnet")
        startInfo.UseShellExecute <- false
        startInfo.RedirectStandardError <- true
        startInfo.RedirectStandardOutput <- true
        startInfo.ArgumentList.Add artifact
        use child = Process.Start startInfo
        let stdout = child.StandardOutput.ReadToEnd()
        let stderr = child.StandardError.ReadToEnd()
        child.WaitForExit()
        Assert.Equal(0, child.ExitCode)
        Assert.Equal("<obj 15 : Int32>", stdout.Trim())
        Assert.Equal("", stderr.Trim())
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``managed artifact preserves exponent-form double literals`` () =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-managed-exponent-" + Guid.NewGuid().ToString("N"))
    let script = Path.Combine(root, "exponent.ikr")
    let output = Path.Combine(root, "publish")
    Directory.CreateDirectory(root) |> ignore
    try
        File.WriteAllText(script, "1e20")
        let artifact =
            match compileFileToManagedArtifact Minimal script output with
            | Choice1Of2 error -> failwith (showError error)
            | Choice2Of2 path -> path

        let startInfo = ProcessStartInfo("dotnet")
        startInfo.UseShellExecute <- false
        startInfo.RedirectStandardError <- true
        startInfo.RedirectStandardOutput <- true
        startInfo.ArgumentList.Add artifact
        use child = Process.Start startInfo
        let stdout = child.StandardOutput.ReadToEnd()
        let stderr = child.StandardError.ReadToEnd()
        child.WaitForExit()
        Assert.Equal(0, child.ExitCode)
        Assert.Equal("<obj 1E+20 : Double>", stdout.Trim())
        Assert.Equal("", stderr.Trim())
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``managed artifact supports definitions and lazy conditionals`` () =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-managed-control-flow-" + Guid.NewGuid().ToString("N"))
    let script = Path.Combine(root, "control-flow.ikr")
    let output = Path.Combine(root, "publish")
    Directory.CreateDirectory(root) |> ignore
    try
        File.WriteAllText(
            script,
            "(define answer 42)\n(if #t answer missing)\n"
            + "(define if (vau operands caller 99))\n(if #t missing missing)")
        let artifact =
            match compileFileToManagedArtifact Minimal script output with
            | Choice1Of2 error -> failwith (showError error)
            | Choice2Of2 path -> path

        let startInfo = ProcessStartInfo("dotnet")
        startInfo.UseShellExecute <- false
        startInfo.RedirectStandardError <- true
        startInfo.RedirectStandardOutput <- true
        startInfo.ArgumentList.Add artifact
        use child = Process.Start startInfo
        let stdout = child.StandardOutput.ReadToEnd()
        let stderr = child.StandardError.ReadToEnd()
        child.WaitForExit()
        Assert.Equal(0, child.ExitCode)
        Assert.Equal("<obj 99 : Int32>", stdout.Trim())
        Assert.Equal("", stderr.Trim())
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``managed artifact preserves selected branch diagnostics`` () =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-managed-diagnostics-" + Guid.NewGuid().ToString("N"))
    let script = Path.Combine(root, "diagnostics.ikr")
    let output = Path.Combine(root, "publish")
    Directory.CreateDirectory(root) |> ignore
    try
        File.WriteAllText(script, "(define answer 42)\n(if #f answer missing)")
        let artifact =
            match compileFileToManagedArtifact Minimal script output with
            | Choice1Of2 error -> failwith (showError error)
            | Choice2Of2 path -> path

        let startInfo = ProcessStartInfo("dotnet")
        startInfo.UseShellExecute <- false
        startInfo.RedirectStandardError <- true
        startInfo.RedirectStandardOutput <- true
        startInfo.ArgumentList.Add artifact
        use child = Process.Start startInfo
        let stdout = child.StandardOutput.ReadToEnd()
        let stderr = child.StandardError.ReadToEnd()
        child.WaitForExit()
        Assert.Equal(1, child.ExitCode)
        Assert.Equal("", stdout.Trim())
        Assert.Contains(script + ":2:15: Getting an unbound variable: 'missing'", stderr)
        Assert.Contains("(if #f answer missing)", stderr)
        Assert.Contains("              ^^^^^^^", stderr)
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``safe managed artifact excludes raw reflection`` () =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-managed-safe-" + Guid.NewGuid().ToString("N"))
    let script = Path.Combine(root, "safe.ikr")
    let output = Path.Combine(root, "publish")
    Directory.CreateDirectory(root) |> ignore
    try
        File.WriteAllText(script, "(. System.Guid NewGuid)")
        let artifact =
            match compileFileToManagedArtifact Safe script output with
            | Choice1Of2 error -> failwith (showError error)
            | Choice2Of2 path -> path

        let startInfo = ProcessStartInfo("dotnet")
        startInfo.UseShellExecute <- false
        startInfo.RedirectStandardError <- true
        startInfo.RedirectStandardOutput <- true
        startInfo.ArgumentList.Add artifact
        use child = Process.Start startInfo
        let stdout = child.StandardOutput.ReadToEnd()
        let stderr = child.StandardError.ReadToEnd()
        child.WaitForExit()
        Assert.Equal(1, child.ExitCode)
        Assert.Equal("", stdout.Trim())
        Assert.Contains("Getting an unbound variable: '.'", stderr)
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``compile managed CLI publishes a runnable assembly`` () =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-managed-cli-" + Guid.NewGuid().ToString("N"))
    let script = Path.Combine(root, "cli-answer.ikr")
    let output = Path.Combine(root, "publish")
    Directory.CreateDirectory(root) |> ignore
    try
        File.WriteAllText(script, "42")
        let exitCode, stdout, stderr =
            runCli ["--profile"; "minimal"; "compile"; script; "--managed"; "-o"; output]
        Assert.Equal(0, exitCode)
        Assert.Contains("cli-answer.dll", stdout)
        Assert.Equal("", stderr.Trim())
        Assert.True(File.Exists(Path.Combine(output, "cli-answer.dll")))
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``native artifacts validate profile and runtime identifier`` () =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-native-profile-" + Guid.NewGuid().ToString("N"))
    let script = Path.Combine(root, "profile.ikr")
    Directory.CreateDirectory(root) |> ignore
    try
        File.WriteAllText(script, "42")
        match compileFileToNativeArtifact Safe "" script (Path.Combine(root, "publish")) with
        | Choice1Of2 (Default message) -> Assert.Contains("requires a runtime identifier", message)
        | result -> failwithf "unexpected native RID result: %A" result
        match compileFileToNativeArtifact Unrestricted "osx-arm64" script (Path.Combine(root, "publish")) with
        | Choice1Of2 (Default message) -> Assert.Contains("minimal and safe profiles", message)
        | result -> failwithf "unexpected unrestricted native result: %A" result
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``native artifact runs without dotnet or Homebrew dylibs`` () =
    if OperatingSystem.IsMacOS() && RuntimeInformation.OSArchitecture = Architecture.Arm64 then
        let root = Path.Combine(Path.GetTempPath(), "ironkernel-native-test-" + Guid.NewGuid().ToString("N"))
        let script = Path.Combine(root, "native-answer.ikr")
        let output = Path.Combine(root, "publish")
        Directory.CreateDirectory(root) |> ignore
        try
            File.WriteAllText(script, "(String.concat \"Iron\" \"Kernel\")")
            let exitCode, compileOutput, compileError =
                runCli
                    [ "--profile"; "safe"; "compile"; script; "--native"; "osx-arm64"
                      "-o"; output ]
            Assert.Equal(0, exitCode)
            Assert.Equal("", compileError.Trim())
            let artifact = Path.Combine(output, "native-answer")
            Assert.Contains(artifact, compileOutput)
            Assert.True(File.Exists artifact)
            Assert.False(File.Exists(artifact + ".dll"))

            let runInfo = ProcessStartInfo(artifact)
            runInfo.UseShellExecute <- false
            runInfo.RedirectStandardError <- true
            runInfo.RedirectStandardOutput <- true
            use child = Process.Start runInfo
            let stdout = child.StandardOutput.ReadToEnd()
            let stderr = child.StandardError.ReadToEnd()
            child.WaitForExit()
            Assert.Equal(0, child.ExitCode)
            Assert.Equal("<obj IronKernel : String>", stdout.Trim())
            Assert.Equal("", stderr.Trim())

            let dependencyInfo = ProcessStartInfo("otool")
            dependencyInfo.UseShellExecute <- false
            dependencyInfo.RedirectStandardOutput <- true
            dependencyInfo.ArgumentList.Add "-L"
            dependencyInfo.ArgumentList.Add artifact
            use dependencies = Process.Start dependencyInfo
            let linkedLibraries = dependencies.StandardOutput.ReadToEnd()
            dependencies.WaitForExit()
            Assert.Equal(0, dependencies.ExitCode)
            Assert.DoesNotContain("/opt/homebrew", linkedLibraries)
            Assert.DoesNotContain("/usr/local/opt", linkedLibraries)
        finally
            Directory.Delete(root, true)

[<Fact>]
let ``truncated package returns a structured error`` () =
    let package = tempPath ".ikc"
    try
        File.WriteAllBytes(
            package,
            Array.concat
                [ Text.Encoding.ASCII.GetBytes("IKC2")
                  BitConverter.GetBytes(1) ])

        match loadIkc package with
        | Choice1Of2 _ -> ()
        | Choice2Of2 value -> failwithf "loaded truncated package as %A" value
    finally
        File.Delete(package)

[<Fact>]
let ``package rejects unknown Core tags`` () =
    let package = tempPath ".ikc"
    try
        File.WriteAllBytes(
            package,
            Array.concat
                [ Text.Encoding.ASCII.GetBytes("IKC2")
                  BitConverter.GetBytes(1)
                  [| 255uy |] ])

        match loadIkc package with
        | Choice1Of2 (Default message) -> Assert.Contains("Unknown IKC expression tag", message)
        | result -> failwithf "unexpected invalid-tag result: %A" result
    finally
        File.Delete(package)

[<Fact>]
let ``legacy source package requests rebuild`` () =
    let package = tempPath ".ikc"
    try
        File.WriteAllBytes(package, Text.Encoding.ASCII.GetBytes("IKC1"))
        match loadIkc package with
        | Choice1Of2 (Default message) -> Assert.Contains("rebuild the package as IKC2", message)
        | result -> failwithf "unexpected legacy package result: %A" result
    finally
        File.Delete(package)

[<Fact>]
let ``package diagnostics use the package path`` () =
    let source = tempPath ".ikr"
    let package = tempPath ".ikc"
    try
        File.WriteAllText(source, "(missing-combiner 42)")
        match compileFileToPackage source package with
        | Choice1Of2 error -> failwith (showError error)
        | Choice2Of2 _ ->
            match loadIkc package with
            | Choice2Of2 value -> failwithf "unexpected package result: %A" value
            | Choice1Of2 error ->
                let diagnostic = showError error
                Assert.Contains(package + ":1:", diagnostic)
                Assert.DoesNotContain(source + ":1:", diagnostic)
                Assert.Contains("(missing-combiner 42)", diagnostic)
    finally
        File.Delete(source)
        File.Delete(package)

[<Fact>]
let ``runtime diagnostics identify the failing operator`` () =
    match bootstrapEnv () with
    | Choice1Of2 error -> failwith (showError error)
    | Choice2Of2 env ->
        let source = "(define ready #t)\n(missing-combiner 42)"
        match runSource env "runtime-error.ikr" source with
        | Choice2Of2 value -> failwithf "unexpectedly returned %A" value
        | Choice1Of2 error ->
            let diagnostic = showError error
            Assert.Contains("runtime-error.ikr:2:2", diagnostic)
            Assert.Contains("(missing-combiner 42)", diagnostic)
            Assert.Contains(" ^^^^^^^^^^^^^^^^", diagnostic)

[<Fact>]
let ``runtime diagnostics prefer the nested operator span`` () =
    match bootstrapEnv () with
    | Choice1Of2 error -> failwith (showError error)
    | Choice2Of2 env ->
        let source = "(define ready #t)\n((missing-combiner) 42)"
        match runSource env "nested-runtime-error.ikr" source with
        | Choice2Of2 value -> failwithf "unexpectedly returned %A" value
        | Choice1Of2 error ->
            let diagnostic = showError error
            Assert.Contains("nested-runtime-error.ikr:2:3", diagnostic)
            Assert.Contains("((missing-combiner) 42)", diagnostic)
            Assert.Contains("  ^^^^^^^^^^^^^^^^", diagnostic)

[<Fact>]
let ``nested located errors render without overflowing`` () =
    let depth = 100_000
    let span =
        { sourceName = "deep.ikr"
          startPosition = { offset = 0L; line = 1L; column = 1L }
          endPosition = { offset = 0L; line = 1L; column = 2L } }
    let mutable error = Default "boom"
    for _ in 1..depth do
        error <- LocatedError(span, None, error)

    let diagnostic = showError error
    Assert.Equal(depth * 14 + 4, diagnostic.Length)
    Assert.StartsWith("deep.ikr:1:1: deep.ikr:1:1: ", diagnostic)
    Assert.EndsWith("boom", diagnostic)

    let nested =
        LocatedError(
            { span with sourceName = "outer.ikr" },
            Some "outer",
            LocatedError({ span with sourceName = "inner.ikr" }, Some "inner", Default "boom"))
    Assert.Equal(
        "outer.ikr:1:1: inner.ikr:1:1: boom\ninner\n^\nouter\n^",
        showError nested)

[<Fact>]
let ``runtime diagnostics identify the selected if branch`` () =
    match bootstrapEnv () with
    | Choice1Of2 error -> failwith (showError error)
    | Choice2Of2 env ->
        let source = "(if #t\n    missing\n    42)"
        match runSource env "if-branch-error.ikr" source with
        | Choice2Of2 value -> failwithf "unexpectedly returned %A" value
        | Choice1Of2 error ->
            let diagnostic = showError error
            Assert.Contains("if-branch-error.ikr:2:5", diagnostic)
            Assert.Contains("    missing", diagnostic)
            Assert.Contains("    ^^^^^^^", diagnostic)

[<Fact>]
let ``runtime diagnostics identify the define value`` () =
    match bootstrapEnv () with
    | Choice1Of2 error -> failwith (showError error)
    | Choice2Of2 env ->
        let source = "(define answer\n  missing)"
        match runSource env "define-value-error.ikr" source with
        | Choice2Of2 value -> failwithf "unexpectedly returned %A" value
        | Choice1Of2 error ->
            let diagnostic = showError error
            Assert.Contains("define-value-error.ikr:2:3", diagnostic)
            Assert.Contains("  missing", diagnostic)
            Assert.Contains("  ^^^^^^^", diagnostic)

[<Fact>]
let ``located guarded if does not evaluate the unused branch`` () =
    match bootstrapEnv () with
    | Choice1Of2 error -> failwith (showError error)
    | Choice2Of2 env ->
        match runSource env "if-lazy.ikr" "(if #t 42 missing)" with
        | Choice2Of2 (IronKernel.Ast.Obj value) -> Assert.Equal(42, value :?> int)
        | result -> failwithf "unexpected located if result: %A" result

[<Fact>]
let ``package validation reports named parse diagnostics`` () =
    let script = tempPath ".ikr"
    let package = tempPath ".ikc"
    try
        File.WriteAllText(script, "(define broken")
        match compileFileToPackage script package with
        | Choice2Of2 _ -> failwith "packaged invalid source"
        | Choice1Of2 error ->
            let diagnostic = showError error
            Assert.Contains(script + ":1:", diagnostic)
            Assert.Contains("(define broken", diagnostic)
            Assert.Contains("^", diagnostic)
    finally
        File.Delete(script)
        File.Delete(package)

[<Fact>]
let ``new with invalid kind reports project usage instead of running a script`` () =
    let exitCode, _, stderr = runCli [ "new"; "widget"; "demo" ]
    Assert.Equal(2, exitCode)
    Assert.Contains("Expected 'ik new <app|lib> <name>'", stderr)
    Assert.DoesNotContain("Getting an unbound variable", stderr)

[<Fact>]
let ``bare ikproj path runs the project instead of parsing XML as Kernel`` () =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-cli-" + Guid.NewGuid().ToString("N"))
    Directory.CreateDirectory(root) |> ignore
    try
        Assert.Equal(0, IronKernel.Project.create "app" "demo" root)
        let projectPath = Path.Combine(root, "demo", "demo.ikproj")
        let exitCode, _, stderr = runCli [ projectPath ]
        Assert.Equal(0, exitCode)
        Assert.DoesNotContain("Parser error", stderr)
        Assert.DoesNotContain("Getting an unbound variable", stderr)
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``run with non-source args forwards them to the discovered project`` () =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-cli-args-" + Guid.NewGuid().ToString("N"))
    Directory.CreateDirectory(root) |> ignore
    try
        Assert.Equal(0, IronKernel.Project.create "app" "demo" root)
        let projectDir = Path.Combine(root, "demo")
        File.WriteAllText(
            Path.Combine(projectDir, "src", "main.ikr"),
            "(if (eqv? (car args) \"--help\") #inert missing)\n")
        let startInfo = ProcessStartInfo("dotnet")
        startInfo.WorkingDirectory <- projectDir
        startInfo.UseShellExecute <- false
        startInfo.RedirectStandardError <- true
        startInfo.RedirectStandardOutput <- true
        startInfo.ArgumentList.Add "run"
        startInfo.ArgumentList.Add "--project"
        startInfo.ArgumentList.Add (Path.Combine(repoRoot, "IronKernel"))
        startInfo.ArgumentList.Add "-c"
        startInfo.ArgumentList.Add buildConfiguration
        startInfo.ArgumentList.Add "--no-build"
        startInfo.ArgumentList.Add "--"
        startInfo.ArgumentList.Add "run"
        startInfo.ArgumentList.Add "--help"
        use child = Process.Start startInfo
        let stderr = child.StandardError.ReadToEnd()
        child.WaitForExit()
        Assert.Equal(0, child.ExitCode)
        Assert.DoesNotContain("Unable to find file", stderr)
        Assert.DoesNotContain("Parser error", stderr)
    finally
        Directory.Delete(root, true)

/// Drives the REPL with stdin redirected, which is exactly the case the
/// Mono.Terminal line editor cannot handle.
let private runReplWithInput (input: string) =
    let startInfo = ProcessStartInfo("dotnet")
    startInfo.WorkingDirectory <- repoRoot
    startInfo.UseShellExecute <- false
    startInfo.RedirectStandardInput <- true
    startInfo.RedirectStandardError <- true
    startInfo.RedirectStandardOutput <- true
    startInfo.ArgumentList.Add "run"
    startInfo.ArgumentList.Add "--project"
    startInfo.ArgumentList.Add "IronKernel"
    startInfo.ArgumentList.Add "-c"
    startInfo.ArgumentList.Add buildConfiguration
    startInfo.ArgumentList.Add "--no-build"
    use child = Process.Start startInfo
    child.StandardInput.Write input
    child.StandardInput.Close()
    let stdout = child.StandardOutput.ReadToEnd()
    let stderr = child.StandardError.ReadToEnd()
    child.WaitForExit()
    child.ExitCode, stdout, stderr

[<Fact>]
let ``repl evaluates piped stdin without a tty`` () =
    let exitCode, stdout, stderr = runReplWithInput "(+ 1 2)\n(* 6 7)\nquit\n"
    Assert.Equal(0, exitCode)
    Assert.DoesNotContain("Unhandled exception", stderr)
    Assert.DoesNotContain("SetCursorPosition", stderr)
    Assert.DoesNotContain("DivideByZeroException", stderr)
    Assert.Contains("3", stdout)
    Assert.Contains("42", stdout)

[<Fact>]
let ``repl exits cleanly at end of piped input`` () =
    let exitCode, _, stderr = runReplWithInput "(+ 1 2)\n"
    Assert.Equal(0, exitCode)
    Assert.DoesNotContain("Unhandled exception", stderr)

[<Fact>]
let ``runtime diagnostics do not attribute operand errors to the operator`` () =
    // The operator is evaluated before the operands, and compiled code hands it
    // the caller's own continuation. Its span must stop at that hand-off, or it
    // swallows every later error and reports column 2 for the whole program.
    match bootstrapEnv () with
    | Choice1Of2 error -> failwith (showError error)
    | Choice2Of2 env ->
        match runSource env "operand-error.ikr" "(define ready #t)\n(+ 1 missing)" with
        | Choice2Of2 value -> failwithf "unexpectedly returned %A" value
        | Choice1Of2 error ->
            let diagnostic = showError error
            Assert.Contains("operand-error.ikr:2:1", diagnostic)
            Assert.Contains("^^^^^^^^^^^^^", diagnostic)

[<Fact>]
let ``runtime diagnostics keep the enclosing span for errors after an if condition`` () =
    match bootstrapEnv () with
    | Choice1Of2 error -> failwith (showError error)
    | Choice2Of2 env ->
        match runSource env "if-condition.ikr" "(if 5 1 2)" with
        | Choice2Of2 value -> failwithf "unexpectedly returned %A" value
        | Choice1Of2 error ->
            let diagnostic = showError error
            Assert.Contains("if-condition.ikr:1:1", diagnostic)
            Assert.Contains("^^^^^^^^^^", diagnostic)
