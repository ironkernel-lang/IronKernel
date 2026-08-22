open System
open System.IO
open IronKernel.Repl
open IronKernel.Emit
open IronKernel.StaticEmit
open IronKernel.Ast
open IronKernel.Errors

module ProjectTool = IronKernel.Project

let private usage =
    """Usage:
  ironkernel [--profile <profile>]                         Start the REPL
  ironkernel [--profile <profile>] <file.ikr> [args...]    Run a source script
  ironkernel [--profile <profile>] run <file> [args...]    Run a .ikr script or .ikc package
    ironkernel [--profile <profile>] compile <file.ikr> [-o <file.ikc>]
    ironkernel [--profile <profile>] compile <file.ikr> --managed [-o <directory>]
    ironkernel --profile <minimal|safe> compile <file.ikr> --native <rid> [-o <directory>]
  ironkernel --help
  ironkernel --version

Profiles: minimal, safe, unrestricted (default)

Project commands:
  ik new <app|lib> <name>
  ik restore [--locked] [project.ikproj]
  ik run [project.ikproj] [args...]
  ik build|test|tree|pack [project.ikproj]
  ik add <package> <version> [--clr] [--test]
  ik remove <package>
  ik publish <source> [api-key]
  ik doctor"""

let private usageError message =
    eprintfn "%s\n\n%s" message usage
    2

let private runPackage profile (path: string) (args: string list) =
    match loadIkcWithArgsForProfile profile path args with
    | Choice1Of2 error ->
        eprintfn "Package error: %s" (showError error)
        1
    | Choice2Of2 Inert -> 0
    | Choice2Of2 value ->
        printfn "%s" (showVal value)
        0

let private runPath profile (path: string) (args: string list) =
    let extension = Path.GetExtension(path)
    if String.Equals(extension, ".scm", StringComparison.OrdinalIgnoreCase) then
        eprintfn "Warning: .scm source is deprecated; rename this file to .ikr."
    if String.Equals(extension, ".ikc", StringComparison.OrdinalIgnoreCase) then
        runPackage profile path args
    else
        runOneWithProfile profile path args

let private parseProfile = function
    | "minimal" -> Choice2Of2 Minimal
    | "safe" -> Choice2Of2 Safe
    | "unrestricted" -> Choice2Of2 Unrestricted
    | value -> Choice1Of2 ("Unknown capability profile: " + value)

let private parseGlobalOptions args =
    match args with
    | "--profile" :: value :: rest ->
        match parseProfile value with
        | Choice1Of2 error -> Choice1Of2 error
        | Choice2Of2 profile -> Choice2Of2(Some profile, rest)
    | "--profile" :: [] -> Choice1Of2 "Missing value for --profile."
    | rest -> Choice2Of2(None, rest)

let private isProjectPath (path: string) =
    Path.GetExtension(path).Equals(".ikproj", StringComparison.OrdinalIgnoreCase)

let private isRunnableSource (path: string) =
    let extension = Path.GetExtension(path)
    [ ".ikr"; ".ikc"; ".scm" ]
    |> List.exists (fun candidate -> extension.Equals(candidate, StringComparison.OrdinalIgnoreCase))

let private withProject (profileOverride: CapabilityProfile option) explicitPath action =
    let discovery =
        match explicitPath with
        | Some value -> ProjectTool.ProjectFound value
        | None -> ProjectTool.discover (Directory.GetCurrentDirectory())
    match discovery with
    | ProjectTool.NoProjectFound ->
        eprintfn "No .ikproj file found."
        2
    | ProjectTool.MultipleProjects projects ->
        eprintfn "Multiple .ikproj files found; specify one explicitly:"
        projects
        |> List.iter (fun path -> eprintfn "  %s" path)
        2
    | ProjectTool.ProjectFound path ->
        match ProjectTool.load path with
        | Choice1Of2 error ->
            eprintfn "Project error: %s" (showError error)
            2
        | Choice2Of2 project ->
            let project =
                match profileOverride with
                | Some profile -> { project with profile = profile }
                | None -> project
            action project

let private dispatch (profileOverride: CapabilityProfile option) args =
    let profile = defaultArg profileOverride Unrestricted
    match args with
    | [] -> runReplWithProfile profile ()
    | ["--help"] | ["-h"] | ["help"] ->
        printfn "%s" usage
        0
    | ["--version"] | ["-V"] ->
        printfn "IronKernel %s" version
        0
    | ["new"; kind; name] when kind = "app" || kind = "lib" ->
        ProjectTool.create kind name (Directory.GetCurrentDirectory())
    | "new" :: _ ->
        usageError "Expected 'ik new <app|lib> <name>'."
    | "restore" :: rest ->
        let projectPath, options = ProjectTool.parseProjectOptions rest
        let locked = List.contains "--locked" options
        withProject profileOverride projectPath (fun project -> ProjectTool.restore project locked)
    | ["build"] -> withProject profileOverride None ProjectTool.build
    | ["test"] -> withProject profileOverride None ProjectTool.test
    | ["tree"] -> withProject profileOverride None ProjectTool.tree
    | ["pack"] -> withProject profileOverride None ProjectTool.pack
    | "build" :: [projectPath]
    | "test" :: [projectPath]
    | "tree" :: [projectPath]
    | "pack" :: [projectPath] ->
        let action =
            match args.Head with
            | "build" -> ProjectTool.build
            | "test" -> ProjectTool.test
            | "tree" -> ProjectTool.tree
            | _ -> ProjectTool.pack
        withProject profileOverride (Some projectPath) action
    | "add" :: id :: version :: flags when
        flags |> List.forall (fun flag -> flag = "--clr" || flag = "--test") ->
        let kind = if List.contains "--clr" flags then "Clr" else "IronKernel"
        let scope = if List.contains "--test" flags then "test" else "runtime"
        withProject profileOverride None (fun project -> ProjectTool.addPackage project.path id version kind scope)
    | ["remove"; id] ->
        withProject profileOverride None (fun project -> ProjectTool.removePackage project.path id)
    | ["publish"; source] ->
        let apiKey = Environment.GetEnvironmentVariable("NUGET_API_KEY")
        if String.IsNullOrWhiteSpace apiKey then usageError "Set NUGET_API_KEY before publishing."
        else withProject profileOverride None (fun project -> ProjectTool.publish project source apiKey)
    | ["publish"; source; apiKey] ->
        withProject profileOverride None (fun project -> ProjectTool.publish project source apiKey)
    | ["doctor"] -> ProjectTool.doctor ()
    | "run" :: path :: scriptArgs when isProjectPath path ->
        withProject profileOverride (Some path) (fun project -> ProjectTool.run project scriptArgs)
    | "run" :: path :: scriptArgs when isRunnableSource path ->
        runPath profile path scriptArgs
    | "run" :: scriptArgs ->
        // Non-source tokens (including flags) are project program args, not scripts.
        withProject profileOverride None (fun project -> ProjectTool.run project scriptArgs)
    | ["compile"] -> usageError "Missing source file for 'compile'."
    | "compile" :: input :: "--native" :: rid :: rest ->
        let outputResult =
            match rest with
            | [] -> Choice2Of2(Path.GetFileNameWithoutExtension(input) + "-" + rid)
            | ["-o"; path] | ["--output"; path] -> Choice2Of2 path
            | _ -> Choice1Of2 "Expected only '-o <directory>' after '--native <rid>'."
        match outputResult with
        | Choice1Of2 message -> usageError message
        | Choice2Of2 output ->
            match compileFileToNativeArtifact profile rid input output with
            | Choice2Of2 path ->
                printfn "Wrote %s" path
                0
            | Choice1Of2 error ->
                eprintfn "Compile error: %s" (showError error)
                1
    | "compile" :: input :: "--managed" :: rest ->
        let outputResult =
            match rest with
            | [] -> Choice2Of2(Path.GetFileNameWithoutExtension(input) + "-managed")
            | ["-o"; path] | ["--output"; path] -> Choice2Of2 path
            | _ -> Choice1Of2 "Expected only '-o <directory>' after '--managed'."
        match outputResult with
        | Choice1Of2 message -> usageError message
        | Choice2Of2 output ->
            match compileFileToManagedArtifact profile input output with
            | Choice2Of2 path ->
                printfn "Wrote %s" path
                0
            | Choice1Of2 error ->
                eprintfn "Compile error: %s" (showError error)
                1
    | "compile" :: input :: rest ->
        let outputResult =
            match rest with
            | [] -> Choice2Of2 (defaultPackagePath input)
            | ["-o"; path] | ["--output"; path] -> Choice2Of2 path
            | _ -> Choice1Of2 "Expected only '-o <file.ikc>' after the source file."
        match outputResult with
        | Choice1Of2 message -> usageError message
        | Choice2Of2 output ->
            match compileFileToPackageForProfile profile input output with
            | Choice2Of2 path ->
                printfn "Wrote %s" path
                0
            | Choice1Of2 err ->
                eprintfn "Compile error: %s" (showError err)
                1
    | option :: _ when option.StartsWith("-") ->
        usageError ("Unknown option: " + option)
    | path :: scriptArgs when isProjectPath path ->
        withProject profileOverride (Some path) (fun project -> ProjectTool.run project scriptArgs)
    | filename :: scriptArgs -> runPath profile filename scriptArgs

[<EntryPoint>]
let main argv =
    match parseGlobalOptions (Array.toList argv) with
    | Choice1Of2 error -> usageError error
    | Choice2Of2 (profileOverride, args) -> dispatch profileOverride args
