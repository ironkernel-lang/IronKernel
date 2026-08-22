module IronKernel.Tests.ProjectTests

open System
open System.IO
open System.IO.Compression
open Xunit

open IronKernel.Ast
open IronKernel.Errors
open IronKernel.Project

let private withProject body =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-project-" + Guid.NewGuid().ToString("N"))
    Directory.CreateDirectory(root) |> ignore
    try
        Assert.Equal(0, create "app" "demo" root)
        let projectPath = Path.Combine(root, "demo", "demo.ikproj")
        match load projectPath with
        | Choice1Of2 error -> failwithf "project load failed: %A" error
        | Choice2Of2 project -> body project
    finally
        Directory.Delete(root, true)

let private assetsOk project =
    match resolveAssets project with
    | Choice2Of2 assets -> assets
    | Choice1Of2 error -> failwithf "resolveAssets failed: %A" error

[<Fact>]
let ``new project loads runs tests and builds`` () =
    withProject (fun project ->
        Assert.EndsWith("src/main.ikr", project.main.Replace('\\', '/'))
        Assert.Equal(0, run project [])
        Assert.Equal(0, test project)
        Assert.Equal(0, build project)
        Assert.True(File.Exists(Path.Combine(project.outputPath, "demo.ikc"))))

[<Fact>]
let ``project package references can be added and removed`` () =
    withProject (fun project ->
        Assert.Equal(0, addPackage project.path "Example.Dependency" "1.2.3" "IronKernel" "runtime")
        let reloaded =
            match load project.path with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "reload failed: %A" error
        Assert.Contains(reloaded.packages, fun package ->
            package.id = "Example.Dependency"
            && package.version = "1.2.3"
            && package.kind = "IronKernel")
        Assert.Equal(0, removePackage project.path "Example.Dependency")
        let afterRemoval =
            match load project.path with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "reload failed: %A" error
        Assert.Empty(afterRemoval.packages))

[<Fact>]
let ``add and remove package treat package ids as case-insensitive`` () =
    withProject (fun project ->
        Assert.Equal(0, addPackage project.path "Example.Dependency" "1.2.3" "IronKernel" "runtime")
        Assert.Equal(1, addPackage project.path "example.dependency" "9.9.9" "IronKernel" "runtime")
        Assert.Equal(0, removePackage project.path "EXAMPLE.DEPENDENCY")
        let afterRemoval =
            match load project.path with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "reload failed: %A" error
        Assert.Empty(afterRemoval.packages))

[<Fact>]
let ``project restore creates NuGet assets and lock file`` () =
    withProject (fun project ->
        Assert.Equal(0, restore project false)
        Assert.True(File.Exists(Path.Combine(project.directory, "obj", "project.assets.json")))
        Assert.True(File.Exists(Path.Combine(project.directory, "packages.lock.json")))
        Assert.Equal(0, restore project true))

[<Fact>]
let ``project pack emits NuGet package with ikr sources`` () =
    withProject (fun project ->
        Assert.Equal(0, pack project)
        let package =
            Directory.GetFiles(Path.Combine(project.directory, "bin"), "*.nupkg")
            |> Array.exactlyOne
        use archive = ZipFile.OpenRead(package)
        Assert.Contains(archive.Entries, fun entry ->
            entry.FullName.EndsWith("main.ikr", StringComparison.Ordinal)))

let private withDependencyGraph body =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-deps-" + Guid.NewGuid().ToString("N"))
    Directory.CreateDirectory(root) |> ignore
    try
        Assert.Equal(0, create "lib" "shared" root)
        let shared =
            match load (Path.Combine(root, "shared", "shared.ikproj")) with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "shared load failed: %A" error
        File.WriteAllText(shared.main, "(define hello (lambda () \"from package\"))\n")
        Assert.Equal(0, pack shared)

        Assert.Equal(0, create "app" "consumer" root)
        let consumerPath = Path.Combine(root, "consumer", "consumer.ikproj")
        let consumer =
            match load consumerPath with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "consumer load failed: %A" error
        File.WriteAllText(
            consumer.main,
            "(if (eqv? (hello) \"from package\") #inert missing)\n")
        File.WriteAllText(
            Path.Combine(consumer.directory, "test", "main_test.ikr"),
            "(if (eqv? (hello) \"from package\") #inert missing)\n")
        Assert.Equal(0, addPackage consumer.path "shared" "0.1.0" "IronKernel" "runtime")

        let feed = Path.Combine(shared.directory, "bin")
        File.WriteAllText(
            Path.Combine(root, "NuGet.config"),
            $"""<?xml version="1.0" encoding="utf-8"?>
<configuration>
  <packageSources>
    <clear />
    <add key="local" value="{feed}" />
  </packageSources>
</configuration>
            """)
        let reloaded =
            match load consumer.path with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "consumer reload failed: %A" error
        body root shared reloaded
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``NuGet IronKernel dependency sources load before project main`` () =
    withDependencyGraph (fun _ _ consumer ->
        Assert.Equal(0, restore consumer false)
        Assert.NotEmpty((assetsOk consumer).sources)
        Assert.Equal(0, run consumer []))

/// A "testlib" package consumed with IronKernelScope="test": the consumer's main
/// does not need it, its test file does.
let private withTestScopedGraph body =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-testdeps-" + Guid.NewGuid().ToString("N"))
    Directory.CreateDirectory(root) |> ignore
    try
        Assert.Equal(0, create "lib" "testlib" root)
        let testlib =
            match load (Path.Combine(root, "testlib", "testlib.ikproj")) with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "testlib load failed: %A" error
        File.WriteAllText(
            testlib.main,
            "(define assert-true (lambda (x) (if x #inert (assertion-failed))))\n")
        Assert.Equal(0, pack testlib)

        Assert.Equal(0, create "app" "consumer" root)
        let consumerPath = Path.Combine(root, "consumer", "consumer.ikproj")
        File.WriteAllText(
            Path.Combine(root, "consumer", "src", "main.ikr"),
            "(define answer 42)\n")
        File.WriteAllText(
            Path.Combine(root, "consumer", "test", "main_test.ikr"),
            "(assert-true (eqv? answer 42))\n")
        Assert.Equal(0, addPackage consumerPath "testlib" "0.1.0" "IronKernel" "test")

        let feed = Path.Combine(testlib.directory, "bin")
        File.WriteAllText(
            Path.Combine(root, "NuGet.config"),
            $"""<?xml version="1.0" encoding="utf-8"?>
<configuration>
  <packageSources>
    <clear />
    <add key="local" value="{feed}" />
  </packageSources>
</configuration>
            """)
        let consumer =
            match load consumerPath with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "consumer load failed: %A" error
        body root testlib consumer
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``test-scoped dependencies load for ik test only`` () =
    withTestScopedGraph (fun _ _ consumer ->
        Assert.Equal(0, restore consumer false)
        let assets = assetsOk consumer
        Assert.Empty(assets.sources)
        Assert.NotEmpty(assets.testSources)
        // The test file can use the dependency's binding...
        Assert.Equal(0, test consumer)
        // ...but run does not load it: a main that needs it fails. This is the
        // negative control -- without the scope split, this run would succeed.
        File.WriteAllText(consumer.main, "(assert-true #t)\n")
        Assert.Equal(1, run consumer []))

[<Fact>]
let ``pack excludes test-scoped references from the package`` () =
    withTestScopedGraph (fun _ _ consumer ->
        Assert.Equal(0, restore consumer false)
        Assert.Equal(0, pack consumer)
        let generated =
            File.ReadAllText(Path.Combine(consumer.directory, "obj", consumer.name + ".pack.csproj"))
        Assert.DoesNotContain("testlib", generated))

[<Fact>]
let ``unknown IronKernelScope fails to load`` () =
    withProject (fun project ->
        Assert.Equal(0, addPackage project.path "Example.Dependency" "1.0.0" "IronKernel" "test")
        let text =
            File.ReadAllText(project.path)
                .Replace("IronKernelScope=\"test\"", "IronKernelScope=\"dev\"")
        File.WriteAllText(project.path, text)
        match load project.path with
        | Choice1Of2 (Default message) -> Assert.Contains("IronKernelScope", message)
        | Choice1Of2 other -> failwithf "unexpected error: %A" other
        | Choice2Of2 _ -> failwith "expected scope validation to fail the load")

[<Fact>]
let ``build concatenates dependency sources before main`` () =
    withProject (fun project ->
        File.WriteAllText(
            Path.Combine(project.directory, "src", "util.ikr"),
            "(define greeting \"ordered\")\n")
        File.WriteAllText(
            project.main,
            "(if (eqv? greeting \"ordered\") #inert missing)\n")
        let reloaded =
            match load project.path with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "reload failed: %A" error
        Assert.Equal(0, run reloaded [])
        Assert.Equal(0, build reloaded)
        let combined =
            File.ReadAllText(Path.Combine(reloaded.directory, "obj", reloaded.name + ".combined.ikr"))
        let helperIndex = combined.IndexOf("define greeting", StringComparison.Ordinal)
        let mainIndex = combined.IndexOf("eqv? greeting", StringComparison.Ordinal)
        Assert.True(helperIndex >= 0 && mainIndex > helperIndex))

[<Fact>]
let ``build and test restore NuGet dependencies like run`` () =
    withDependencyGraph (fun _ _ consumer ->
        Assert.False(File.Exists(Path.Combine(consumer.directory, "obj", "project.assets.json")))
        Assert.Equal(0, test consumer)
        Assert.True(File.Exists(Path.Combine(consumer.directory, "obj", "project.assets.json")))
        Directory.Delete(Path.Combine(consumer.directory, "obj"), true)
        Assert.Equal(0, build consumer)
        Assert.True(File.Exists(Path.Combine(consumer.outputPath, "consumer.ikc"))))

[<Fact>]
let ``ensureRestored refreshes stale assets after project changes`` () =
    withDependencyGraph (fun _ _ consumer ->
        Assert.Equal(0, restore consumer false)
        let assets = Path.Combine(consumer.directory, "obj", "project.assets.json")
        File.SetLastWriteTimeUtc(consumer.path, File.GetLastWriteTimeUtc(assets).AddMinutes(1.0))
        Assert.Equal(0, ensureRestored consumer)
        Assert.True(File.GetLastWriteTimeUtc assets >= File.GetLastWriteTimeUtc consumer.path)
        let stamp = File.GetLastWriteTimeUtc assets
        Assert.Equal(0, ensureRestored consumer)
        Assert.Equal(stamp, File.GetLastWriteTimeUtc assets))

[<Fact>]
let ``discover reports multiple projects instead of none`` () =
    let root = Path.Combine(Path.GetTempPath(), "ironkernel-discover-" + Guid.NewGuid().ToString("N"))
    Directory.CreateDirectory(root) |> ignore
    try
        File.WriteAllText(Path.Combine(root, "a.ikproj"), "<Project Sdk=\"Microsoft.NET.Sdk\" />")
        File.WriteAllText(Path.Combine(root, "b.ikproj"), "<Project Sdk=\"Microsoft.NET.Sdk\" />")
        match discover root with
        | MultipleProjects projects ->
            Assert.Equal(2, projects.Length)
            Assert.Contains(projects, fun path -> path.EndsWith("a.ikproj", StringComparison.Ordinal))
            Assert.Contains(projects, fun path -> path.EndsWith("b.ikproj", StringComparison.Ordinal))
        | other -> failwithf "expected MultipleProjects, got %A" other
        File.Delete(Path.Combine(root, "b.ikproj"))
        match discover root with
        | ProjectFound path -> Assert.EndsWith("a.ikproj", path)
        | other -> failwithf "expected ProjectFound, got %A" other
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``publish selects matching package id and version over lexical order`` () =
    withProject (fun project ->
        Directory.CreateDirectory(Path.Combine(project.directory, "bin")) |> ignore
        let older = Path.Combine(project.directory, "bin", "zzz.9.9.9.nupkg")
        let expected =
            Path.Combine(project.directory, "bin", sprintf "%s.%s.nupkg" project.name project.version)
        File.WriteAllText(older, "old")
        File.WriteAllText(expected, "new")
        File.SetLastWriteTimeUtc(older, DateTime.UtcNow.AddHours(1.0))
        File.SetLastWriteTimeUtc(expected, DateTime.UtcNow.AddHours(-1.0))
        match selectPackageForPublish project with
        | Some path -> Assert.Equal(expected, path)
        | None -> failwith "expected a package")

let private escapeJsonPath (path: string) =
    path.Replace("\\", "\\\\")

[<Fact>]
let ``resolveAssets searches all packageFolders`` () =
    withProject (fun project ->
        let objDir = Path.Combine(project.directory, "obj")
        Directory.CreateDirectory(objDir) |> ignore
        let emptyFolder = Path.Combine(project.directory, "empty-packages")
        let realFolder = Path.Combine(project.directory, "real-packages")
        Directory.CreateDirectory(emptyFolder) |> ignore
        let packageDir = Path.Combine(realFolder, "shared", "0.1.0")
        let sourceDir = Path.Combine(packageDir, "ironkernel", "src")
        Directory.CreateDirectory(sourceDir) |> ignore
        let sourcePath = Path.Combine(sourceDir, "main.ikr")
        File.WriteAllText(sourcePath, "(define hello (lambda () 1))\n")
        let assets =
            $"""{{
  "packageFolders": {{
    "{escapeJsonPath emptyFolder}/": {{}},
    "{escapeJsonPath realFolder}/": {{}}
  }},
  "libraries": {{
    "shared/0.1.0": {{
      "type": "package",
      "files": [ "ironkernel/src/main.ikr" ]
    }}
  }}
}}"""
        File.WriteAllText(Path.Combine(objDir, "project.assets.json"), assets)
        let resolved = assetsOk project
        Assert.Contains(resolved.sources, fun path ->
            Path.GetFullPath(path) = Path.GetFullPath(sourcePath)))

[<Fact>]
let ``resolveAssets loads runtime assemblies from the active TFM target`` () =
    withProject (fun project ->
        let objDir = Path.Combine(project.directory, "obj")
        Directory.CreateDirectory(objDir) |> ignore
        let packages = Path.Combine(project.directory, "packages")
        let packageDir = Path.Combine(packages, "clrlib", "1.0.0")
        let net10 = Path.Combine(packageDir, "lib", "net10.0")
        let netstandard = Path.Combine(packageDir, "lib", "netstandard2.0")
        Directory.CreateDirectory(net10) |> ignore
        Directory.CreateDirectory(netstandard) |> ignore
        let correctDll = Path.Combine(net10, "ClrLib.dll")
        let wrongDll = Path.Combine(netstandard, "ClrLib.dll")
        File.WriteAllText(correctDll, "net10")
        File.WriteAllText(wrongDll, "netstandard")
        let assets =
            $"""{{
  "packageFolders": {{
    "{escapeJsonPath packages}/": {{}}
  }},
  "targets": {{
    "net10.0": {{
      "clrlib/1.0.0": {{
        "type": "package",
        "runtime": {{
          "lib/net10.0/ClrLib.dll": {{}}
        }}
      }}
    }}
  }},
  "libraries": {{
    "clrlib/1.0.0": {{
      "type": "package",
      "files": [
        "lib/net10.0/ClrLib.dll",
        "lib/netstandard2.0/ClrLib.dll"
      ]
    }}
  }}
}}"""
        File.WriteAllText(Path.Combine(objDir, "project.assets.json"), assets)
        let resolved = assetsOk project
        Assert.Equal<string list>([ Path.GetFullPath correctDll ], resolved.assemblies |> List.map Path.GetFullPath)
        Assert.DoesNotContain(Path.GetFullPath wrongDll, resolved.assemblies |> List.map Path.GetFullPath))

[<Fact>]
let ``resolveAssets orders package sources by NuGet dependencies`` () =
    withProject (fun project ->
        let objDir = Path.Combine(project.directory, "obj")
        Directory.CreateDirectory(objDir) |> ignore
        let packages = Path.Combine(project.directory, "packages")
        let writePackage (id: string) (contents: string) =
            let sourceDir = Path.Combine(packages, id, "1.0.0", "ironkernel", "src")
            Directory.CreateDirectory(sourceDir) |> ignore
            let path = Path.Combine(sourceDir, "main.ikr")
            File.WriteAllText(path, contents)
            path
        // apple depends on zebra; alphabetical order would load apple first.
        let zebraPath = writePackage "zebra" "(define base 1)\n"
        let applePath = writePackage "apple" "(define uses-base base)\n"
        let assets =
            $"""{{
  "packageFolders": {{
    "{escapeJsonPath packages}/": {{}}
  }},
  "targets": {{
    "net10.0": {{
      "apple/1.0.0": {{
        "type": "package",
        "dependencies": {{ "zebra": "1.0.0" }}
      }},
      "zebra/1.0.0": {{
        "type": "package"
      }}
    }}
  }},
  "libraries": {{
    "apple/1.0.0": {{
      "type": "package",
      "files": [ "ironkernel/src/main.ikr" ]
    }},
    "zebra/1.0.0": {{
      "type": "package",
      "files": [ "ironkernel/src/main.ikr" ]
    }}
  }}
}}"""
        File.WriteAllText(Path.Combine(objDir, "project.assets.json"), assets)
        let resolved = assetsOk project
        let expected = [ Path.GetFullPath zebraPath; Path.GetFullPath applePath ]
        let actual = resolved.sources |> List.map Path.GetFullPath
        Assert.Equal<string list>(expected, actual))

[<Fact>]
let ``resolveAssets orders sources from preferred net10 TFM not first targets key`` () =
    withProject (fun project ->
        let objDir = Path.Combine(project.directory, "obj")
        Directory.CreateDirectory(objDir) |> ignore
        let packages = Path.Combine(project.directory, "packages")
        let writePackage (id: string) (contents: string) =
            let sourceDir = Path.Combine(packages, id, "1.0.0", "ironkernel", "src")
            Directory.CreateDirectory(sourceDir) |> ignore
            let path = Path.Combine(sourceDir, "main.ikr")
            File.WriteAllText(path, contents)
            path
        let zebraPath = writePackage "zebra" "(define base 1)\n"
        let applePath = writePackage "apple" "(define uses-base base)\n"
        // First targets key has no dependency edges; net10.0 does. Source order must follow net10.0.
        let assets =
            $"""{{
  "packageFolders": {{
    "{escapeJsonPath packages}/": {{}}
  }},
  "targets": {{
    "netstandard2.0": {{
      "apple/1.0.0": {{ "type": "package" }},
      "zebra/1.0.0": {{ "type": "package" }}
    }},
    "net10.0": {{
      "apple/1.0.0": {{
        "type": "package",
        "dependencies": {{ "zebra": "1.0.0" }}
      }},
      "zebra/1.0.0": {{ "type": "package" }}
    }}
  }},
  "libraries": {{
    "apple/1.0.0": {{
      "type": "package",
      "files": [ "ironkernel/src/main.ikr" ]
    }},
    "zebra/1.0.0": {{
      "type": "package",
      "files": [ "ironkernel/src/main.ikr" ]
    }}
  }}
}}"""
        File.WriteAllText(Path.Combine(objDir, "project.assets.json"), assets)
        let resolved = assetsOk project
        let expected = [ Path.GetFullPath zebraPath; Path.GetFullPath applePath ]
        let actual = resolved.sources |> List.map Path.GetFullPath
        Assert.Equal<string list>(expected, actual))

[<Fact>]
let ``parseProjectOptions finds project after flags`` () =
    let project, options =
        parseProjectOptions [ "--locked"; "demo.ikproj"; "--verbose" ]
    Assert.Equal(Some "demo.ikproj", project)
    Assert.Equal<string list>([ "--locked"; "--verbose" ], options)

[<Fact>]
let ``test loads IronKernelMain before test files`` () =
    withProject (fun project ->
        File.WriteAllText(project.main, "(define answer 42)\n")
        File.WriteAllText(
            Path.Combine(project.directory, "test", "main_test.ikr"),
            "(if (eqv? answer 42) #inert missing)\n")
        let reloaded =
            match load project.path with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "reload failed: %A" error
        Assert.Equal(0, test reloaded))

[<Fact>]
let ``ensureRestored clears assets after all packages are removed`` () =
    withDependencyGraph (fun _ _ consumer ->
        Assert.Equal(0, restore consumer false)
        Assert.NotEmpty((assetsOk consumer).sources)
        Assert.Equal(0, removePackage consumer.path "shared")
        let reloaded =
            match load consumer.path with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "reload failed: %A" error
        Assert.Empty(reloaded.packages)
        Assert.Equal(0, ensureRestored reloaded)
        Assert.Empty((assetsOk reloaded).sources))

[<Fact>]
let ``ensureRestored refreshes when packages lock file is newer`` () =
    withDependencyGraph (fun _ _ consumer ->
        Assert.Equal(0, restore consumer false)
        let assets = Path.Combine(consumer.directory, "obj", "project.assets.json")
        let lockFile = Path.Combine(consumer.directory, "packages.lock.json")
        Assert.True(File.Exists lockFile)
        File.SetLastWriteTimeUtc(lockFile, File.GetLastWriteTimeUtc(assets).AddMinutes(1.0))
        Assert.Equal(0, ensureRestored consumer)
        Assert.True(File.GetLastWriteTimeUtc assets >= File.GetLastWriteTimeUtc lockFile))

[<Fact>]
let ``project profile override is honored by run`` () =
    withProject (fun project ->
        // Safe profile still bootstraps; override must be applied on the project record.
        let safeProject = { project with profile = Safe }
        Assert.Equal(0, run safeProject []))

[<Fact>]
let ``load rejects unknown IronKernelProfile instead of defaulting to unrestricted`` () =
    withProject (fun project ->
        let text = File.ReadAllText project.path
        File.WriteAllText(
            project.path,
            text.Replace(
                "<IronKernelProfile>unrestricted</IronKernelProfile>",
                "<IronKernelProfile>unsrestricted</IronKernelProfile>"))
        match load project.path with
        | Choice2Of2 _ -> failwith "expected unknown profile to fail load"
        | Choice1Of2 (Default message) ->
            Assert.Contains("Unknown IronKernelProfile", message)
            Assert.Contains("unsrestricted", message)
        | Choice1Of2 other -> failwithf "unexpected error: %A" other)

[<Fact>]
let ``resolveAssets rejects empty packageFolders when project has packages`` () =
    withProject (fun project ->
        Assert.Equal(0, addPackage project.path "Example.Dependency" "1.0.0" "IronKernel" "runtime")
        let reloaded =
            match load project.path with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "reload failed: %A" error
        let objDir = Path.Combine(reloaded.directory, "obj")
        Directory.CreateDirectory(objDir) |> ignore
        File.WriteAllText(
            Path.Combine(objDir, "project.assets.json"),
            """{ "packageFolders": {}, "libraries": {} }""")
        match resolveAssets reloaded with
        | Choice2Of2 _ -> failwith "expected empty packageFolders to fail when packages exist"
        | Choice1Of2 (Default message) ->
            Assert.Contains("packageFolders", message)
        | Choice1Of2 other -> failwithf "unexpected error: %A" other)

[<Fact>]
let ``ensureRestored does not restore-loop on persistent assets errors`` () =
    withProject (fun project ->
        Assert.Equal(0, addPackage project.path "Example.Dependency" "1.0.0" "IronKernel" "runtime")
        let reloaded =
            match load project.path with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "reload failed: %A" error
        let objDir = Path.Combine(reloaded.directory, "obj")
        Directory.CreateDirectory(objDir) |> ignore
        let assets = Path.Combine(objDir, "project.assets.json")
        File.WriteAllText(assets, "{ \"packageFolders\": {")
        // Fresh broken assets: resolve fails, but ensureRestored must not keep invoking restore.
        File.SetLastWriteTimeUtc(assets, File.GetLastWriteTimeUtc(reloaded.path).AddMinutes(1.0))
        Assert.Equal(0, ensureRestored reloaded)
        let stamp = File.GetLastWriteTimeUtc assets
        Assert.Equal(0, ensureRestored reloaded)
        Assert.Equal(stamp, File.GetLastWriteTimeUtc assets)
        match resolveAssets reloaded with
        | Choice1Of2 (Default message) -> Assert.Contains("Invalid project.assets.json", message)
        | other -> failwithf "expected persistent assets error, got %A" other)

[<Fact>]
let ``ensureRestored restores once when packageFolders are empty and stale`` () =
    withDependencyGraph (fun _ _ consumer ->
        let assets = Path.Combine(consumer.directory, "obj", "project.assets.json")
        Directory.CreateDirectory(Path.GetDirectoryName assets) |> ignore
        File.WriteAllText(assets, """{ "packageFolders": {}, "libraries": {} }""")
        File.SetLastWriteTimeUtc(assets, File.GetLastWriteTimeUtc(consumer.path).AddMinutes(-1.0))
        Assert.Equal(0, ensureRestored consumer)
        match resolveAssets consumer with
        | Choice2Of2 resolved -> Assert.NotEmpty(resolved.sources)
        | Choice1Of2 error -> failwithf "expected restore to repair assets: %A" error
        let stamp = File.GetLastWriteTimeUtc assets
        Assert.Equal(0, ensureRestored consumer)
        Assert.Equal(stamp, File.GetLastWriteTimeUtc assets))

[<Fact>]
let ``orderedSources keeps IronKernelMain only once when path casing differs`` () =
    withProject (fun project ->
        let altMain =
            Path.Combine(
                Path.GetDirectoryName project.main,
                Path.GetFileName(project.main).ToUpperInvariant())
        let project' = { project with main = altMain; sources = [ project.main ] }
        let ordered = orderedSources project' { sources = []; assemblies = []; testSources = []; testAssemblies = [] }
        Assert.Equal(1, ordered.Length)
        Assert.True(
            String.Equals(ordered[0], altMain, StringComparison.OrdinalIgnoreCase)))

[<Fact>]
let ``test succeeds when sources list casing differs from IronKernelMain`` () =
    withProject (fun project ->
        let altMain =
            Path.Combine(
                Path.GetDirectoryName project.main,
                Path.GetFileName(project.main).ToUpperInvariant())
        File.WriteAllText(project.main, "(define answer 42)\n")
        File.WriteAllText(
            Path.Combine(project.directory, "test", "main_test.ikr"),
            "(if (eqv? answer 42) #inert missing)\n")
        // Only meaningful on case-insensitive filesystems where both paths resolve.
        if File.Exists altMain && not (String.Equals(altMain, project.main, StringComparison.Ordinal)) then
            let project' = { project with main = altMain; sources = [ project.main ] }
            Assert.Equal(0, test project'))

[<Fact>]
let ``tree restores stale assets after package changes`` () =
    withDependencyGraph (fun _ _ consumer ->
        Assert.Equal(0, restore consumer false)
        Assert.Equal(0, removePackage consumer.path "shared")
        let reloaded =
            match load consumer.path with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> failwithf "reload failed: %A" error
        Assert.Equal(0, tree reloaded)
        match resolveAssets reloaded with
        | Choice2Of2 assets -> Assert.Empty(assets.sources)
        | Choice1Of2 error -> failwithf "resolve after tree failed: %A" error)

[<Fact>]
let ``load deduplicates IronKernelMain against sources ignoring case`` () =
    withProject (fun project ->
        let text = File.ReadAllText project.path
        File.WriteAllText(
            project.path,
            text.Replace(
                "<IronKernelMain>src/main.ikr</IronKernelMain>",
                "<IronKernelMain>src/MAIN.ikr</IronKernelMain>"))
        match load project.path with
        | Choice1Of2 error ->
            // Case-sensitive filesystems reject MAIN.ikr when only main.ikr exists.
            Assert.Contains("does not exist", showError error)
        | Choice2Of2 loaded ->
            let mains =
                loaded.sources
                |> List.filter (fun path ->
                    String.Equals(path, loaded.main, StringComparison.OrdinalIgnoreCase))
            Assert.Equal(1, mains.Length)
            Assert.Equal(loaded.main, mains[0])
            let ordered = orderedSources loaded { sources = []; assemblies = []; testSources = []; testAssemblies = [] }
            Assert.Equal(1, ordered |> List.filter (fun path ->
                String.Equals(path, loaded.main, StringComparison.OrdinalIgnoreCase)) |> List.length))

[<Fact>]
let ``resolveAssets reports malformed assets instead of throwing`` () =
    withProject (fun project ->
        let objDir = Path.Combine(project.directory, "obj")
        Directory.CreateDirectory(objDir) |> ignore
        File.WriteAllText(Path.Combine(objDir, "project.assets.json"), "{ \"packageFolders\": {")
        match resolveAssets project with
        | Choice2Of2 _ -> failwith "expected malformed assets to fail"
        | Choice1Of2 (Default message) ->
            Assert.Contains("Invalid project.assets.json", message)
        | Choice1Of2 other -> failwithf "unexpected error: %A" other)

[<Fact>]
let ``resolveAssets reports missing libraries instead of throwing`` () =
    withProject (fun project ->
        let objDir = Path.Combine(project.directory, "obj")
        Directory.CreateDirectory(objDir) |> ignore
        let packages = Path.Combine(project.directory, "packages")
        Directory.CreateDirectory(packages) |> ignore
        File.WriteAllText(
            Path.Combine(objDir, "project.assets.json"),
            $"""{{ "packageFolders": {{ "{escapeJsonPath packages}/": {{}} }} }}""")
        match resolveAssets project with
        | Choice2Of2 _ -> failwith "expected missing libraries to fail"
        | Choice1Of2 (Default message) ->
            Assert.Contains("missing libraries", message)
        | Choice1Of2 other -> failwithf "unexpected error: %A" other)

[<Fact>]
let ``tree reports invalid assets with nonzero exit code`` () =
    withProject (fun project ->
        let objDir = Path.Combine(project.directory, "obj")
        Directory.CreateDirectory(objDir) |> ignore
        File.WriteAllText(Path.Combine(objDir, "project.assets.json"), "not-json")
        Assert.Equal(1, tree project))

[<Fact>]
let ``resolveAssets keeps dependency order when TFM omits prerequisite package node`` () =
    withProject (fun project ->
        let objDir = Path.Combine(project.directory, "obj")
        Directory.CreateDirectory(objDir) |> ignore
        let packages = Path.Combine(project.directory, "packages")
        let writePackage (id: string) (contents: string) =
            let sourceDir = Path.Combine(packages, id, "1.0.0", "ironkernel", "src")
            Directory.CreateDirectory(sourceDir) |> ignore
            let path = Path.Combine(sourceDir, "main.ikr")
            File.WriteAllText(path, contents)
            path
        let zebraPath = writePackage "zebra" "(define base 1)\n"
        let applePath = writePackage "apple" "(define uses-base base)\n"
        // apple lists zebra as a dependency, but zebra is absent from targets.
        // Old code dropped that edge and alphabetically placed apple before zebra.
        let assets =
            $"""{{
  "packageFolders": {{
    "{escapeJsonPath packages}/": {{}}
  }},
  "targets": {{
    "net10.0": {{
      "apple/1.0.0": {{
        "type": "package",
        "dependencies": {{ "zebra": "1.0.0" }}
      }}
    }}
  }},
  "libraries": {{
    "apple/1.0.0": {{
      "type": "package",
      "files": [ "ironkernel/src/main.ikr" ]
    }},
    "zebra/1.0.0": {{
      "type": "package",
      "files": [ "ironkernel/src/main.ikr" ]
    }}
  }}
}}"""
        File.WriteAllText(Path.Combine(objDir, "project.assets.json"), assets)
        let resolved = assetsOk project
        let expected = [ Path.GetFullPath zebraPath; Path.GetFullPath applePath ]
        let actual = resolved.sources |> List.map Path.GetFullPath
        Assert.Equal<string list>(expected, actual))

[<Fact>]
let ``resolveAssets breaks dependency cycles without alphabetical dump`` () =
    withProject (fun project ->
        let objDir = Path.Combine(project.directory, "obj")
        Directory.CreateDirectory(objDir) |> ignore
        let packages = Path.Combine(project.directory, "packages")
        let writePackage (id: string) (contents: string) =
            let sourceDir = Path.Combine(packages, id, "1.0.0", "ironkernel", "src")
            Directory.CreateDirectory(sourceDir) |> ignore
            let path = Path.Combine(sourceDir, "main.ikr")
            File.WriteAllText(path, contents)
            path
        let zebraPath = writePackage "zebra" "(define from-zebra 1)\n"
        let applePath = writePackage "apple" "(define from-apple 1)\n"
        // Mutual dependencies: alphabetical dump would force apple before zebra.
        // Cycle break should prefer original libraries encounter order (apple, then zebra).
        let assets =
            $"""{{
  "packageFolders": {{
    "{escapeJsonPath packages}/": {{}}
  }},
  "targets": {{
    "net10.0": {{
      "apple/1.0.0": {{
        "type": "package",
        "dependencies": {{ "zebra": "1.0.0" }}
      }},
      "zebra/1.0.0": {{
        "type": "package",
        "dependencies": {{ "apple": "1.0.0" }}
      }}
    }}
  }},
  "libraries": {{
    "apple/1.0.0": {{
      "type": "package",
      "files": [ "ironkernel/src/main.ikr" ]
    }},
    "zebra/1.0.0": {{
      "type": "package",
      "files": [ "ironkernel/src/main.ikr" ]
    }}
  }}
}}"""
        File.WriteAllText(Path.Combine(objDir, "project.assets.json"), assets)
        let resolved = assetsOk project
        let actual = resolved.sources |> List.map Path.GetFullPath
        // Both packages appear exactly once; order follows libraries key order on tie.
        Assert.Equal(2, actual.Length)
        Assert.Equal(Path.GetFullPath applePath, actual[0])
        Assert.Equal(Path.GetFullPath zebraPath, actual[1]))
