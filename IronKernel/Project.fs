namespace IronKernel

module Project =

    open System
    open System.Diagnostics
    open System.IO
    open System.IO.Compression
    open System.Reflection
    open System.Runtime.Loader
    open System.Text.Json
    open System.Xml.Linq

    open Ast
    open Emit
    open Errors
    open Runtime
    open SymbolTable

    type PackageReference = {
        id : string
        version : string
        kind : string
        /// "runtime" (the default) or "test". A test-scoped reference restores and
        /// loads for `ik test` only: `ik run`/`ik build` ignore it, and `ik pack`
        /// leaves it out of the published package's dependencies.
        scope : string
    }

    type IkProject = {
        path : string
        directory : string
        name : string
        version : string
        main : string
        profile : CapabilityProfile
        sources : string list
        tests : string list
        packages : PackageReference list
        outputPath : string
    }

    type ResolvedAssets = {
        sources : string list
        assemblies : string list
        /// Sources and assemblies reachable only through test-scoped references,
        /// in the same topological order. Loaded by `ik test`, never by run/build.
        testSources : string list
        testAssemblies : string list
    }

    type ProjectDiscovery =
        | ProjectFound of string
        | NoProjectFound
        | MultipleProjects of string list

    let private descendants name (document: XDocument) =
        document.Descendants(XName.Get name)

    let private property name fallback (document: XDocument) =
        descendants name document
        |> Seq.tryHead
        |> Option.map _.Value
        |> Option.filter (String.IsNullOrWhiteSpace >> not)
        |> Option.defaultValue fallback

    let private parseProfile = function
        | "minimal" -> Some Minimal
        | "safe" -> Some Safe
        | "unrestricted" -> Some Unrestricted
        | _ -> None

    let private pathsEqual (left: string) (right: string) =
        String.Equals(left, right, StringComparison.OrdinalIgnoreCase)

    let private packageIdsEqual (left: string) (right: string) =
        String.Equals(left, right, StringComparison.OrdinalIgnoreCase)

    let private expandInclude projectDirectory (includeValue: string) =
        let normalized = includeValue.Replace('\\', '/')
        if normalized.Contains("**") then
            let prefix = normalized.Substring(0, normalized.IndexOf("**", StringComparison.Ordinal))
            let root = Path.GetFullPath(Path.Combine(projectDirectory, prefix))
            if Directory.Exists root then
                Directory.GetFiles(root, "*.ikr", SearchOption.AllDirectories)
                |> Array.sort
                |> Array.toList
            else []
        elif normalized.Contains("*") then
            let directory =
                Path.GetDirectoryName normalized
                |> fun value -> if String.IsNullOrEmpty value then projectDirectory else Path.Combine(projectDirectory, value)
            let pattern = Path.GetFileName normalized
            if Directory.Exists directory then
                Directory.GetFiles(directory, pattern, SearchOption.TopDirectoryOnly)
                |> Array.sort
                |> Array.toList
            else []
        else [Path.GetFullPath(Path.Combine(projectDirectory, includeValue))]

    let load projectPath =
        try
            let fullPath = Path.GetFullPath projectPath
            let directory = Path.GetDirectoryName fullPath
            let document = XDocument.Load fullPath
            let root = document.Root
            if obj.ReferenceEquals(root, null) || root.Name.LocalName <> "Project" then
                Choice1Of2 (Default "An .ikproj file must have a Project root element")
            else
                let sdk = root.Attribute(XName.Get "Sdk")
                if obj.ReferenceEquals(sdk, null)
                   || not (
                       sdk.Value.StartsWith("IronKernel.Sdk/", StringComparison.Ordinal)
                       || sdk.Value = "Microsoft.NET.Sdk") then
                    Choice1Of2 (Default "Project Sdk must be IronKernel.Sdk/<version> or Microsoft.NET.Sdk")
                else
                    let itemPaths itemName =
                        descendants itemName document
                        |> Seq.choose (fun element ->
                            let includeAttribute = element.Attribute(XName.Get "Include")
                            if obj.ReferenceEquals(includeAttribute, null) then None else Some includeAttribute.Value)
                        |> Seq.collect (expandInclude directory)
                        |> Seq.distinct
                        |> Seq.toList
                    let packages =
                        descendants "PackageReference" document
                        |> Seq.choose (fun element ->
                            let includeAttribute = element.Attribute(XName.Get "Include")
                            let versionAttribute = element.Attribute(XName.Get "Version")
                            if obj.ReferenceEquals(includeAttribute, null)
                               || obj.ReferenceEquals(versionAttribute, null) then None
                            else
                                let kindAttribute = element.Attribute(XName.Get "IronKernelKind")
                                let scopeAttribute = element.Attribute(XName.Get "IronKernelScope")
                                Some
                                    { id = includeAttribute.Value
                                      version = versionAttribute.Value
                                      kind = if obj.ReferenceEquals(kindAttribute, null) then "IronKernel" else kindAttribute.Value
                                      scope = if obj.ReferenceEquals(scopeAttribute, null) then "runtime" else scopeAttribute.Value })
                        |> Seq.toList
                    let invalidScopes =
                        packages
                        |> List.filter (fun package -> package.scope <> "runtime" && package.scope <> "test")
                    let name = property "PackageId" (Path.GetFileNameWithoutExtension fullPath) document
                    let mainRelative = property "IronKernelMain" "src/main.ikr" document
                    let mainPath = Path.GetFullPath(Path.Combine(directory, mainRelative))
                    let sources = itemPaths "IronKernelSource"
                    // Prefer the globbed path casing when it refers to the same file as IronKernelMain.
                    let main =
                        sources
                        |> List.tryFind (pathsEqual mainPath)
                        |> Option.defaultValue mainPath
                    let sources =
                        if sources |> List.exists (pathsEqual main) then sources else sources @ [main]
                    let profileName = property "IronKernelProfile" "unrestricted" document
                    if invalidScopes <> [] then
                        Choice1Of2(
                            Default(
                                sprintf
                                    "Unknown IronKernelScope '%s' on package '%s'; expected runtime or test"
                                    invalidScopes.Head.scope
                                    invalidScopes.Head.id))
                    elif not (File.Exists main) then
                        Choice1Of2 (Default("Project main source does not exist: " + main))
                    else
                        match parseProfile profileName with
                        | None ->
                            Choice1Of2(
                                Default(
                                    sprintf
                                        "Unknown IronKernelProfile '%s'; expected minimal, safe, or unrestricted"
                                        profileName))
                        | Some profile ->
                            Choice2Of2
                                { path = fullPath
                                  directory = directory
                                  name = name
                                  version = property "Version" "0.1.0" document
                                  main = main
                                  profile = profile
                                  sources = sources
                                  tests = itemPaths "IronKernelTest"
                                  packages = packages
                                  outputPath =
                                    property "OutputPath" "bin" document
                                    |> fun value -> Path.GetFullPath(Path.Combine(directory, value)) }
        with ex ->
            Choice1Of2 (Default("Unable to load project: " + ex.Message))

    /// Pull an optional .ikproj path from anywhere in the argument list; remaining tokens are flags.
    let parseProjectOptions (arguments: string list) =
        let isProjectPath (arg: string) =
            Path.GetExtension(arg).Equals(".ikproj", StringComparison.OrdinalIgnoreCase)
        let projectPath = arguments |> List.tryFind isProjectPath
        let options = arguments |> List.filter (isProjectPath >> not)
        projectPath, options

    let discover startDirectory =
        let rec search directory =
            if not (Directory.Exists directory) then
                let parent = Directory.GetParent directory
                if obj.ReferenceEquals(parent, null) then NoProjectFound
                else search parent.FullName
            else
                let projects =
                    Directory.GetFiles(directory, "*.ikproj")
                    |> Array.sort
                    |> Array.toList
                match projects with
                | [project] -> ProjectFound project
                | [] ->
                    let parent = Directory.GetParent directory
                    if obj.ReferenceEquals(parent, null) then NoProjectFound
                    else search parent.FullName
                | many -> MultipleProjects many
        search (Path.GetFullPath startDirectory)

    let private runProcess command arguments workingDirectory =
        let startInfo = ProcessStartInfo(command)
        startInfo.WorkingDirectory <- workingDirectory
        startInfo.UseShellExecute <- false
        for argument in arguments do
            startInfo.ArgumentList.Add argument
        use childProcess = Process.Start startInfo
        childProcess.WaitForExit()
        childProcess.ExitCode

    let restore project locked =
        let args =
            [ "restore"; project.path; "--use-lock-file" ]
            @ (if locked then ["--locked-mode"] else [])
        runProcess "dotnet" args project.directory

    let private assetsPath project =
        Path.Combine(project.directory, "obj", "project.assets.json")

    let private lockFilePath project =
        Path.Combine(project.directory, "packages.lock.json")

    let private assetsAreStale project =
        let path = assetsPath project
        let lockPath = lockFilePath project
        not (File.Exists path)
        || File.GetLastWriteTimeUtc project.path > File.GetLastWriteTimeUtc path
        || (File.Exists lockPath
            && File.GetLastWriteTimeUtc lockPath > File.GetLastWriteTimeUtc path)

    let private packageIdFromLibraryName (libraryName: string) =
        match libraryName.IndexOf('/') with
        | index when index > 0 -> libraryName.Substring(0, index).ToLowerInvariant()
        | _ -> libraryName.ToLowerInvariant()

    let private selectTargetFramework (targets: JsonElement) =
        let frameworks = targets.EnumerateObject() |> Seq.toList
        frameworks
        |> List.tryFind (fun framework ->
            framework.Name.IndexOf("net10.0", StringComparison.OrdinalIgnoreCase) >= 0)
        |> Option.orElse (List.tryHead frameworks)

    let private dependencyIds (libraryValue: JsonElement) =
        match libraryValue.TryGetProperty("dependencies") with
        | true, deps ->
            deps.EnumerateObject()
            |> Seq.map (fun dep -> dep.Name.ToLowerInvariant())
            |> Seq.toList
        | _ -> []

    /// Order libraries so NuGet dependencies load before their dependents for one TFM graph.
    /// Uses libraryNames for package-id resolution so sources outside the TFM node list still
    /// honor edges. Cycles break by fewest remaining prereqs, then original libraryNames order.
    let private topologicalLibraryOrder (targetLibraries: JsonElement option) libraryNames =
        if libraryNames = [] then []
        else
            let indexByName =
                libraryNames
                |> List.mapi (fun index name -> name, index)
                |> Map.ofList
            let idToLibrary =
                libraryNames
                |> List.groupBy packageIdFromLibraryName
                |> Map.ofList
            let depsByLibrary =
                match targetLibraries with
                | None -> Map.empty
                | Some tfm ->
                    let librarySet = Set.ofList libraryNames
                    tfm.EnumerateObject()
                    |> Seq.choose (fun lib ->
                        if librarySet.Contains lib.Name then
                            Some(lib.Name, dependencyIds lib.Value)
                        else None)
                    |> Map.ofSeq
            let prerequisites =
                libraryNames
                |> List.map (fun name ->
                    let prereqs =
                        Map.tryFind name depsByLibrary
                        |> Option.defaultValue []
                        |> List.collect (fun depId ->
                            Map.tryFind depId idToLibrary |> Option.defaultValue [])
                        |> List.distinct
                        |> List.filter ((<>) name)
                    name, set prereqs)
            let rec sort remaining acc =
                match remaining with
                | [] -> List.rev acc
                | _ ->
                    let ready =
                        remaining
                        |> List.filter (fun (_, prereqs) ->
                            prereqs
                            |> Set.forall (fun prerequisite -> List.contains prerequisite acc))
                    let pick =
                        match ready with
                        | _ :: _ ->
                            ready
                            |> List.minBy (fun (name, _) -> Map.find name indexByName)
                            |> fst
                        | [] ->
                            // Cycle / unsatisfied edge: never dump alphabetically.
                            remaining
                            |> List.minBy (fun (name, prereqs) ->
                                let unsatisfied =
                                    prereqs
                                    |> Set.filter (fun prerequisite ->
                                        not (List.contains prerequisite acc)
                                        && List.exists (fun (n, _) -> n = prerequisite) remaining)
                                    |> Set.count
                                unsatisfied, Map.find name indexByName)
                            |> fst
                    sort (List.filter (fun (n, _) -> n <> pick) remaining) (pick :: acc)
            sort prerequisites []

    let private assetPathsFromGroup (group: JsonElement) =
        group.EnumerateObject()
        |> Seq.map _.Name
        |> Seq.filter (fun relative ->
            relative.EndsWith(".dll", StringComparison.OrdinalIgnoreCase)
            && not (relative.Contains("/ref/", StringComparison.OrdinalIgnoreCase))
            && not (relative.EndsWith("/_._", StringComparison.Ordinal))
            && relative <> "_._")
        |> Seq.toList

    /// Runtime assemblies for the active TFM come from targets, not the flat libraries.files list.
    let private runtimeAssembliesFromTarget (packageDirectory: string) (libraryValue: JsonElement) =
        let relatives =
            match libraryValue.TryGetProperty("runtime") with
            | true, group -> assetPathsFromGroup group
            | _ -> []
            |> fun runtime ->
                if runtime <> [] then runtime
                else
                    match libraryValue.TryGetProperty("compile") with
                    | true, group -> assetPathsFromGroup group
                    | _ -> []
        relatives
        |> List.choose (fun relative ->
            let fullPath =
                Path.Combine(packageDirectory, relative.Replace('/', Path.DirectorySeparatorChar))
            if File.Exists fullPath then Some fullPath else None)

    let private assetsError message =
        Choice1Of2(Default message)

    let resolveAssets project : ThrowsError<ResolvedAssets> =
        let path = assetsPath project
        if not (File.Exists path) then
            Choice2Of2 { sources = []; assemblies = []; testSources = []; testAssemblies = [] }
        else
            try
                use document = JsonDocument.Parse(File.ReadAllText path)
                let root = document.RootElement
                let packageFolders =
                    match root.TryGetProperty("packageFolders") with
                    | true, folders when folders.ValueKind = JsonValueKind.Object ->
                        folders.EnumerateObject()
                        |> Seq.map _.Name
                        |> Seq.toList
                    | true, _ ->
                        raise (JsonException "packageFolders must be an object")
                    | _ -> []
                let packageDirectoryFor (libraryName: string) =
                    let relative = libraryName.ToLowerInvariant()
                    packageFolders
                    |> List.tryPick (fun folder ->
                        let candidate = Path.Combine(folder, relative)
                        if Directory.Exists candidate then Some candidate else None)
                if packageFolders = [] then
                    // Declared PackageReferences require NuGet packageFolders; empty means incomplete assets.
                    if project.packages <> [] then
                        assetsError
                            "Invalid project.assets.json: missing or empty packageFolders. Run 'ik restore'."
                    else
                        Choice2Of2 { sources = []; assemblies = []; testSources = []; testAssemblies = [] }
                else
                    match root.TryGetProperty("libraries") with
                    | false, _ -> assetsError "Invalid project.assets.json: missing libraries."
                    | true, libraries when libraries.ValueKind <> JsonValueKind.Object ->
                        assetsError "Invalid project.assets.json: libraries must be an object."
                    | true, libraries ->
                        let sourceMap =
                            libraries.EnumerateObject()
                            |> Seq.choose (fun library ->
                                let value = library.Value
                                let libraryType =
                                    match value.TryGetProperty("type") with
                                    | true, typeValue -> typeValue.GetString()
                                    | _ -> null
                                if libraryType <> "package" then None
                                else
                                    match packageDirectoryFor library.Name with
                                    | None -> None
                                    | Some packageDirectory ->
                                        let files =
                                            match value.TryGetProperty("files") with
                                            | true, values when values.ValueKind = JsonValueKind.Array ->
                                                values.EnumerateArray()
                                                |> Seq.choose (fun item ->
                                                    if item.ValueKind = JsonValueKind.String then
                                                        Some(item.GetString())
                                                    else None)
                                                |> Seq.toList
                                            | _ -> []
                                        let sources =
                                            files
                                            |> List.choose (fun relative ->
                                                if relative.StartsWith("ironkernel/src/", StringComparison.Ordinal)
                                                   && relative.EndsWith(".ikr", StringComparison.OrdinalIgnoreCase) then
                                                    let fullPath =
                                                        Path.Combine(
                                                            packageDirectory,
                                                            relative.Replace('/', Path.DirectorySeparatorChar))
                                                    if File.Exists fullPath then Some(relative, fullPath) else None
                                                else None)
                                            |> List.sortBy fst
                                            |> List.map snd
                                        if sources = [] then None else Some(library.Name, sources))
                            |> Map.ofSeq
                        let selectedTarget =
                            match root.TryGetProperty("targets") with
                            | true, targets when targets.ValueKind = JsonValueKind.Object ->
                                selectTargetFramework targets
                            | _ -> None
                        let assemblyMap =
                            match selectedTarget with
                            | None -> Map.empty
                            | Some framework ->
                                framework.Value.EnumerateObject()
                                |> Seq.choose (fun library ->
                                    match packageDirectoryFor library.Name with
                                    | None -> None
                                    | Some packageDirectory ->
                                        let assemblies =
                                            runtimeAssembliesFromTarget packageDirectory library.Value
                                        if assemblies = [] then None
                                        else Some(library.Name, assemblies))
                                |> Map.ofSeq
                        let libraryNames =
                            [ yield! (sourceMap |> Map.toList |> List.map fst)
                              yield! (assemblyMap |> Map.toList |> List.map fst) ]
                            |> List.distinct
                        let order =
                            topologicalLibraryOrder
                                (selectedTarget |> Option.map _.Value)
                                libraryNames
                        // Partition into runtime and test-only libraries. A library is
                        // runtime when it is reachable from a runtime-scoped project
                        // reference through the dependency graph; anything else came in
                        // only through test-scoped references. Projects with no
                        // test-scoped reference keep everything runtime, whatever the
                        // graph says, so existing projects cannot change behaviour.
                        let runtimeReachable =
                            if project.packages |> List.forall (fun p -> p.scope <> "test") then
                                order |> List.map packageIdFromLibraryName |> Set.ofList
                            else
                                let dependenciesById =
                                    match selectedTarget with
                                    | None -> Map.empty
                                    | Some framework ->
                                        framework.Value.EnumerateObject()
                                        |> Seq.fold (fun acc library ->
                                            let id = packageIdFromLibraryName library.Name
                                            let existing = Map.tryFind id acc |> Option.defaultValue []
                                            Map.add id (existing @ dependencyIds library.Value) acc) Map.empty
                                let roots =
                                    project.packages
                                    |> List.filter (fun p -> p.scope <> "test")
                                    |> List.map (fun p -> p.id.ToLowerInvariant())
                                let rec closure visited = function
                                    | [] -> visited
                                    | id :: rest when Set.contains id visited -> closure visited rest
                                    | id :: rest ->
                                        let deps = Map.tryFind id dependenciesById |> Option.defaultValue []
                                        closure (Set.add id visited) (deps @ rest)
                                closure Set.empty roots
                        let runtimeOrder, testOrder =
                            order
                            |> List.partition (fun name ->
                                Set.contains (packageIdFromLibraryName name) runtimeReachable)
                        let collect names =
                            names
                            |> List.fold (fun (sourceAcc, assemblyAcc) name ->
                                let sources = Map.tryFind name sourceMap |> Option.defaultValue []
                                let assemblies = Map.tryFind name assemblyMap |> Option.defaultValue []
                                sourceAcc @ sources, assemblyAcc @ assemblies) ([], [])
                        let sources, assemblies = collect runtimeOrder
                        let testSources, testAssemblies = collect testOrder
                        Choice2Of2
                            { sources = sources
                              assemblies = List.distinct assemblies
                              testSources = testSources
                              testAssemblies = List.distinct testAssemblies }
            with
            | :? JsonException as ex ->
                assetsError ("Invalid project.assets.json: " + ex.Message)
            | ex ->
                assetsError ("Unable to read project.assets.json: " + ex.Message)

    /// Prefer locked restore for CI when the lock file is at least as new as the project file.
    let private shouldUseLockedRestore project =
        let lockPath = lockFilePath project
        File.Exists lockPath
        && File.GetLastWriteTimeUtc project.path <= File.GetLastWriteTimeUtc lockPath

    let private touchAssetsMarker project (path: string) =
        let candidates =
            [ DateTime.UtcNow; File.GetLastWriteTimeUtc project.path ]
            @ if File.Exists(lockFilePath project) then
                  [ File.GetLastWriteTimeUtc(lockFilePath project) ]
              else
                  []
        File.SetLastWriteTimeUtc(path, List.max candidates)

    let private packageFoldersMissingOrEmpty (assetsFile: string) =
        try
            use document = JsonDocument.Parse(File.ReadAllText assetsFile)
            match document.RootElement.TryGetProperty("packageFolders") with
            | true, folders when folders.ValueKind = JsonValueKind.Object ->
                folders.EnumerateObject() |> Seq.isEmpty
            | _ -> true
        with _ ->
            true

    /// Restore when assets are missing/stale, or still expose packages after references were removed.
    /// Persistent resolve failures are not retried forever; callers surface them via resolveAssets.
    let ensureRestored project =
        let path = assetsPath project
        let locked = shouldUseLockedRestore project
        let needsRestore =
            if not (File.Exists path) then
                project.packages <> []
            elif assetsAreStale project then
                true
            elif project.packages <> []
                 && packageFoldersMissingOrEmpty path
                 && File.GetLastWriteTimeUtc path < File.GetLastWriteTimeUtc project.path then
                // Incomplete assets older than the project still need a restore.
                true
            else
                match resolveAssets project with
                | Choice1Of2 _ ->
                    // Do not restore-loop on persistent assets errors.
                    false
                | Choice2Of2 assets when project.packages = [] ->
                    assets.sources <> [] || assets.assemblies <> []
                | Choice2Of2 _ -> false
        if not needsRestore then 0
        else
            let exitCode = restore project locked
            if exitCode <> 0 then exitCode
            elif not (File.Exists path) then
                if project.packages = [] then 0 else 1
            else
                match resolveAssets project with
                | Choice2Of2 _ ->
                    // Restore can be a no-op for an unchanged graph; advance the marker so we do not loop.
                    touchAssetsMarker project path
                    0
                | Choice1Of2 error ->
                    // Leave mtime unchanged when assets remain unusable so we do not mask failure
                    // as a successful restore; callers will surface the same resolve error.
                    eprintfn "Project error: %s" (showError error)
                    1

    let private loadAssemblies paths =
        let failures =
            paths
            |> List.choose (fun path ->
                try
                    AssemblyLoadContext.Default.LoadFromAssemblyPath(Path.GetFullPath path) |> ignore
                    None
                with ex ->
                    eprintfn "Failed to load assembly '%s': %s" path ex.Message
                    Some path)
        failures = []

    let private runFiles env files =
        files
        |> List.fold (fun state path ->
            match state with
            | Choice1Of2 _ -> state
            | Choice2Of2 _ -> runSourceFile env path) (Choice2Of2 Inert)

    /// Dependency sources, then project sources excluding main, then main last.
    let orderedSources (project: IkProject) (assets: ResolvedAssets) =
        let projectSources =
            project.sources |> List.filter (fun path -> not (pathsEqual path project.main))
        assets.sources @ projectSources @ [project.main]

    /// The same, with test-scoped dependency sources after the runtime ones --
    /// a test dependency may use a runtime dependency, never the other way round.
    let orderedTestSources (project: IkProject) (assets: ResolvedAssets) =
        let projectSources =
            project.sources |> List.filter (fun path -> not (pathsEqual path project.main))
        assets.sources @ assets.testSources @ projectSources @ [project.main]

    let private withResolvedAssets project action =
        match resolveAssets project with
        | Choice1Of2 error ->
            eprintfn "Project error: %s" (showError error)
            1
        | Choice2Of2 assets -> action assets

    let run project args =
        match ensureRestored project with
        | exitCode when exitCode <> 0 -> exitCode
        | _ ->
            withResolvedAssets project (fun assets ->
                if not (loadAssemblies assets.assemblies) then 1
                else
                    match bootstrapEnvForProfile project.profile with
                    | Choice1Of2 error ->
                        eprintfn "Startup error: %s" (showError error)
                        1
                    | Choice2Of2 standardEnv ->
                        let env =
                            bindVars standardEnv
                                [ "args", ofList(List.map (fun arg -> Obj(arg :> obj)) args) ]
                        match runFiles env (orderedSources project assets) with
                        | Choice1Of2 error ->
                            eprintfn "Project error: %s" (showError error)
                            1
                        | Choice2Of2 _ -> 0)

    let test project =
        match ensureRestored project with
        | exitCode when exitCode <> 0 -> exitCode
        | _ ->
            withResolvedAssets project (fun assets ->
                if not (loadAssemblies (assets.assemblies @ assets.testAssemblies)) then 1
                else
                    project.tests
                    |> List.fold (fun failures testFile ->
                        match bootstrapEnvForProfile project.profile with
                        | Choice1Of2 error ->
                            eprintfn "Test startup error: %s" (showError error)
                            failures + 1
                        | Choice2Of2 env ->
                            match runFiles env (orderedTestSources project assets @ [testFile]) with
                            | Choice1Of2 error ->
                                eprintfn "FAIL %s\n%s" testFile (showError error)
                                failures + 1
                            | Choice2Of2 _ ->
                                printfn "PASS %s" testFile
                                failures) 0
                    |> fun failures -> if failures = 0 then 0 else 1)

    let build project =
        match ensureRestored project with
        | exitCode when exitCode <> 0 -> exitCode
        | _ ->
            withResolvedAssets project (fun assets ->
                Directory.CreateDirectory project.outputPath |> ignore
                let objectDirectory = Path.Combine(project.directory, "obj")
                Directory.CreateDirectory objectDirectory |> ignore
                let combinedPath = Path.Combine(objectDirectory, project.name + ".combined.ikr")
                let source =
                    orderedSources project assets
                    |> List.map File.ReadAllText
                    |> String.concat Environment.NewLine
                File.WriteAllText(combinedPath, source)
                let output = Path.Combine(project.outputPath, project.name + ".ikc")
                match compileFileToPackageForProfile project.profile combinedPath output with
                | Choice1Of2 error ->
                    eprintfn "Build error: %s" (showError error)
                    1
                | Choice2Of2 path ->
                    printfn "Wrote %s" path
                    0)

    let private projectXml name =
        $"""<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework>
    <EnableDefaultCompileItems>false</EnableDefaultCompileItems>
    <RestorePackagesWithLockFile>true</RestorePackagesWithLockFile>
    <PackageId>{name}</PackageId>
    <Version>0.1.0</Version>
    <Authors>TODO</Authors>
    <Description>IronKernel project</Description>
    <PackageTags>ironkernel</PackageTags>
    <IronKernelMain>src/main.ikr</IronKernelMain>
    <IronKernelProfile>unrestricted</IronKernelProfile>
  </PropertyGroup>
  <ItemGroup>
    <IronKernelSource Include="src/**/*.ikr" />
    <IronKernelTest Include="test/**/*.ikr" />
  </ItemGroup>
</Project>
"""

    let create kind name parentDirectory =
        try
            let directory = Path.Combine(parentDirectory, name)
            if Directory.Exists directory then
                eprintfn "Directory already exists: %s" directory
                1
            else
                Directory.CreateDirectory(Path.Combine(directory, "src")) |> ignore
                Directory.CreateDirectory(Path.Combine(directory, "test")) |> ignore
                File.WriteAllText(Path.Combine(directory, name + ".ikproj"), projectXml name)
                let main =
                    if kind = "lib" then
                        "(provide! (hello)\n  (define hello (lambda () \"hello\")))\n"
                    else
                        "(Console.write-line \"Hello from IronKernel!\")\n"
                File.WriteAllText(Path.Combine(directory, "src", "main.ikr"), main)
                File.WriteAllText(Path.Combine(directory, "test", "main_test.ikr"), "(if #t #inert missing)\n")
                File.WriteAllText(Path.Combine(directory, ".gitignore"), "bin/\nobj/\n*.ikc\n")
                File.WriteAllText(
                    Path.Combine(directory, "README.md"),
                    "# " + name + "\n\nAn IronKernel " + kind + " project.\n")
                printfn "Created %s" directory
                0
        with ex ->
            eprintfn "Unable to create project: %s" ex.Message
            1

    let private saveDocument (path: string) (document: XDocument) =
        use writer =
            System.Xml.XmlWriter.Create(
                path,
                System.Xml.XmlWriterSettings(Indent = true))
        document.Save writer

    let addPackage (projectPath: string) id version kind scope =
        let document = XDocument.Load projectPath
        let existing =
            descendants "PackageReference" document
            |> Seq.tryFind (fun element ->
                let attribute = element.Attribute(XName.Get "Include")
                not (obj.ReferenceEquals(attribute, null))
                && packageIdsEqual attribute.Value id)
        match existing with
        | Some _ ->
            eprintfn "Package already referenced: %s" id
            1
        | None ->
            let group =
                document.Root.Elements(XName.Get "ItemGroup")
                |> Seq.tryHead
                |> Option.defaultWith (fun () ->
                    let value = XElement(XName.Get "ItemGroup")
                    document.Root.Add value
                    value)
            let reference =
                XElement(
                    XName.Get "PackageReference",
                    XAttribute(XName.Get "Include", id),
                    XAttribute(XName.Get "Version", version),
                    XAttribute(XName.Get "IronKernelKind", kind))
            if scope = "test" then
                reference.Add(XAttribute(XName.Get "IronKernelScope", "test"))
            group.Add reference
            saveDocument projectPath document
            printfn "Added %s %s%s" id version (if scope = "test" then " (test)" else "")
            0

    let removePackage (projectPath: string) id =
        let document = XDocument.Load projectPath
        let matches =
            descendants "PackageReference" document
            |> Seq.filter (fun element ->
                let attribute = element.Attribute(XName.Get "Include")
                not (obj.ReferenceEquals(attribute, null))
                && packageIdsEqual attribute.Value id)
            |> Seq.toList
        matches |> List.iter _.Remove()
        saveDocument projectPath document
        if matches = [] then
            eprintfn "Package not found: %s" id
            1
        else
            printfn "Removed %s" id
            0

    let tree project =
        match ensureRestored project with
        | exitCode when exitCode <> 0 -> exitCode
        | _ ->
            let path = assetsPath project
            if not (File.Exists path) then
                eprintfn "Run 'ik restore' first."
                1
            else
                try
                    use document = JsonDocument.Parse(File.ReadAllText path)
                    match document.RootElement.TryGetProperty("libraries") with
                    | false, _ ->
                        eprintfn "Invalid project.assets.json: missing libraries."
                        1
                    | true, libraries when libraries.ValueKind <> JsonValueKind.Object ->
                        eprintfn "Invalid project.assets.json: libraries must be an object."
                        1
                    | true, libraries ->
                        libraries.EnumerateObject()
                        |> Seq.map _.Name
                        |> Seq.sort
                        |> Seq.iter (printfn "%s")
                        0
                with
                | :? JsonException as ex ->
                    eprintfn "Invalid project.assets.json: %s" ex.Message
                    1
                | ex ->
                    eprintfn "Unable to read project.assets.json: %s" ex.Message
                    1

    let pack project =
        let objectDirectory = Path.Combine(project.directory, "obj")
        let outputDirectory = Path.Combine(project.directory, "bin")
        Directory.CreateDirectory objectDirectory |> ignore
        Directory.CreateDirectory outputDirectory |> ignore
        let generatedProject = Path.Combine(objectDirectory, project.name + ".pack.csproj")
        let manifestPath = Path.Combine(objectDirectory, "ironkernel.package.json")
        let readmePath = Path.Combine(project.directory, "README.md")
        if not (File.Exists readmePath) then
            File.WriteAllText(readmePath, "# " + project.name + Environment.NewLine)
        let mainRelative = Path.GetRelativePath(project.directory, project.main).Replace('\\', '/')
        let manifest =
            JsonSerializer.Serialize(
                {| schemaVersion = 1
                   name = project.name
                   version = project.version
                   entry = mainRelative
                   profile = project.profile.ToString().ToLowerInvariant() |},
                JsonSerializerOptions(WriteIndented = true))
        File.WriteAllText(manifestPath, manifest)
        let packageItems =
            project.sources
            |> List.map (fun source ->
                let relative = Path.GetRelativePath(project.directory, source).Replace('\\', '/')
                let packageRelative =
                    if relative.StartsWith("src/", StringComparison.Ordinal) then
                        relative.Substring(4)
                    else relative
                sprintf "    <None Include=\"%s\" Pack=\"true\" PackagePath=\"ironkernel/src/%s\" />" source packageRelative)
            |> String.concat Environment.NewLine
        let references =
            project.packages
            // Test-scoped references are a build-time concern; a consumer of the
            // published package must not inherit them.
            |> List.filter (fun package -> package.scope <> "test")
            |> List.map (fun package ->
                sprintf "    <PackageReference Include=\"%s\" Version=\"%s\" />" package.id package.version)
            |> String.concat Environment.NewLine
        let generated =
            $"""<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework>
    <EnableDefaultCompileItems>false</EnableDefaultCompileItems>
    <IncludeBuildOutput>false</IncludeBuildOutput>
    <PackageId>{project.name}</PackageId>
    <Version>{project.version}</Version>
    <Authors>IronKernel</Authors>
    <Description>IronKernel source package</Description>
    <PackageTags>ironkernel</PackageTags>
    <PackageReadmeFile>README.md</PackageReadmeFile>
    <NoWarn>NU5128</NoWarn>
  </PropertyGroup>
  <ItemGroup>
{packageItems}
    <None Include="{manifestPath}" Pack="true" PackagePath="ironkernel/package.json" />
    <None Include="{readmePath}" Pack="true" PackagePath="" />
{references}
  </ItemGroup>
</Project>
"""
        File.WriteAllText(generatedProject, generated)
        runProcess "dotnet" ["pack"; generatedProject; "-o"; outputDirectory] project.directory

    let selectPackageForPublish project =
        let outputDirectory = Path.Combine(project.directory, "bin")
        if not (Directory.Exists outputDirectory) then None
        else
            let packages = Directory.GetFiles(outputDirectory, "*.nupkg")
            let expectedName = sprintf "%s.%s.nupkg" project.name project.version
            packages
            |> Array.tryFind (fun path ->
                String.Equals(Path.GetFileName path, expectedName, StringComparison.OrdinalIgnoreCase))
            |> Option.orElseWith (fun () ->
                packages
                |> Array.sortByDescending File.GetLastWriteTimeUtc
                |> Array.tryHead)

    let publish project source apiKey =
        match selectPackageForPublish project with
        | None ->
            eprintfn "No package found. Run 'ik pack' first."
            1
        | Some package ->
            runProcess
                "dotnet"
                [ "nuget"; "push"; package; "--source"; source; "--api-key"; apiKey ]
                project.directory

    let doctor () =
        printfn "IronKernel project doctor"
        let dotnetExit = runProcess "dotnet" ["--version"] (Directory.GetCurrentDirectory())
        let stdlib =
            [ "kernel.ikr"; "promises.ikr" ]
            |> List.forall (fun name ->
                File.Exists name || File.Exists(Path.Combine(AppContext.BaseDirectory, name)))
        printfn "stdlib: %s" (if stdlib then "ok" else "missing")
        if dotnetExit = 0 && stdlib then 0 else 1
