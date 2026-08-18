namespace IronKernel

/// Emits Kernel programs to CLR packages and runs compiled forms.
module Emit =

    open System
    open System.IO
    open Ast
    open Errors
    open Runtime
    open SymbolTable
    open Compiler
    open Choice
    open Eval

    /// R-1RK 7.2.6: an abnormal pass reached root-continuation, so the session ends.
    /// The signal travels the error channel and picks up source locations on the way
    /// out like any other, so the wrappers are stripped to find it.
    let rec private sessionExit error =
        match error with
        | SessionExit value -> Some value
        | LocatedError(_, _, inner) -> sessionExit inner
        | _ -> None

    let runCompiledForms (env: LispVal) (forms: KernelFunc list) : ThrowsError<LispVal> =
        let cont = newContinuation env
        let rec loop (fs: KernelFunc list) (last: LispVal) =
            match fs with
            | [] -> returnM last
            | f :: rest ->
                match run (f.Invoke(env, cont)) with
                | Choice1Of2 e ->
                    // Reaching root-continuation ends the session, so the remaining
                    // forms are not run and the value is not an error.
                    match sessionExit e with
                    | Some value -> returnM value
                    | None -> throwError e
                | Choice2Of2 v -> loop rest v
        loop forms Inert

    let runLocatedForms (env: LispVal) (forms: LocatedKernelFunc list) : ThrowsError<LispVal> =
        let cont = newContinuation env
        let rec loop remaining last =
            match remaining with
            | [] -> returnM last
            | form :: rest ->
                match run (form.func.Invoke(env, cont)) with
                | Choice1Of2 error when (sessionExit error).IsSome ->
                    returnM (sessionExit error).Value
                | Choice1Of2 (LocatedError _ as error) -> throwError error
                | Choice1Of2 error ->
                    throwError (LocatedError(form.span, form.sourceLine, error))
                | Choice2Of2 value -> loop rest value
        loop forms Inert

    let compileSource (source: string) : ThrowsError<KernelFunc list> =
        analyzeAndCompile source

    let compileSourceLocated env sourceName source =
        analyzeAndCompileLocated env sourceName source

    let private readSource (path: string) : ThrowsError<string> =
        try
            returnM (File.ReadAllText path)
        with ex -> throwError (Default ("Failed to read '" + path + "': " + ex.Message))

    let compileFile (path: string) : ThrowsError<KernelFunc list> =
        match readSource path with
        | Choice1Of2 e -> throwError e
        | Choice2Of2 source ->
            let env = makePrimitiveBindings ()
            match compileSourceLocated env path source with
            | Choice1Of2 e -> throwError e
            | Choice2Of2 forms -> forms |> List.map (fun form -> form.func) |> returnM

    let runSource (env: LispVal) sourceName source =
        match compileSourceLocated env sourceName source with
        | Choice1Of2 e -> throwError e
        | Choice2Of2 forms -> runLocatedForms env forms

    let runSourceFile (env: LispVal) path =
        match readSource path with
        | Choice1Of2 e -> throwError e
        | Choice2Of2 source -> runSource env path source

    let private writeIkcPackage (outputPath: string) expressions : ThrowsError<string> =
        try
            use fs = File.Create outputPath
            CorePackage.write fs expressions
            returnM outputPath
        with ex ->
            throwError (Default ("Failed to write '" + outputPath + "': " + ex.Message))

    let private analyzePackage env sourceName source =
        match Parser.readLocatedExprList sourceName source with
        | Choice1Of2 error -> throwError error
        | Choice2Of2 forms ->
            forms
            |> List.map (Analyze.analyzeLocatedGuarded env source)
            |> returnM

    let bootstrapEnvForProfile profile =
        RuntimeSourceServices.configure ()
        Compiler.installBodyCompiler ()
        let env = makePrimitiveBindingsForProfile profile
        let loadFile name =
            let legacyName = Path.ChangeExtension(name, ".scm")
            let candidates =
                [ name
                  Path.Combine(AppContext.BaseDirectory, name)
                  legacyName
                  Path.Combine(AppContext.BaseDirectory, legacyName) ]
            let path =
                candidates
                |> List.tryFind File.Exists
                |> Option.defaultValue name
            if Path.GetExtension(path).Equals(".scm", StringComparison.OrdinalIgnoreCase) then
                eprintfn "Warning: legacy stdlib file '%s'; rename it to .ikr." path
            match readSource path with
            | Choice1Of2 error -> throwError error
            | Choice2Of2 source ->
                match Parser.readExprListFromSource path source with
                | Choice1Of2 error -> throwError error
                | Choice2Of2 forms ->
                    let rec evaluate = function
                        | [] -> returnM Inert
                        | form :: rest ->
                            match eval env (newContinuation env) form with
                            | Choice1Of2 error -> throwError error
                            | Choice2Of2 _ -> evaluate rest
                    evaluate forms
        match loadFile "kernel.ikr" with
        | Choice1Of2 e -> throwError e
        | Choice2Of2 _ ->
            match loadFile "promises.ikr" with
            | Choice1Of2 e -> throwError e
            | Choice2Of2 _ -> returnM env

    let bootstrapEnv () = bootstrapEnvForProfile Unrestricted

    let defaultPackagePath inputPath = Path.ChangeExtension(inputPath, ".ikc")

    /// Validate and package Kernel source without evaluating it.
    let compileFileToPackage (inputPath: string) (outputPath: string) : ThrowsError<string> =
        let env = makePrimitiveBindings ()
        if not (String.Equals(Path.GetExtension(outputPath), ".ikc", StringComparison.OrdinalIgnoreCase)) then
            throwError (Default "IronKernel packages must use the .ikc extension")
        else
            match readSource inputPath with
            | Choice1Of2 e -> throwError e
            | Choice2Of2 source ->
                match analyzePackage env inputPath source with
                | Choice1Of2 e -> throwError e
                | Choice2Of2 expressions -> writeIkcPackage outputPath expressions

    let compileFileToPackageForProfile profile (inputPath: string) (outputPath: string) : ThrowsError<string> =
        if not (String.Equals(Path.GetExtension(outputPath), ".ikc", StringComparison.OrdinalIgnoreCase)) then
            throwError (Default "IronKernel packages must use the .ikc extension")
        else
            match readSource inputPath with
            | Choice1Of2 e -> throwError e
            | Choice2Of2 source ->
                let env = makePrimitiveBindingsForProfile profile
                match analyzePackage env inputPath source with
                | Choice1Of2 e -> throwError e
                | Choice2Of2 expressions -> writeIkcPackage outputPath expressions

    [<Obsolete("Use compileFileToPackage; IKC files are packages, not CLR assemblies.")>]
    let compileFileToAssembly inputPath outputPath =
        compileFileToPackage inputPath outputPath

    let loadIkcWithArgsForProfile profile (path: string) (args: string list) : ThrowsError<LispVal> =
        try
            match bootstrapEnvForProfile profile with
            | Choice1Of2 e -> throwError e
            | Choice2Of2 standardEnv ->
                let env =
                    bindVars standardEnv
                        [ "args", ofList (List.map (fun arg -> Obj(arg :> obj)) args) ]
                use fs = File.OpenRead path
                let forms = CorePackage.read env path fs |> List.map compileToFunc
                runCompiledForms env forms
        with
        | :? InvalidDataException as ex -> throwError (Default ("Failed to load '" + path + "': " + ex.Message))
        | :? IOException as ex -> throwError (Default ("Failed to load '" + path + "': " + ex.Message))

    let loadIkcWithArgs path args = loadIkcWithArgsForProfile Unrestricted path args
    let loadIkc path = loadIkcWithArgs path []
