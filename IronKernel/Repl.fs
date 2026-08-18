namespace IronKernel
    
module Repl =

    open Ast
    open System
    open System.Reflection
    open Errors
    open Eval
    open Parser
    open SymbolTable
    open Choice
    open Runtime
    open Compiler
    open Emit
    open Mono.Terminal
    open System.Text

    let lineEditor = LineEditor("ironkernel")

    let flushStr (str:String) =
      Console.Write(str)

    let putStrLn (str:String) =
      Console.WriteLine(str)

    /// The Mono.Terminal line editor drives the cursor directly, so it needs a real
    /// TTY. With stdin or stdout redirected `Console.WindowWidth` is 0 and rendering
    /// divides by zero, which used to crash piped and scripted sessions.
    let isInteractiveConsole () =
      not Console.IsInputRedirected
      && not Console.IsOutputRedirected
      && (try Console.WindowWidth > 0 with :? IO.IOException -> false)

    /// Plain reads keep non-interactive sessions working; `until` already stops on the
    /// null that `ReadLine` returns at end of input.
    let readPrompt (prompt: string) =
      if isInteractiveConsole () then
        fun _ -> lineEditor.Edit(prompt, "")
      else
        fun _ ->
          Console.Write prompt
          Console.Out.Flush()
          Console.ReadLine()

    let evalString env cont expr = 
        let evaled = 
            match (readExpr expr) with
            |Choice1Of2(error) -> throwError error
            |Choice2Of2(result) -> try 
                                    // Prefer hybrid compiled evaluation; residual path covers full Kernel.
                                    evalCompiled env cont result
                                   with ex -> throwError (ClrException ex)
        extractValue (trapError evaled) 

    let evalAndPrint env cont expr : unit = (evalString env cont expr |> showVal |> putStrLn)

    let until cond (prompt:unit -> string) action =
      let rec loop _ =
        let result = prompt ()
        if result <> null && not(cond result) then  
            if result <> "" then action result
            loop ()
      loop ()

    let runOneWithProfile profile filename (args:string list) =
        match bootstrapEnvForProfile profile with
        | Choice1Of2 error ->
            eprintfn "Startup error: %s" (showError error)
            1
        | Choice2Of2 standardEnv ->
            let env =
                bindVars standardEnv
                    [ "args", ofList (List.map (fun x -> Ast.Obj(x :> obj)) args) ]
            match runSourceFile env filename with
            | Choice1Of2 error ->
                eprintfn "Script error: %s" (showError error)
                1
            | Choice2Of2 _ -> 0

    let runOne filename args = runOneWithProfile Unrestricted filename args

    /// Product version from MSBuild `<Version>` (root `version` file via Directory.Build.props).
    let version =
        let asm = Assembly.GetExecutingAssembly()
        match asm.GetCustomAttribute<AssemblyInformationalVersionAttribute>() with
        | null ->
            match asm.GetName().Version with
            | null -> "0.0.0"
            | v -> sprintf "%d.%d.%d" v.Major v.Minor v.Build
        | attr ->
            // Strip optional SourceLink/build metadata ("1.2.3+abc" -> "1.2.3").
            let raw = attr.InformationalVersion
            match raw.IndexOf('+') with
            | -1 -> raw
            | i -> raw.Substring(0, i)

    let showBanner _ = 
        putStrLn ""
        putStrLn (sprintf " IronKernel v%s" version)
        putStrLn " Full-Kernel hybrid CLR compiler"
        putStrLn " https://github.com/ironkernel-lang/IronKernel"
        putStrLn ""

    let runReplWithProfile profile _ =
        Console.OutputEncoding <- Encoding.UTF8
        showBanner ()
        match bootstrapEnvForProfile profile with
        | Choice1Of2 error ->
            eprintfn "Startup error: %s" (showError error)
            1
        | Choice2Of2 env ->
            let run = evalAndPrint env (newContinuation env)
            until (fun x -> x.ToLowerInvariant().Equals("quit"))
                (readPrompt "IronKernel> ") run
            0

    let runRepl arg = runReplWithProfile Unrestricted arg
