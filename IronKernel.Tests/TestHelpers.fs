module IronKernel.Tests.TestHelpers

open System.IO

open IronKernel.Ast
open IronKernel.Compiler
open IronKernel.Eval
open IronKernel.Runtime
open IronKernel.Repl
open IronKernel.Choice
open IronKernel.Errors
open IronKernel.Parser

/// Isolated primitive environment (does not share REPL state).
let freshEnv () =
    IronKernel.RuntimeSourceServices.configure ()
    installBodyCompiler ()
    makePrimitiveBindings ()

let evalIn env expr =
    evalString env (newContinuation env) expr

let expect eqvResult =
    match eqvResult with
    | Choice1Of2 e -> failwith (showError e)
    | Choice2Of2 (Bool true) -> ()
    | Choice2Of2 (Bool false) -> failwith "values are not eqv?"
    | Choice2Of2 other -> failwith ("expected Bool, got " + showVal other)

let assertEqv actual expected =
    expect (eqv' [actual; expected])

let assertEval env expr expected =
    assertEqv (evalIn env expr) expected

let assertEvalString expr expected =
    assertEval (freshEnv ()) expr expected

/// Run a session of (expr, expected) pairs in one fresh environment.
let evalSession (lines: (string * LispVal) list) =
    let env = freshEnv ()
    lines
    |> List.iter (fun (expr, expected) ->
        let actual = evalIn env expr
        match eqv' [actual; expected] with
        | Choice2Of2 (Bool true) -> ()
        | Choice2Of2 (Bool false) ->
            failwithf "expecting '%s' got '%s' for: %s" (showVal expected) (showVal actual) expr
        | Choice1Of2 e ->
            failwithf "eqv? failed (%s) for: %s => %s" (showError e) expr (showVal actual)
        | Choice2Of2 other ->
            failwithf "eqv? returned %s for: %s" (showVal other) expr)

/// Fresh env with kernel.ikr loaded.
let withKernel (body: LispVal -> unit) =
    let env = freshEnv ()
    match evalIn env "(load \"kernel.ikr\")" with
    | Status s -> failwith ("failed to load kernel.ikr: " + s)
    | _ -> body env

/// Fresh env with kernel.ikr + promises.ikr.
let withKernelAndPromises (body: LispVal -> unit) =
    withKernel (fun env ->
        match evalIn env "(load \"promises.ikr\")" with
        | Status s -> failwith ("failed to load promises.ikr: " + s)
        | _ -> body env)

let evalSessionKernel (lines: (string * LispVal) list) =
    withKernel (fun env ->
        lines
        |> List.iter (fun (expr, expected) ->
            let actual = evalIn env expr
            match eqv' [actual; expected] with
            | Choice2Of2 (Bool true) -> ()
            | Choice2Of2 (Bool false) ->
                failwithf "expecting '%s' got '%s' for: %s" (showVal expected) (showVal actual) expr
            | Choice1Of2 e ->
                failwithf "eqv? failed (%s) for: %s => %s" (showError e) expr (showVal actual)
            | Choice2Of2 other ->
                failwithf "eqv? returned %s for: %s" (showVal other) expr))

/// The same, with promises.ikr loaded as well.
let evalSessionKernelAndPromises (lines: (string * LispVal) list) =
    withKernelAndPromises (fun env ->
        lines
        |> List.iter (fun (expr, expected) ->
            let actual = evalIn env expr
            match eqv' [actual; expected] with
            | Choice2Of2 (Bool true) -> ()
            | Choice2Of2 (Bool false) ->
                failwithf "expecting '%s' got '%s' for: %s" (showVal expected) (showVal actual) expr
            | Choice1Of2 e ->
                failwithf "eqv? failed (%s) for: %s => %s" (showError e) expr (showVal actual)
            | Choice2Of2 other ->
                failwithf "eqv? returned %s for: %s" (showVal other) expr))

let parseOk input =
    match readExpr input with
    | Choice2Of2 v -> v
    | Choice1Of2 e -> failwith ("parse failed: " + showError e)

let parseError input =
    match readExpr input with
    | Choice1Of2 _ -> ()
    | Choice2Of2 v -> failwith ("expected parse error, got " + showVal v)

type EvaluationMode =
    | Interpreted
    | Compiled

type EvaluationObservation =
    | Returned of string
    | Failed of string

let evalRaw mode env expr =
    let form = parseOk expr
    let cont = newContinuation env
    match mode with
    | Interpreted -> eval env cont form
    | Compiled -> evalCompiled env cont form

let observe = function
    | Choice2Of2 value -> Returned (showVal value)
    | Choice1Of2 error -> Failed (showError error)

/// Evaluate the same stateful session through both engines and compare every step.
let assertParitySession expressions =
    let interpretedEnv = freshEnv ()
    let compiledEnv = freshEnv ()

    expressions
    |> List.iter (fun expr ->
        let interpreted = evalRaw Interpreted interpretedEnv expr |> observe
        let compiled = evalRaw Compiled compiledEnv expr |> observe
        if interpreted <> compiled then
            failwithf
                "interpreter/compiler mismatch for %s\ninterpreted: %A\ncompiled: %A"
                expr
                interpreted
                compiled)

let assertParityValueSession expressions expected =
    assertParitySession expressions

    for mode in [Interpreted; Compiled] do
        let env = freshEnv ()
        let mutable result = Choice2Of2 Inert
        for expr in expressions do
            result <- evalRaw mode env expr

        match result with
        | Choice2Of2 actual -> assertEqv actual expected
        | Choice1Of2 error ->
            failwithf "%A evaluation failed: %s" mode (showError error)

let repoFile relative =
    let candidates =
        [ relative
          Path.Combine("..", relative)
          Path.Combine("..", "..", relative)
          Path.Combine(Directory.GetCurrentDirectory(), relative) ]
    candidates
    |> List.tryFind File.Exists
    |> Option.defaultWith (fun () -> failwith ("missing file: " + relative))
