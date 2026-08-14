module IronKernel.Tests.EffectTests

open System.Threading.Tasks
open Xunit

open IronKernel.Ast
open IronKernel.Eval
open IronKernel.Runtime
open IronKernel.SymbolTable
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``tagged shift selects the nearest matching prompt`` () =
    evalSessionKernel
        [ "(define outer (make-prompt-tag))", Inert
          "(define inner (make-prompt-tag))", Inert
          "(reset outer (+ 100 (reset inner (+ 10 (shift outer (lambda (k) 1))))))", Obj 1
          "(reset outer (+ 100 (reset inner (+ 10 (shift inner (lambda (k) 1))))))", Obj 101
          "(reset outer (+ 100 (reset inner (+ 10 (shift outer (lambda (k) (k 1)))))))", Obj 111 ]

[<Fact>]
let ``tagged shift reports a missing prompt`` () =
    withKernel (fun env ->
        ignore (evalIn env "(define tag (make-prompt-tag))")
        match evalRaw Interpreted env "(shift tag (lambda (k) 1))" with
        | Choice1Of2 (Default message) -> Assert.Contains("matching tagged prompt", message)
        | result -> failwithf "unexpected missing-prompt result: %A" result)

[<Fact>]
let ``deep effect handler can abort or resume`` () =
    evalSessionKernel
        [ "(define effect (make-prompt-tag))", Inert
          "(prompt effect (lambda (value k) (+ value 1)) (+ 100 (perform effect 41)))", Obj 42
          "(prompt effect (lambda (value k) (resume k (+ value 1))) (+ 1 (perform effect 40)))", Obj 42
          """(prompt effect
               (lambda (value k) (resume k (+ value 1)))
               (+ (perform effect 1) (perform effect 2)))""", Obj 5 ]

[<Fact>]
let ``effect resumptions are one shot`` () =
    withKernel (fun env ->
        ignore (evalIn env "(define effect (make-prompt-tag))")
        ignore (evalIn env "(define saved (vector #inert))")
        assertEval env
            """(prompt effect
                 (lambda (value k)
                   (begin (vector-set! saved 0 k) (resume k value)))
                 (perform effect 1))"""
            (Obj 1)
        match evalRaw Interpreted env "(resume (vector-ref saved 0) 0)" with
        | Choice1Of2 (Default message) -> Assert.Contains("already been consumed", message)
        | result -> failwithf "unexpected repeated-resume result: %A" result)

[<Fact>]
let ``aborting handler invalidates the resumption`` () =
    withKernel (fun env ->
        ignore (evalIn env "(define effect (make-prompt-tag))")
        ignore (evalIn env "(define saved (vector #inert))")
        assertEval env
            """(prompt effect
                 (lambda (value k)
                   (begin (vector-set! saved 0 k) (+ value 1)))
                 (+ 100 (perform effect 41)))"""
            (Obj 42)
        match evalRaw Interpreted env "(resume (vector-ref saved 0) 0)" with
        | Choice1Of2 (Default message) -> Assert.Contains("already been consumed", message)
        | result -> failwithf "unexpected aborted-resumption result: %A" result)

[<Fact>]
let ``resume result is not replaced by trailing handler forms`` () =
    evalSessionKernel
        [ "(define effect (make-prompt-tag))", Inert
          """(prompt effect
               (lambda (value k)
                 (begin (resume k (+ value 1)) 999))
               (+ 100 (perform effect 41)))""", Obj 142 ]

[<Fact>]
let ``await task suspends and resumes the trampoline`` () =
    let env = makePrimitiveBindings ()
    let completion =
        TaskCompletionSource<LispVal>(TaskCreationOptions.RunContinuationsAsynchronously)
    ignore (defineVar env "pending" (Obj(completion.Task :> obj)))

    let resultTask =
        evalAsync env (newContinuation env) (parseOk "(+ 1 (await-task pending))")

    Assert.False(resultTask.IsCompleted)
    completion.SetResult(Obj (41 :> obj))

    match resultTask.GetAwaiter().GetResult() with
    | Choice2Of2 (Obj (:? int as value)) -> Assert.Equal(42, value)
    | result -> failwithf "unexpected async result: %A" result

[<Fact>]
let ``await task maps faults to language errors`` () =
    let env = makePrimitiveBindings ()
    let completion =
        TaskCompletionSource<LispVal>(TaskCreationOptions.RunContinuationsAsynchronously)
    ignore (defineVar env "pending" (Obj(completion.Task :> obj)))

    let resultTask =
        evalAsync env (newContinuation env) (parseOk "(await-task pending)")
    completion.SetException(System.InvalidOperationException("async boom"))

    match resultTask.GetAwaiter().GetResult() with
    | Choice1Of2 (ClrException error) -> Assert.Contains("async boom", error.Message)
    | result -> failwithf "unexpected faulted-task result: %A" result

[<Fact>]
let ``await task unwraps generic task results`` () =
    let env = makePrimitiveBindings ()
    let completion =
        TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously)
    ignore (defineVar env "pending" (Obj(completion.Task :> obj)))

    let resultTask =
        evalAsync env (newContinuation env) (parseOk "(await-task pending)")
    completion.SetResult("hello")

    match resultTask.GetAwaiter().GetResult() with
    | Choice2Of2 (Obj (:? string as value)) -> Assert.Equal("hello", value)
    | result -> failwithf "unexpected generic-task result: %A" result

[<Fact>]
let ``effects and async preserve interpreter compiler parity`` () =
    assertParitySession
        [ "(load \"kernel.ikr\")"
          "(define effect (make-prompt-tag))"
          "(prompt effect (lambda (value k) (resume k value)) (+ 1 (perform effect 41)))"
          "(+ 1 (await-task (task-delay 5 41)))" ]

[<Fact>]
let ``await-task returns the awaited value`` () =
    // The value used to be discarded and reported as #inert. An F# `task { ... }` is
    // an AsyncStateMachineBox that *derives from* Task<T> without being it, so a check
    // against the concrete type never matched. Nothing awaited a task and inspected
    // the result, so only capability gating was covered and this went unnoticed.
    withKernel (fun env ->
        assertEval env "(await-task (task-delay 5 42))" (Obj 42)
        assertEval env "(equal? (await-task (task-delay 5 'done)) 'done)" (Bool true)
        // The value must survive being bound, not just being returned.
        ignore (evalIn env "(define awaited (await-task (task-delay 5 7)))")
        assertEval env "(=? awaited 7)" (Bool true)
        // And it must compose with further computation rather than ending it.
        assertEval env "(+ 1 (await-task (task-delay 5 41)))" (Obj 42))

[<Fact>]
let ``await-task rejects a non-task argument`` () =
    let env = freshEnv ()
    match evalIn env "(await-task 5)" with
    | Status message -> Assert.Contains("Task", message)
    | value -> failwithf "expected an error, got %s" (showVal value)
