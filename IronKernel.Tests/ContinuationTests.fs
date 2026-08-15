module IronKernel.Tests.ContinuationTests

open System
open Xunit
open IronKernel.Ast
open IronKernel.Eval
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``CPS frames reject non-continuations explicitly`` () =
    let callback _ _ _ _ = Done(Choice2Of2 Inert)
    let error = Assert.Throws<ArgumentException>(fun () -> makeCPS Nil Nil callback |> ignore)
    Assert.Equal("cont", error.ParamName)

[<Fact>]
let ``evaluator entry points reject invalid contexts structurally`` () =
    let env = freshEnv ()
    let cont = newContinuation env
    let assertTypeMismatch expected found step =
        match run step with
        | Choice1Of2 (TypeMismatch (actual, value)) ->
            Assert.Equal(expected, actual)
            Assert.Equal(showVal found, showVal value)
        | result -> failwithf "expected %s type mismatch, got %A" expected result

    for step in
        [ continueEvalStep Nil cont Inert
          evalStep Nil cont Inert
          operateStep Nil cont Inert [] ] do
        assertTypeMismatch "environment" Nil step

    for step in
        [ continueEvalStep env Nil Inert
          evalStep env Nil Inert
          operateStep env Nil Inert [] ] do
        assertTypeMismatch "continuation" Nil step

[<Fact>]
let ``call-cc escapes`` () =
    evalSessionKernel [
        "(call/cc (lambda (k) (* 5 4)))", Obj 20
        "(call/cc (lambda (k) (* 5 (k 4))))", Obj 4
        """(let ((x (call/cc (lambda (k) k))))
             (x (lambda (_) "hi")))""", Obj "hi"
    ]

[<Fact>]
let ``shift and reset core`` () =
    evalSessionKernel [
        "(- (reset (+ 3 (* 5 2))) 1)", Obj 12
        "(reset (+ 3 (shift (lambda (k) (* 5 2)))))", Obj 10
        "(- (reset (+ 3 (shift (lambda (k) (* 5 2))))) 1)", Obj 9
        "(reset (let ((x 1)) (+ 10 (shift (lambda (k) x)))))", Obj 1
        "(+ 1 (reset (+ 2 (shift (lambda (k) 3)))))", Obj 4
        "(reset (+ (shift (lambda (k) (k 7))) 1))", Obj 8
        "(+ (reset (+ (shift (lambda (k) (k 7))) 1)) 3)", Obj 11
        "(reset (+ (shift (lambda (k) (+ 2 (k 7)))) 3))", Obj 12
        "(+ 1 (reset (+ 2 (shift (lambda (k) (+ 3 (k 4)))))))", Obj 10
    ]

[<Fact>]
let ``shift and reset with lists`` () =
    evalSessionKernel [
        "(cons 1 (reset (cons 2 (shift (lambda (k) (cons 3 '()))))))", ofList [Obj 1; Obj 3]
        "(cons 1 (reset (cons 2 '())))", ofList [Obj 1; Obj 2]
        "(cons 'a (reset (cons 'b (shift (lambda (k) (cons 1 (k (k (cons 'c '())))))))))",
            ofList [Atom "a"; Obj 1; Atom "b"; Atom "b"; Atom "c"]
        "(cons 1 (reset (cons 2 (shift (lambda (k) (cons 3 (k (cons 4 '()))))))))",
            ofList [Obj 1; Obj 3; Obj 2; Obj 4]
        "(cons 1 (reset (cons 2 (shift (lambda (k) (cons 3 (k (k (cons 4 '())))))))))",
            ofList [Obj 1; Obj 3; Obj 2; Obj 2; Obj 4]
    ]

[<Fact>]
let ``tagged prompt lookup handles deep continuation records`` () =
    let depth = 100_000
    let env = freshEnv ()
    let target = Guid.NewGuid()
    let record next =
        { closure = env
          currentCont = None
          nextCont = next
          args = None }
    let mutable deepRecord = record None
    for _ in 1..depth do
        deepRecord <- record (Some(Continuation(deepRecord, None, Delimited)))

    let matchingRecord = record None
    let matchingFrame =
        { parentCont = newContinuation env
          tag = Some target
          handler = None }
    let matching = Continuation(matchingRecord, Some matchingFrame, Full)
    let outerFrame =
        { parentCont = matching
          tag = Some(Guid.NewGuid())
          handler = None }
    let continuation = Continuation(deepRecord, Some outerFrame, Full)

    match findPrompt (Some target) continuation with
    | Some(combined, frame) ->
        Assert.Equal(Some target, frame.tag)
        let mutable current = combined
        for _ in 1..depth do
            match current.nextCont with
            | Some(Continuation(next, None, Delimited)) -> current <- next
            | other -> failwithf "unexpected continuation link: %A" other
        match current.nextCont with
        | Some(Continuation(appended, None, Full)) ->
            Assert.True(Object.ReferenceEquals(appended.closure, matchingRecord.closure))
            Assert.True(appended.nextCont.IsNone)
        | other -> failwithf "missing appended continuation: %A" other
    | None -> failwith "matching prompt was not found"

[<Fact>]
let ``tagged prompt lookup handles deeply nested prompt frames`` () =
    let depth = 100_000
    let env = freshEnv ()
    let target = Guid.NewGuid()
    let record () =
        { closure = env
          currentCont = None
          nextCont = None
          args = None }
    let matchingFrame =
        { parentCont = newContinuation env
          tag = Some target
          handler = None }
    let mutable continuation = Continuation(record (), Some matchingFrame, Full)
    for _ in 1..depth do
        let frame =
            { parentCont = continuation
              tag = Some(Guid.NewGuid())
              handler = None }
        continuation <- Continuation(record (), Some frame, Full)

    match findPrompt (Some target) continuation with
    | Some(combined, frame) ->
        Assert.Equal(Some target, frame.tag)
        let mutable current = combined
        for _ in 1..depth do
            match current.nextCont with
            | Some(Continuation(next, None, Full)) -> current <- next
            | other -> failwithf "unexpected continuation link: %A" other
        Assert.True(current.nextCont.IsNone)
    | None -> failwith "matching prompt was not found"

[<Fact>]
let ``generator style yield via shift`` () =
    evalSessionKernel [
        "(defn (yield x) (shift (lambda (k) (cons x (k (#inert))))))", Inert
        "(reset (begin (yield 1) (yield 2) (yield 3) ()))", ofList [Obj 1; Obj 2; Obj 3]
    ]

[<Fact>]
let ``tail recursion does not overflow`` () =
    evalSessionKernel [
        "(define f (lambda (x) (if (> x 0) (f (- x 1)) 0)))", Inert
        "(f 1000000)", Obj 0
    ]
