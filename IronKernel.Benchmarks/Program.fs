module IronKernel.Benchmarks.Program

open System
open BenchmarkDotNet.Attributes
open BenchmarkDotNet.Running
open IronKernel.Ast
open IronKernel.Compiler
open IronKernel.Emit
open IronKernel.Eval
open IronKernel.Interop
open IronKernel.Parser
open IronKernel.Runtime
open IronKernel.SymbolTable

let private parse expression =
    match readExpr expression with
    | Choice2Of2 value -> value
    | Choice1Of2 error -> invalidOp (sprintf "Benchmark expression failed to parse: %A" error)

[<MemoryDiagnoser>]
type CompilerBenchmarks() =
    let env = makePrimitiveBindings ()
    let literalCall = parse "(+ 20 22)"
    let dynamicCall = parse "(+ value 1)"
    let mutable compiledFolded = Unchecked.defaultof<KernelFunc>
    let mutable compiledGeneric = Unchecked.defaultof<KernelFunc>

    [<GlobalSetup>]
    member _.Setup() =
        defineVar env "value" (Obj 41) |> ignore
        compiledFolded <- compileLispValGuarded env literalCall
        compiledGeneric <- compileLispValGuarded env dynamicCall

    [<Benchmark>]
    member _.ColdCompile() =
        compileLispValGuarded env dynamicCall

    [<Benchmark(Baseline = true)>]
    member _.Interpreted() =
        eval env (newContinuation env) dynamicCall

    [<Benchmark>]
    member _.CompiledGeneric() =
        run (compiledGeneric.Invoke(env, newContinuation env))

    [<Benchmark>]
    member _.CompiledFolded() =
        run (compiledFolded.Invoke(env, newContinuation env))

[<MemoryDiagnoser>]
type SymbolLookupBenchmarks() =
    let mutable env = Nil

    [<Params(1, 10, 50)>]
    member val Depth = 1 with get, set

    [<GlobalSetup>]
    member this.Setup() =
        let root = newEnv []
        defineVar root "target" (Obj 42) |> ignore
        env <-
            [2..this.Depth]
            |> List.fold (fun parent _ -> newEnv [parent]) root

    [<Benchmark>]
    member _.LookupParentBinding() =
        getVar' env "target"

[<MemoryDiagnoser>]
type ClrResolutionBenchmarks() =
    [<Benchmark>]
    member _.ResolveAcrossAssemblies() =
        resolveTypeExact "IronKernel.Ast"

[<MemoryDiagnoser>]
type EqualityBenchmarks() =
    let values () = [1..16] |> List.map (fun value -> Obj (value :> obj))
    let scalarArgs = [Obj (42 :> obj); Obj (42 :> obj)]
    let flatListArgs = [ofList (values ()); ofList (values ())]
    let nestedListArgs =
        [ ofList [ofList (values ()); ofList (values ())]
          ofList [ofList (values ()); ofList (values ())] ]
    let dottedListArgs =
        [ (ofDotted (values ()) (Atom "tail"))
          (ofDotted (values ()) (Atom "tail")) ]

    [<Benchmark(Baseline = true)>]
    member _.ScalarEqual() =
        eqv' scalarArgs

    [<Benchmark>]
    member _.FlatListEqual() =
        eqv' flatListArgs

    [<Benchmark>]
    member _.NestedListEqual() =
        eqv' nestedListArgs

    [<Benchmark>]
    member _.DottedListEqual() =
        eqv' dottedListArgs

[<MemoryDiagnoser>]
type ApplicationArityBenchmarks() =
    let env = makePrimitiveBindings ()
    let unaryCall = parse "(zero? value)"
    let binaryCall = parse "(+ value 1)"
    let ternaryCall = parse "(vector value 1 2)"

    let evaluate expression =
        eval env (newContinuation env) expression

    [<GlobalSetup>]
    member _.Setup() =
        defineVar env "value" (Obj 0) |> ignore

    [<Benchmark(Baseline = true)>]
    member _.UnaryCall() =
        evaluate unaryCall

    [<Benchmark>]
    member _.BinaryCall() =
        evaluate binaryCall

    [<Benchmark>]
    member _.TernaryCall() =
        evaluate ternaryCall

[<MemoryDiagnoser>]
type ControlFlowBenchmarks() =
    let lambdaLiteralCall = parse "((lambda (x) (* 5 x)) 4)"
    let namedLambdaCall = parse "(named-lambda 4)"
    let namedVauCall = parse "(named-vau 4)"
    let callCc = parse "(call/cc callcc-handler)"
    let shiftReset = parse "(reset (+ (shift shift-handler) 1))"
    let promptOnly = parse "(prompt effect effect-resume-handler (+ 1 40))"
    let directEffectHandler = parse "(effect-abort-handler 40 #inert)"
    let effectAbort =
        parse
            "(prompt effect effect-abort-handler (+ 1 (perform effect 40)))"
    let effectResume =
        parse
            "(prompt effect effect-resume-handler (+ 1 (perform effect 40)))"
    let definitions =
        [ "effect", "(define effect (make-prompt-tag))"
          "lambda", "(define named-lambda (lambda (x) (* 5 x)))"
          "lambda", "(define named-vau (wrap (vau (x) _ (* 5 x))))"
          "call/cc", "(define callcc-handler (lambda (k) (* 5 (k 4))))"
          "shift", "(define shift-handler (lambda (k) (k 7)))"
          "effect", "(define effect-abort-handler (lambda (value k) (+ value 1)))"
          "effect", "(define effect-resume-handler (lambda (value k) (resume k (+ value 1))))" ]
    let cases =
        [ lambdaLiteralCall, 20
          namedLambdaCall, 20
          namedVauCall, 20
          callCc, 4
          shiftReset, 8
          promptOnly, 41
          directEffectHandler, 41
          effectAbort, 41
          effectResume, 42 ]
    let mutable env = Nil

    let evaluate expression =
        eval env (newContinuation env) expression

    [<GlobalSetup>]
    member _.Setup() =
        env <-
            match bootstrapEnv () with
            | Choice2Of2 value -> value
            | Choice1Of2 error -> invalidOp (sprintf "Benchmark bootstrap failed: %A" error)
        let requireInert label expression =
            (match eval env (newContinuation env) (parse expression) with
             | Choice2Of2 Inert -> ()
             | result -> invalidOp (sprintf "Benchmark %s setup failed: %A" label result))
        let requireValue expression expected =
            (match evaluate expression with
             | Choice2Of2 (Obj (:? int as value)) when value = expected -> ()
             | result -> invalidOp (sprintf "Benchmark control-flow check failed: %A" result))

        definitions |> List.iter (fun (label, definition) -> requireInert label definition)
        cases |> List.iter (fun (expression, expected) -> requireValue expression expected)

    [<Benchmark>]
    member _.LambdaLiteralCall() =
        evaluate lambdaLiteralCall

    [<Benchmark(Baseline = true)>]
    member _.NamedLambdaCall() =
        evaluate namedLambdaCall

    [<Benchmark>]
    member _.NamedVauCall() =
        evaluate namedVauCall

    [<Benchmark>]
    member _.CallCcEscape() =
        evaluate callCc

    [<Benchmark>]
    member _.ShiftResetResume() =
        evaluate shiftReset

    [<Benchmark>]
    member _.PromptOnly() =
        evaluate promptOnly

    [<Benchmark>]
    member _.DirectEffectHandler() =
        evaluate directEffectHandler

    [<Benchmark>]
    member _.EffectHandlerAbort() =
        evaluate effectAbort

    [<Benchmark>]
    member _.EffectHandlerResume() =
        evaluate effectResume

/// Before/after for guarded `vau` specialization. `Unguarded` is the plain
/// `analyze` path (COperate through the named call-site cache); `Guarded` is the
/// binding-guarded intrinsic.
///
/// Measures when guarded specialization actually pays, which decides whether
/// extending `PrimitiveIdentity` to further primitives is worthwhile. The two
/// environment configurations differ sharply:
///
///   * Shared `env` (top-level forms): the call-site cache validates by reference
///     equality and always hits, so the guard's name re-resolution is pure
///     overhead and the guarded path loses.
///   * Fresh child frame per call: the call-site cache misses and must re-resolve
///     and refill, which the guard beats.
///
/// Only the shared case occurs today. Procedure bodies are stored as raw
/// `KernelCode` and interpreted, and `CompiledCombiner` is never constructed, so
/// no compiled expression is ever invoked against a fresh frame. Until bodies are
/// compiled, added guards are measured pessimizations rather than wins.
[<MemoryDiagnoser>]
type GuardSpecializationBenchmarks() =
    let env = makePrimitiveBindings ()
    let form = parse "(if #t 1 2)"
    let mutable unguarded = Unchecked.defaultof<KernelFunc>
    let mutable guarded = Unchecked.defaultof<KernelFunc>

    [<GlobalSetup>]
    member _.Setup() =
        unguarded <- compileLispVal form
        guarded <- compileLispValGuarded env form
        let requireOne (func: KernelFunc) =
            match run (func.Invoke(env, newContinuation env)) with
            | Choice2Of2 (Obj (:? int as value)) when value = 1 -> ()
            | result -> invalidOp (sprintf "Guard benchmark setup failed: %A" result)
        requireOne unguarded
        requireOne guarded

    [<Benchmark(Baseline = true)>]
    member _.Unguarded() =
        run (unguarded.Invoke(env, newContinuation env))

    [<Benchmark>]
    member _.Guarded() =
        run (guarded.Invoke(env, newContinuation env))

    // The realistic case for code inside a procedure body: a fresh child frame per
    // call, so the named call-site cache misses and must re-resolve and refill.
    // The child-frame allocation is common to both and cancels in the ratio.
    [<Benchmark>]
    member _.UnguardedFreshEnv() =
        let frame = newEnv [env]
        run (unguarded.Invoke(frame, newContinuation frame))

    [<Benchmark>]
    member _.GuardedFreshEnv() =
        let frame = newEnv [env]
        run (guarded.Invoke(frame, newContinuation frame))

[<EntryPoint>]
let main args =
    BenchmarkSwitcher.FromAssembly(typeof<CompilerBenchmarks>.Assembly).Run(args) |> ignore
    0
