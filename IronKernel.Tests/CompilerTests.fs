module IronKernel.Tests.CompilerTests

open System
open System.IO
open Xunit
open IronKernel.Ast
open IronKernel.Analyze
open IronKernel.Compiler
open IronKernel.StaticCompiler
open IronKernel.Emit
open IronKernel.Eval
open IronKernel.Ir
open IronKernel.Errors
open IronKernel.Parser
open IronKernel.PartialEval
open IronKernel.SymbolTable
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``analyze combinations without privileging operator names`` () =
    match analyze (parseOk "(if #t 1 2)") with
    | COperate (CVar "if", [Bool true; Obj _; Obj _]) -> ()
    | other -> failwith (showCore other)

    match analyze (parseOk "(define x 1)") with
    | COperate (CVar "define", [Atom "x"; Obj _]) -> ()
    | other -> failwith (showCore other)

    match analyze (parseOk "(vau (x) e x)") with
    | COperate (CVar "vau", [List [Atom "x"]; Atom "e"; Atom "x"]) -> ()
    | other -> failwith (showCore other)

    match analyze (parseOk "(+ 1 2)") with
    | COperate (CVar "+", [Obj _; Obj _]) -> ()
    | other -> failwith (showCore other)

[<Fact>]
let ``analysis handles deeply nested operator positions`` () =
    let depth = 100_000
    let mutable form = Atom "deep-operator"
    for _ in 1..depth do
        form <- List [form]

    let assertShape analyzed =
        let mutable current = analyzed
        for _ in 1..depth do
            match current with
            | COperate(operator, []) -> current <- operator
            | other -> failwithf "expected nested operator, got %s" (showCore other)
        match current with
        | CVar "deep-operator" -> ()
        | other -> failwithf "expected operator leaf, got %s" (showCore other)

    assertShape (analyze form)
    assertShape (analyzeGuarded (freshEnv ()) form)

[<Fact>]
let ``located analysis handles deeply nested operator positions`` () =
    let depth = 100_000
    let span =
        { sourceName = "deep.ikr"
          startPosition = { offset = 0L; line = 1L; column = 1L }
          endPosition = { offset = 0L; line = 1L; column = 1L } }
    let mutable located : IronKernel.Source.LocatedValue =
        { kind = IronKernel.Source.LAtom "deep-operator"; span = span }
    for _ in 1..depth do
        located <- { kind = IronKernel.Source.LList [located]; span = span }

    let mutable analyzed = analyzeLocatedGuarded (freshEnv ()) "deep-operator" located
    for _ in 1..depth do
        match analyzed with
        | CLocated(_, Some "deep-operator", COperate(operator, [])) -> analyzed <- operator
        | other -> failwithf "expected located operator, got %s" (showCore other)
    match analyzed with
    | CLocated(_, Some "deep-operator", CVar "deep-operator") -> ()
    | other -> failwithf "expected located operator leaf, got %s" (showCore other)

[<Fact>]
let ``located analysis handles deeply nested guarded conditionals`` () =
    let depth = 5_000
    let span =
        { sourceName = "deep-if.ikr"
          startPosition = { offset = 0L; line = 1L; column = 1L }
          endPosition = { offset = 0L; line = 1L; column = 1L } }
    let located kind : IronKernel.Source.LocatedValue = { kind = kind; span = span }
    let ifOperator = located (IronKernel.Source.LAtom "if")
    let condition = located (IronKernel.Source.LLiteral(Bool true))
    let alternative = located (IronKernel.Source.LLiteral Inert)
    let mutable expression = alternative
    for _ in 1..depth do
        expression <-
            located (IronKernel.Source.LList [ifOperator; condition; expression; alternative])

    let mutable analyzed = analyzeLocatedGuarded (freshEnv ()) "if #t #inert #inert" expression
    for _ in 1..depth do
        match analyzed with
        | CLocated(_, Some "if #t #inert #inert", CGuarded(_, CIf(_, consequent, _), _)) ->
            analyzed <- consequent
        | other -> failwithf "expected located guarded conditional, got %s" (showCore other)
    match analyzed with
    | CLocated(_, Some "if #t #inert #inert", CLit Inert) -> ()
    | other -> failwithf "expected inert conditional leaf, got %s" (showCore other)

[<Fact>]
let ``compilation handles deeply nested operator positions`` () =
    let depth = 100_000
    let mutable expression = CVar "deep-operator"
    for _ in 1..depth do
        expression <- COperate(expression, [])

    let compiled = compileToFunc expression
    Assert.NotNull(compiled)

[<Fact>]
let ``compilation handles deeply nested definitions`` () =
    let depth = 100_000
    let mutable expression = CLit Inert
    for _ in 1..depth do
        expression <- CDefine(CVar "deep-binding", expression)

    let compiled = compileToFunc expression
    Assert.NotNull(compiled)

[<Fact>]
let ``compilation handles deeply nested located operators`` () =
    let depth = 100_000
    let span =
        { sourceName = "deep.ikr"
          startPosition = { offset = 0L; line = 1L; column = 1L }
          endPosition = { offset = 0L; line = 1L; column = 1L } }
    let mutable expression = CVar "deep-operator"
    for _ in 1..depth do
        expression <- CLocated(span, Some "deep-operator", COperate(expression, []))

    let compiled = compileToFunc expression
    Assert.NotNull(compiled)

[<Fact>]
let ``partial evaluation handles deeply nested locations`` () =
    let depth = 100_000
    let env = freshEnv ()
    let span =
        { sourceName = "deep.ikr"
          startPosition = { offset = 0L; line = 1L; column = 1L }
          endPosition = { offset = 0L; line = 1L; column = 1L } }
    let mutable expression = COperate(CVar "+", [Obj(1 :> obj); Obj(2 :> obj)])
    for _ in 1..depth do
        expression <- CLocated(span, Some "+ 1 2", expression)

    let mutable optimized = partialEvaluate env expression
    for _ in 1..depth do
        match optimized with
        | CLocated(_, _, inner) -> optimized <- inner
        | other -> failwithf "expected located expression, got %s" (showCore other)
    match optimized with
    | CContractFold(_, Obj (:? int as value), _) -> Assert.Equal(3, value)
    | other -> failwithf "expected folded leaf, got %s" (showCore other)

[<Fact>]
let ``environment-aware analysis guards primitive forms`` () =
    let env = freshEnv ()

    match analyzeGuarded env (parseOk "(if #t 1 2)") with
    | CGuarded (guard, CIntrinsicOperate (PrimitiveIf, _), COperate (CVar "if", _)) ->
        Assert.True(bindingGuardMatches env guard)
    | other -> failwith (showCore other)

    match analyzeGuarded env (parseOk "(define answer 42)") with
    | CGuarded (guard, CIntrinsicOperate (PrimitiveDefine, _), COperate (CVar "define", _)) ->
        Assert.True(bindingGuardMatches env guard)
    | other -> failwith (showCore other)

[<Fact>]
let ``compiled guard deoptimizes after primitive rebinding`` () =
    let env = freshEnv ()
    let compiled = compileLispValGuarded env (parseOk "(if #t 1 2)")

    match run (compiled.Invoke(env, newContinuation env)) with
    | Choice2Of2 (Obj (:? int as value)) -> Assert.Equal(1, value)
    | result -> failwithf "unexpected guarded result: %A" result

    ignore (evalIn env "(define if (vau operands caller operands))")

    match run (compiled.Invoke(env, newContinuation env)) with
    | Choice2Of2 (List [Bool true; Obj (:? int as one); Obj (:? int as two)]) ->
        Assert.Equal(1, one)
        Assert.Equal(2, two)
    | result -> failwithf "guard did not fall back after rebind: %A" result

[<Fact>]
let ``wrapped if is not analyzed as a guarded intrinsic`` () =
    let env = freshEnv ()
    ignore (evalIn env "(define if (wrap if))")

    match analyzeGuarded env (parseOk "(if #t 1 2)") with
    | COperate (CVar "if", [Bool true; Obj _; Obj _]) -> ()
    | CGuarded _ as other ->
        failwithf "wrapped if must not use guarded fast path: %s" (showCore other)
    | other -> failwith (showCore other)

[<Fact>]
let ``compiled wrapped if evaluates unused branch like the interpreter`` () =
    // Operative if skips the unused branch; applicative (wrap if) evaluates both.
    // A buggy guard fast path would return 1 while the interpreter errors.
    assertParitySession
        [ "(define if (wrap if))"
          "(if #t 1 missing-binding)" ]

[<Fact>]
let ``compiled guard detects a new shadowing binding`` () =
    let parent = freshEnv ()
    let child = newEnv [parent]
    let compiled = compileLispValGuarded child (parseOk "(if #t 1 2)")

    ignore (evalIn child "(define if (vau operands caller operands))")

    match run (compiled.Invoke(child, newContinuation child)) with
    | Choice2Of2 (List [Bool true; Obj (:? int as one); Obj (:? int as two)]) ->
        Assert.Equal(1, one)
        Assert.Equal(2, two)
    | result -> failwithf "guard did not detect shadowing: %A" result

[<Fact>]
let ``compiled guard deoptimizes after parent binding mutation`` () =
    let parent = freshEnv ()
    let child = newEnv [parent]
    let compiled = compileLispValGuarded child (parseOk "(if #t 1 2)")

    ignore (evalIn parent "(define if (vau operands caller operands))")

    match run (compiled.Invoke(child, newContinuation child)) with
    | Choice2Of2 (List [Bool true; Obj (:? int as one); Obj (:? int as two)]) ->
        Assert.Equal(1, one)
        Assert.Equal(2, two)
    | result -> failwithf "guard did not detect parent mutation: %A" result

[<Fact>]
let ``compiled define guard deoptimizes after binding changes`` () =
    let replacement = "(vau operands caller operands)"
    let rhsExpressions =
        [ "42"
          "(+ 20 22)"
          "(if #t 42 missing)"
          "((lambda (value) (+ value 1)) 41)" ]

    let assertScenario label createEnvironments mutate =
        for index, rhs in List.indexed rhsExpressions do
            let interpretedEnv, compiledEnv = createEnvironments ()
            let source = $"(define generated{index} {rhs})"
            let compiled = compileLispValGuarded compiledEnv (parseOk source)

            mutate interpretedEnv
            mutate compiledEnv

            let interpreted = evalRaw Interpreted interpretedEnv source |> observe
            let compiledResult = run (compiled.Invoke(compiledEnv, newContinuation compiledEnv)) |> observe
            if interpreted <> compiledResult then
                failwithf
                    "%s define guard mismatch for %s\ninterpreted: %A\ncompiled: %A"
                    label
                    source
                    interpreted
                    compiledResult

    assertScenario
        "local mutation"
        (fun () -> freshEnv (), freshEnv ())
        (fun env -> ignore (evalIn env $"(define define {replacement})"))

    assertScenario
        "parent mutation"
        (fun () ->
            let interpretedParent = freshEnv ()
            let compiledParent = freshEnv ()
            newEnv [interpretedParent], newEnv [compiledParent])
        (fun env ->
            match env with
            | Environment record -> ignore (evalIn (List.head record.parents) $"(define define {replacement})")
            | _ -> failwith "expected child environment")

    assertScenario
        "child shadowing"
        (fun () ->
            let interpretedParent = freshEnv ()
            let compiledParent = freshEnv ()
            newEnv [interpretedParent], newEnv [compiledParent])
        (fun env ->
            let replacementValue = evalIn env replacement
            ignore (defineVar env "define" replacementValue))

[<Fact>]
let ``located compiled guard retains the generic fallback`` () =
    let env = freshEnv ()
    let compiled =
        match compileSourceLocated env "guarded-if.ikr" "(if #t 1 2)" with
        | Choice2Of2 [form] -> form.func
        | result -> failwithf "unexpected located compilation result: %A" result

    ignore (evalIn env "(define if (vau operands caller operands))")

    match run (compiled.Invoke(env, newContinuation env)) with
    | Choice2Of2 (List [Bool true; Obj (:? int as one); Obj (:? int as two)]) ->
        Assert.Equal(1, one)
        Assert.Equal(2, two)
    | result -> failwithf "located guard did not use its generic fallback: %A" result

[<Fact>]
let ``toLispVal roundtrips analyzed if`` () =
    let original = parseOk "(if #t 1 2)"
    assertEqv (toLispVal (analyze original)) original

[<Fact>]
let ``toLispVal handles deeply nested core expressions`` () =
    let depth = 100_000
    let mutable expression = CLit Inert
    for _ in 1..depth do
        expression <- CDefine(CVar "deep-binding", expression)

    let mutable value = toLispVal expression
    for _ in 1..depth do
        match value with
        | List [Atom "define"; Atom "deep-binding"; rhs] -> value <- rhs
        | other -> failwithf "expected nested definition, got %s" (showVal other)
    match value with
    | Inert -> ()
    | other -> failwithf "expected inert leaf, got %s" (showVal other)

[<Fact>]
let ``showCore handles deeply nested core expressions`` () =
    let depth = 100_000
    let mutable expression = CVar "leaf"
    for _ in 1..depth do
        expression <- CReset expression

    let rendered = showCore expression
    Assert.Equal(depth * 8 + 8, rendered.Length)
    Assert.StartsWith(System.String.Concat(System.Linq.Enumerable.Repeat("(reset ", depth)), rendered)
    Assert.EndsWith("var:leaf" + System.String(')', depth), rendered)

[<Fact>]
let ``expression tree helpers compile their live core shapes`` () =
    let env = freshEnv ()
    let invoke expression =
        compileToFunc expression
        |> fun compiled -> run (compiled.Invoke(env, newContinuation env))

    match invoke (CLit (Obj 1)) with
    | Choice2Of2 (Obj (:? int as value)) -> Assert.Equal(1, value)
    | result -> failwithf "unexpected literal result: %A" result

    match invoke (CVar "+") with
    | Choice2Of2 (Applicative _) -> ()
    | result -> failwithf "unexpected lookup result: %A" result

    match invoke (CIf(CLit (Bool true), CLit (Obj 2), CLit (Obj 3))) with
    | Choice2Of2 (Obj (:? int as value)) -> Assert.Equal(2, value)
    | result -> failwithf "unexpected conditional result: %A" result

    match invoke (CApp(CVar "+", [CLit (Obj 1); CLit (Obj 2)])) with
    | Choice2Of2 (Obj (:? int as value)) -> Assert.Equal(3, value)
    | result -> failwithf "unexpected application result: %A" result

[<Fact>]
let ``compiled arithmetic and define`` () =
    let env = freshEnv ()
    let cont = newContinuation env
    match evalCompiled env cont (parseOk "(+ 10 32)") with
    | Choice2Of2 (Obj n) -> Assert.Equal(42, n :?> int)
    | Choice2Of2 v -> failwith (showVal v)
    | Choice1Of2 e -> failwith (showError e)

    match evalCompiled env cont (parseOk "(define x 5)") with
    | Choice2Of2 Inert -> ()
    | Choice2Of2 v -> failwith (showVal v)
    | Choice1Of2 e -> failwith (showError e)

    match evalCompiled env cont (parseOk "(+ x 1)") with
    | Choice2Of2 (Obj n) -> Assert.Equal(6, n :?> int)
    | Choice2Of2 v -> failwith (showVal v)
    | Choice1Of2 e -> failwith (showError e)

[<Fact>]
let ``compiled operative path keeps operands unevaluated`` () =
    let env = freshEnv ()
    ignore (evalIn env "(define q (vau (x) _ x))")
    match evalCompiled env (newContinuation env) (parseOk "(q (+ 1 2))") with
    | Choice2Of2 (List [Atom "+"; Obj a; Obj b]) ->
        Assert.Equal(1, a :?> int)
        Assert.Equal(2, b :?> int)
    | Choice2Of2 v -> failwith (showVal v)
    | Choice1Of2 e -> failwith (showError e)

[<Fact>]
let ``compiled named operator lookup preserves error parity`` () =
    assertParitySession ["(missing-combiner 42)"]

[<Fact>]
let ``compiled computed operator retains general evaluation`` () =
    assertParitySession ["((if #t + -) 20 22)"]

[<Fact>]
let ``generated programs preserve interpreter compiler and package parity`` () =
    let rec generateNumber depth seed =
        if depth = 0 then string ((seed % 19) - 9)
        else
            match seed % 5 with
            | 0 -> $"(+ {generateNumber (depth - 1) (seed + 1)} {generateNumber (depth - 1) (seed + 2)})"
            | 1 -> $"(- {generateNumber (depth - 1) (seed + 3)} {generateNumber (depth - 1) (seed + 4)})"
            | 2 -> $"(* {generateNumber (depth - 1) (seed + 5)} {generateNumber (depth - 1) (seed + 6)})"
            | 3 ->
                $"(if (< {generateNumber (depth - 1) (seed + 7)} {generateNumber (depth - 1) (seed + 8)}) {generateNumber (depth - 1) (seed + 9)} {generateNumber (depth - 1) (seed + 10)})"
            | _ ->
                $"((lambda (value) (+ value {generateNumber (depth - 1) (seed + 11)})) {generateNumber (depth - 1) (seed + 12)})"

    let names = [ for index in 0..63 -> $"generated{index}" ]
    let definitions =
        names
        |> List.mapi (fun index name -> $"(define {name} {generateNumber 3 (index * 13 + 1)})")
    let listArguments = String.concat " " names
    let source = String.concat "\n" (definitions @ [$"(list {listArguments})"])

    let runInterpreted () =
        match bootstrapEnv (), readExprListFromSource "generated-artifact.ikr" source with
        | Choice1Of2 error, _
        | _, Choice1Of2 error -> Choice1Of2 error
        | Choice2Of2 env, Choice2Of2 forms ->
            let mutable result = Choice2Of2 Inert
            for form in forms do
                match result with
                | Choice1Of2 _ -> ()
                | Choice2Of2 _ -> result <- eval env (newContinuation env) form
            result

    let runCompiled () =
        match bootstrapEnv () with
        | Choice1Of2 error -> Choice1Of2 error
        | Choice2Of2 env -> runSource env "generated-artifact.ikr" source

    let directory = Path.Combine(Path.GetTempPath(), $"ironkernel-artifact-{Guid.NewGuid():N}")
    Directory.CreateDirectory(directory) |> ignore
    let script = Path.Combine(directory, "generated.ikr")
    let package = Path.Combine(directory, "generated.ikc")
    try
        File.WriteAllText(script, source)
        match compileFileToPackage script package with
        | Choice1Of2 error -> failwithf "generated package compilation failed: %s" (showError error)
        | Choice2Of2 _ -> ()

        let interpreted = runInterpreted () |> observe
        let compiled = runCompiled () |> observe
        let packaged = loadIkc package |> observe
        Assert.Equal(interpreted, compiled)
        Assert.Equal(interpreted, packaged)
    finally
        Directory.Delete(directory, true)

[<Fact>]
let ``ikc emit and load`` () =
    let dir = System.IO.Path.GetTempPath()
    let src = System.IO.Path.Combine(dir, "ik-compiler-test.ikr")
    let outp = System.IO.Path.Combine(dir, "ik-compiler-test.ikc")
    let sourceSentinel = "IKC_SOURCE_PAYLOAD_SENTINEL"
    System.IO.File.WriteAllText(src, "; " + sourceSentinel + "\n(+ 20 22)")
    match compileFileToPackage src outp with
    | Choice1Of2 e -> failwith (showError e)
    | Choice2Of2 path ->
        Assert.True(System.IO.File.Exists path)
        let bytes = System.IO.File.ReadAllBytes path
        Assert.Equal("IKC2", System.Text.Encoding.ASCII.GetString(bytes, 0, 4))
        Assert.DoesNotContain(sourceSentinel, System.Text.Encoding.UTF8.GetString bytes)
        match loadIkc path with
        | Choice2Of2 (Obj n) -> Assert.Equal(42, n :?> int)
        | Choice2Of2 v -> failwith (showVal v)
        | Choice1Of2 e -> failwith (showError e)

[<Fact>]
let ``ikc guard rehydrates and deoptimizes after rebinding`` () =
    let directory = System.IO.Path.Combine(System.IO.Path.GetTempPath(), $"ironkernel-guard-{System.Guid.NewGuid():N}")
    System.IO.Directory.CreateDirectory(directory) |> ignore
    let source = System.IO.Path.Combine(directory, "guard.ikr")
    let package = System.IO.Path.Combine(directory, "guard.ikc")
    try
        System.IO.File.WriteAllText(source, "(define if (vau operands caller operands))\n(if 1 2 3)")
        match compileFileToPackage source package with
        | Choice1Of2 error -> failwith (showError error)
        | Choice2Of2 _ ->
            match loadIkc package with
            | Choice2Of2 (List [Obj (:? int as one); Obj (:? int as two); Obj (:? int as three)]) ->
                Assert.Equal(1, one)
                Assert.Equal(2, two)
                Assert.Equal(3, three)
            | result -> failwithf "portable guard did not deoptimize: %A" result
    finally
        System.IO.Directory.Delete(directory, true)

[<Fact>]
let ``ikc binds runtime arguments without source parsing`` () =
    let directory = System.IO.Path.Combine(System.IO.Path.GetTempPath(), $"ironkernel-args-{System.Guid.NewGuid():N}")
    System.IO.Directory.CreateDirectory(directory) |> ignore
    let source = System.IO.Path.Combine(directory, "args.ikr")
    let package = System.IO.Path.Combine(directory, "args.ikc")
    try
        System.IO.File.WriteAllText(source, "(car args)")
        match compileFileToPackage source package with
        | Choice1Of2 error -> failwith (showError error)
        | Choice2Of2 _ ->
            match loadIkcWithArgs package ["portable"] with
            | Choice2Of2 (Obj (:? string as value)) -> Assert.Equal("portable", value)
            | result -> failwithf "unexpected packaged argument result: %A" result
    finally
        System.IO.Directory.Delete(directory, true)

[<Fact>]
let ``analyzeAndCompile multiple top-level forms`` () =
    match analyzeAndCompile "(define a 1) (+ a 2)" with
    | Choice2Of2 [_; _] -> ()
    | Choice2Of2 xs -> failwithf "expected 2 forms, got %d" (List.length xs)
    | Choice1Of2 e -> failwith (showError e)

[<Fact>]
let ``static backend emits direct managed entry points without source compilation`` () =
    let expressions = analyzeForms [parseOk "(+ 20 22)"]
    match generateProgram Minimal expressions with
    | Error error -> failwith error
    | Ok source ->
        Assert.Contains("appNamed env cont \"+\" [|Obj(box 20); Obj(box 22)|]", source)
        Assert.DoesNotContain("(+ 20 22)", source)
        Assert.DoesNotContain("Parser", source)
        Assert.DoesNotContain("Expression.Compile", source)

let private invokeSite (compiled: KernelFunc) env =
    match run (compiled.Invoke(env, newContinuation env)) with
    | Choice2Of2 value -> value
    | Choice1Of2 error -> failwith (showError error)

[<Fact>]
let ``inline cache observes rebinding at the same call site`` () =
    let env = freshEnv ()
    ignore (evalIn env "(define f (wrap (vau (x) _ x)))")
    let compiled = compileLispValGuarded env (parseOk "(f 41)")
    assertEqv (invokeSite compiled env) (Obj (41 :> obj))
    // Redefinition bumps the binding cell version; the cached combiner must drop.
    ignore (evalIn env "(define f (wrap (vau (x) _ (+ x 1))))")
    assertEqv (invokeSite compiled env) (Obj (42 :> obj))

[<Fact>]
let ``inline cache observes shadowing definitions in child frames`` () =
    let parent = freshEnv ()
    ignore (evalIn parent "(define f (wrap (vau (x) _ x)))")
    let child = newEnv [parent]
    let compiled = compileLispValGuarded child (parseOk "(f 41)")
    assertEqv (invokeSite compiled child) (Obj (41 :> obj))
    // Defining f in the child grows its frame; the cached parent cell must drop.
    let replacement = evalIn parent "(wrap (vau (x) _ (+ x 1)))"
    match defineVar child "f" replacement with
    | Choice1Of2 error -> failwith (showError error)
    | Choice2Of2 _ -> ()
    assertEqv (invokeSite compiled child) (Obj (42 :> obj))

[<Fact>]
let ``inline cache stays correct across alternating environments`` () =
    let envA = freshEnv ()
    let envB = freshEnv ()
    ignore (evalIn envA "(define f (wrap (vau (x) _ x)))")
    ignore (evalIn envB "(define f (wrap (vau (x) _ (+ x 1))))")
    let compiled = compileLispValGuarded envA (parseOk "(f 41)")
    assertEqv (invokeSite compiled envA) (Obj (41 :> obj))
    assertEqv (invokeSite compiled envB) (Obj (42 :> obj))
    assertEqv (invokeSite compiled envA) (Obj (41 :> obj))

[<Fact>]
let ``inline cache preserves raw operands for operatives`` () =
    let env = freshEnv ()
    ignore (evalIn env "(define q (vau (x) _ x))")
    ignore (evalIn env "(define whatever 99)")
    let compiled = compileLispValGuarded env (parseOk "(q whatever)")
    // Operative dispatch must see the raw operand tree, not the bound value.
    assertEqv (invokeSite compiled env) (Atom "whatever")
    assertEqv (invokeSite compiled env) (Atom "whatever")

[<Fact>]
let ``inline cache dispatches per environment under concurrent invocation`` () =
    // A host embedding the compiler can invoke one compiled form from several
    // threads. Publishing the cache field by field let a caller validate its own
    // environment and then dispatch a combiner another caller had just stored,
    // silently returning the other environment's result. Long parent chains
    // widen the resolution window the race needs.
    let build result =
        let root = freshEnv ()
        ignore (evalIn root $"(define f (wrap (vau (x) _ {result})))")
        let mutable env = root
        for _ in 1..1000 do
            env <- newEnv [env]
        env

    let envA = build 1
    let envB = build 2
    let compiled = compileLispValGuarded envA (parseOk "(f 0)")
    let mismatches = ref 0

    System.Threading.Tasks.Parallel.For(
        0,
        500_000,
        System.Action<int>(fun index ->
            let env, expected = if index % 2 = 0 then envA, 1 else envB, 2
            match run (compiled.Invoke(env, newContinuation env)) with
            | Choice2Of2 (Obj (:? int as actual)) when actual = expected -> ()
            | _ -> System.Threading.Interlocked.Increment(&mismatches.contents) |> ignore))
    |> ignore

    Assert.Equal(0, mismatches.Value)

[<Fact>]
let ``inline cache reports unbound operand variables`` () =
    let env = freshEnv ()
    let compiled = compileLispValGuarded env (parseOk "(+ missing 1)")
    match run (compiled.Invoke(env, newContinuation env)) with
    | Choice1Of2 (UnboundVar(_, "missing")) -> ()
    | result -> failwithf "expected unbound operand error, got %A" result
    // Binding the operand afterwards must succeed through the same site.
    match defineVar env "missing" (Obj (41 :> obj)) with
    | Choice1Of2 error -> failwith (showError error)
    | Choice2Of2 _ -> ()
    assertEqv (invokeSite compiled env) (Obj (42 :> obj))

// ADR 0004 phase 2: compiled procedure bodies live in the continuation as a list
// of compiled forms. Phase 3 fills `compiledBody` in automatically; these build it
// by hand so the representation and its tail-call rule are exercised now.

/// Compiles each source form and adapts it to the plain function `CompiledCode` holds.
let private compiledBody env sources =
    sources
    |> List.map (fun source ->
        let compiled = compileLispValGuarded env (parseOk source)
        fun (e: LispVal) (c: LispVal) -> compiled.Invoke(e, c))

/// Defines `name` as an applicative whose body is compiled rather than interpreted.
let private defineCompiledProcedure env name formals sources =
    let operative =
        Operative
            { prms = parseOk formals
              envarg = "_"
              body = List.map parseOk sources
              closure = env
              compiledBody = Some(compiledBody env sources) }
    match defineVar env name (Applicative operative) with
    | Choice1Of2 error -> failwith (showError error)
    | Choice2Of2 _ -> ()

[<Fact>]
let ``compiled body runs its forms in order and yields the last value`` () =
    let env = freshEnv ()
    defineCompiledProcedure env "run" "()" [ "(define a 1)"; "(define b 2)"; "(+ a b)" ]
    assertEval env "(run)" (Obj (3 :> obj))

[<Fact>]
let ``compiled body propagates errors from any form`` () =
    let env = freshEnv ()
    defineCompiledProcedure env "run" "()" [ "(define a 1)"; "missing"; "(define b 2)" ]
    match evalRaw Compiled env "(run)" with
    | Choice1Of2 (UnboundVar (_, "missing")) -> ()
    | result -> failwithf "unexpected error result: %A" result

[<Fact>]
let ``compiled body sees its own frame and the caller's arguments`` () =
    let env = freshEnv ()
    defineCompiledProcedure env "twice" "(n)" [ "(+ n n)" ]
    assertEval env "(twice 21)" (Obj (42 :> obj))

/// Length of a continuation's `nextCont` chain. Proper tail calls keep this
/// bounded; a missed tail call adds one frame per iteration.
let rec private continuationDepth value =
    match value with
    | Continuation (record, _, _) ->
        match record.nextCont with
        | Some next -> 1 + continuationDepth next
        | None -> 1
    | _ -> 0

[<Fact>]
let ``self tail call through a compiled body does not grow the continuation`` () =
    // The last form of a compiled body leaves `CompiledCode []` as the caller's
    // continuation. If operative application does not treat that as a tail call, a
    // frame is retained per iteration. The trampoline keeps the CLR stack flat
    // either way and still returns the right answer, so the leak is only visible in
    // the continuation captured at the deepest point.
    withKernel (fun env ->
        ignore (evalIn env "(define captured (vector 0))")
        defineCompiledProcedure
            env
            "countdown"
            "(n)"
            [ "(if (eqv? n 0) (vector-set! captured 0 (call/cc (lambda (k) k))) (countdown (- n 1)))" ]

        let depthAfter iterations =
            ignore (evalIn env (sprintf "(countdown %d)" iterations))
            match evalIn env "(vector-ref captured 0)" with
            | Continuation _ as continuation -> continuationDepth continuation
            | other -> failwithf "expected a captured continuation, got %A" other

        let shallow = depthAfter 10
        let deep = depthAfter 1000
        Assert.Equal(shallow, deep))

[<Fact>]
let ``continuation captured inside a compiled body resumes the remaining forms`` () =
    // Resuming re-enters the body part-way through, which is why a body stays a list
    // of compiled forms rather than one opaque delegate.
    withKernel (fun env ->
        ignore (evalIn env "(define store (vector 0))")
        ignore (evalIn env "(define saved (vector 0))")
        defineCompiledProcedure
            env
            "record"
            "()"
            [ "(vector-set! saved 0 (call/cc (lambda (k) k)))"
              "(vector-set! store 0 (+ (vector-ref store 0) 1))"
              "(vector-ref store 0)" ]

        assertEval env "(record)" (Obj (1 :> obj))
        ignore (evalIn env "((vector-ref saved 0) 0)")
        assertEval env "(vector-ref store 0)" (Obj (2 :> obj)))

[<Fact>]
let ``operative bodies are compiled on first application`` () =
    withKernel (fun env ->
        ignore (evalIn env "(define twice (lambda (n) (+ n n)))")
        let operativeOf name =
            match getVar' env name with
            | Some (Applicative (Operative record)) -> record
            | other -> failwithf "expected an applicative operative, got %A" other

        // Nothing is compiled until the combiner is actually applied.
        Assert.True((operativeOf "twice").compiledBody.IsNone)
        assertEval env "(twice 21)" (Obj (42 :> obj))
        Assert.True((operativeOf "twice").compiledBody.IsSome)

        // The memo is reused rather than recompiled per call.
        let compiled = (operativeOf "twice").compiledBody
        assertEval env "(twice 1)" (Obj (2 :> obj))
        Assert.Same(Option.get compiled, Option.get (operativeOf "twice").compiledBody))
