namespace IronKernel

/// Expression-tree / hybrid compiler for Core IR.
/// Compiles statically visible forms to CLR delegates; residual trees fall back
/// to the trampolined interpreter so full Kernel semantics (vau, eval, conts) remain.
module Compiler =

    open System
    open Ast
    open Errors
    open Ir
    open Analyze
    open Eval
    open SymbolTable
    open Contracts
    open PartialEval
    open Choice

    /// Compiled code returns `Step`, so it runs inside the caller's trampoline
    /// rather than starting a nested one. A nested trampoline would consume CLR
    /// stack on every Kernel tail call, collapse escaping continuations into a
    /// finished value, and block on `Await`. See ADR 0004.
    type KernelFunc = Func<LispVal, LispVal, Step>

    type private CompilationWork =
        | CompileExpression of CoreExpr
        | BuildIf
        | BuildSequence of int
        | BuildDefine of string
        | BuildEval
        | BuildApp of LispVal[]
        | BuildOperation of LispVal[]
        | BuildGuarded of BindingGuard
        | BuildContractFold of ContractGuard * LispVal
        | BuildLocated of SourceSpan * string option

    type Helpers =
        static member Continue(env: LispVal, cont: LispVal, v: LispVal) : Step =
            bounceContinue env cont v
        static member Lookup(env: LispVal, cont: LispVal, name: string) : Step =
            match SymbolTable.getVar env name with
            | Choice2Of2 r -> bounceContinue env cont r
            | Choice1Of2 e -> signal cont e
        static member IfThenElse(env: LispVal, cont: LispVal, fc: KernelFunc, fa: KernelFunc, fb: KernelFunc) : Step =
            fc.Invoke(
                env,
                makeCPS env cont (fun e c value _ ->
                    match value with
                    | Bool true -> fa.Invoke(e, c)
                    | Bool false -> fb.Invoke(e, c)
                    | found -> signal c (TypeMismatch("bool", found))))
        static member Seq(env: LispVal, cont: LispVal, forms: KernelFunc[]) : Step =
            if forms.Length = 0 then bounceContinue env cont Inert
            else
                let rec step index e c =
                    if index = forms.Length - 1 then forms.[index].Invoke(e, c)
                    else forms.[index].Invoke(e, makeCPS e c (fun se sc _ _ -> step (index + 1) se sc))
                step 0 env cont
        static member Define(env: LispVal, cont: LispVal, name: string, fr: KernelFunc) : Step =
            fr.Invoke(
                env,
                makeCPS env cont (fun e c value _ ->
                    match SymbolTable.defineVar e name value with
                    | Choice1Of2 error -> signal c error
                    | Choice2Of2 _ -> bounceContinue e c Inert))
        static member EvalForms(env: LispVal, cont: LispVal, fe: KernelFunc, fx: KernelFunc) : Step =
            fe.Invoke(
                env,
                makeCPS env cont (fun e c environmentValue _ ->
                    fx.Invoke(
                        e,
                        makeCPS e c (fun _ xc code _ -> bounceEval environmentValue xc code))))
        /// Kernel combination: evaluate operator, then operate with *unevaluated* operands.
        /// Applicatives evaluate their arguments inside `operate`; operatives see raw trees.
        static member App(env: LispVal, cont: LispVal, fop: KernelFunc, operands: LispVal[]) : Step =
            fop.Invoke(
                env,
                makeCPS env cont (fun e c combiner _ ->
                    bounceOperate e c combiner (Array.toList operands)))
        static member AppNamed(env: LispVal, cont: LispVal, name: string, operands: LispVal[]) : Step =
            RuntimeDispatch.appNamed env cont name operands

    // Plain closures rather than expression trees. `Expression.Lambda(...).Compile()`
    // costs tens of microseconds per node, which was affordable when only top-level
    // forms were compiled once. Procedure bodies are compiled per operative
    // (ADR 0004 phase 3), and combiners built and applied once -- every `let`
    // expands to one -- would pay that cost with nothing to amortise it against.
    let private compileLiteral v = KernelFunc(fun env cont -> Helpers.Continue(env, cont, v))

    let private compileVariable name = KernelFunc(fun env cont -> Helpers.Lookup(env, cont, name))

    let compileToFunc (expr: CoreExpr) : KernelFunc =
        let mutable pending = [CompileExpression expr]
        let mutable completed : KernelFunc list = []

        let takeCompleted count =
            let mutable functions = []
            for _ in 1..count do
                match completed with
                | func :: rest ->
                    functions <- func :: functions
                    completed <- rest
                | [] -> invalidOp "Compiler work stack is incomplete"
            functions

        while not pending.IsEmpty do
            let work = pending.Head
            pending <- pending.Tail
            match work with
            | CompileExpression expression ->
                match expression with
                | CLit v -> completed <- compileLiteral v :: completed
                | CVar name -> completed <- compileVariable name :: completed
                | CQuote v -> completed <- compileLiteral v :: completed
                | CIf (condition, consequent, alternative) ->
                    pending <-
                        CompileExpression condition
                        :: CompileExpression consequent
                        :: CompileExpression alternative
                        :: BuildIf
                        :: pending
                | CSeq expressions ->
                    pending <- BuildSequence expressions.Length :: pending
                    for child in List.rev expressions do
                        pending <- CompileExpression child :: pending
                | CDefine (CVar name, rhs) ->
                    pending <- CompileExpression rhs :: BuildDefine name :: pending
                | CVau (formals, envarg, body) ->
                    let bodyLv = List.map toLispVal body
                    completed <-
                        KernelFunc(fun env cont ->
                            // The same immutable acquisition the `vau` primitive
                            // performs (R-1RK 4.10.3 / 4.7.2, ADR 0005 phase 0): a
                            // compiled $vau captures structure exactly as an
                            // interpreted one does.
                            let op =
                                Operative { prms = acquireImmutable formals
                                            envarg = envarg
                                            body = acquireImmutableForms bodyLv
                                            closure = env
                                            compiledBody = None }
                            bounceContinue env cont op)
                        :: completed
                | CEval (environmentExpression, valueExpression) ->
                    pending <-
                        CompileExpression environmentExpression
                        :: CompileExpression valueExpression
                        :: BuildEval
                        :: pending
                | CReset body ->
                    // Delimited continuations must go through the trampoline interpreter so
                    // shift sees the proper meta-continuation chain (including under begin/applicatives).
                    let form = ofList [Atom "reset"; toLispVal body]
                    completed <- KernelFunc(fun env cont -> bounceEval env cont form) :: completed
                | CApp (operator, args) ->
                    let operands = List.map toLispVal args |> List.toArray
                    pending <- CompileExpression operator :: BuildApp operands :: pending
                | COperate (CVar name, operands) ->
                    // Per-site inline cache: skips binding resolution (and the CPS
                    // argument chain for simple applicative calls) while the
                    // resolved combiner is provably unchanged.
                    let site = RuntimeDispatch.NamedCallSite(name, operands)
                    completed <-
                        KernelFunc(fun env cont -> site.Invoke(env, cont))
                        :: completed
                | COperate (operator, operands) ->
                    pending <-
                        CompileExpression operator
                        :: BuildOperation(List.toArray operands)
                        :: pending
                | CIntrinsicOperate (identity, operands) ->
                    completed <-
                        KernelFunc(fun env cont ->
                            match identity with
                            | PrimitiveIf -> Runtime.if_then_else env cont operands
                            | PrimitiveDefine -> Runtime.define env cont operands
                            | PrimitiveSequence -> Runtime.sequenceForms env cont operands)
                        :: completed
                | CGuarded (guard, specialized, fallback) ->
                    pending <-
                        CompileExpression specialized
                        :: CompileExpression fallback
                        :: BuildGuarded guard
                        :: pending
                | CContractFold (guard, folded, fallback) ->
                    pending <-
                        CompileExpression fallback
                        :: BuildContractFold(guard, folded)
                        :: pending
                | CResidual v ->
                    completed <- KernelFunc(fun env cont -> bounceEval env cont v) :: completed
                | CLocated (span, sourceLine, inner) ->
                    pending <- CompileExpression inner :: BuildLocated(span, sourceLine) :: pending
                | other ->
                    let value = toLispVal other
                    completed <- KernelFunc(fun env cont -> bounceEval env cont value) :: completed
            | BuildIf ->
                match takeCompleted 3 with
                | [condition; consequent; alternative] ->
                    completed <-
                        KernelFunc(fun env cont ->
                            Helpers.IfThenElse(env, cont, condition, consequent, alternative))
                        :: completed
                | _ -> invalidOp "Conditional compilation is incomplete"
            | BuildSequence count ->
                let functions = takeCompleted count |> List.toArray
                completed <- KernelFunc(fun env cont -> Helpers.Seq(env, cont, functions)) :: completed
            | BuildDefine name ->
                match takeCompleted 1 with
                | [rhs] ->
                    completed <- KernelFunc(fun env cont -> Helpers.Define(env, cont, name, rhs)) :: completed
                | _ -> invalidOp "Definition compilation is incomplete"
            | BuildEval ->
                match takeCompleted 2 with
                | [environmentExpression; valueExpression] ->
                    completed <-
                        KernelFunc(fun env cont ->
                            Helpers.EvalForms(env, cont, environmentExpression, valueExpression))
                        :: completed
                | _ -> invalidOp "Eval compilation is incomplete"
            | BuildApp operands ->
                match takeCompleted 1 with
                | [operator] ->
                    completed <-
                        KernelFunc(fun env cont -> Helpers.App(env, cont, operator, operands))
                        :: completed
                | _ -> invalidOp "Application compilation is incomplete"
            | BuildOperation operands ->
                match takeCompleted 1 with
                | [operator] ->
                    completed <- KernelFunc(fun env cont -> Helpers.App(env, cont, operator, operands)) :: completed
                | _ -> invalidOp "Operation compilation is incomplete"
            | BuildGuarded guard ->
                match takeCompleted 2 with
                | [specialized; fallback] ->
                    completed <-
                        KernelFunc(fun env cont ->
                            if bindingGuardMatches env guard then specialized.Invoke(env, cont)
                            else fallback.Invoke(env, cont))
                        :: completed
                | _ -> invalidOp "Guarded compilation is incomplete"
            | BuildContractFold (guard, folded) ->
                match takeCompleted 1 with
                | [fallback] ->
                    completed <-
                        KernelFunc(fun env cont ->
                            if contractGuardMatches env guard then bounceContinue env cont folded
                            else fallback.Invoke(env, cont))
                        :: completed
                | _ -> invalidOp "Contract fold compilation is incomplete"
            | BuildLocated (span, sourceLine) ->
                match takeCompleted 1 with
                | [inner] ->
                    completed <-
                        KernelFunc(fun env cont ->
                            RuntimeDispatch.runLocated env cont span sourceLine inner)
                        :: completed
                | _ -> invalidOp "Located compilation is incomplete"

        match completed with
        | [result] -> result
        | _ -> invalidOp "Compilation did not produce one function"

    let compileLispVal (v: LispVal) = compileToFunc (analyze v)
    let compileLispValGuarded env (v: LispVal) =
        analyzeGuarded env v
        |> partialEvaluate env
        |> compileToFunc

    let compileForms (forms: LispVal list) = List.map compileLispVal forms
    let compileFormsGuarded env forms = List.map (compileLispValGuarded env) forms

    /// Single trampoline entry for compiled code. Everything below this point
    /// returns `Step` and shares this one loop.
    let evalCompiled env cont (v: LispVal) =
        compileLispValGuarded env v |> fun f -> run (f.Invoke(env, cont))

    /// Installs body compilation for operative application (ADR 0004 phase 3).
    /// The runtime cannot reference this assembly, so the tool injects it, exactly
    /// as `RuntimeSourceServices` injects the parser. Bodies are compiled against
    /// the operative's closure environment; guards and call-site caches revalidate
    /// per call, so the child frame each application creates is handled already.
    let installBodyCompiler () =
        Eval.configureBodyCompiler (fun closure body ->
            body
            |> List.map (fun form ->
                let compiled = compileLispValGuarded closure form
                fun (env: LispVal) (cont: LispVal) -> compiled.Invoke(env, cont)))

    let analyzeAndCompile (source: string) : ThrowsError<KernelFunc list> =
        match Parser.readExprList source with
        | Choice1Of2 e -> throwError e
        | Choice2Of2 forms -> returnM (compileForms forms)

    type LocatedKernelFunc = {
        func : KernelFunc
        span : SourceSpan
        sourceLine : string option
    }

    let analyzeAndCompileLocated env sourceName (source: string) : ThrowsError<LocatedKernelFunc list> =
        match Parser.readLocatedExprList sourceName source with
        | Choice1Of2 e -> throwError e
        | Choice2Of2 forms ->
            forms
            |> List.map (fun form ->
                let compiled =
                    analyzeLocatedGuarded env source form
                    |> partialEvaluate env
                    |> compileToFunc
                { func = compiled
                  span = Source.spanOf form
                  sourceLine = Source.sourceLineAt source form.span.startPosition.line })
            |> returnM
