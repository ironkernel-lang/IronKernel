namespace IronKernel

/// Lowers homoiconic LispVal trees to CoreExpr for compilation / IR evaluation.
module Analyze =

    open Ast
    open Ir
    open SymbolTable
    open ClrSugar

    type private ReificationWork =
        | Reify of CoreExpr
        | BuildIf
        | BuildSequence of int
        | BuildDefine
        | BuildVau of LispVal * string * int
        | BuildApp of int
        | BuildOperate of LispVal list
        | BuildEval
        | BuildReset

    /// Guarded analysis runs on an explicit stack. Recursing into the sub-forms of
    /// `if` and `define` instead would grow the CLR stack with the nesting depth of
    /// the program being analyzed, and a few thousand nested conditionals is enough
    /// to overflow it.
    type private GuardedAnalysisWork =
        | AnalyzeGuardedForm of LispVal
        | BuildGuardedIf of BindingGuard * CoreExpr
        | BuildGuardedDefine of BindingGuard * string * CoreExpr
        | BuildGuardedOperate of LispVal list

    type private LocatedAnalysisWork =
        | AnalyzeLocated of Source.LocatedValue
        | BuildLocatedIf of SourceSpan * string option * BindingGuard * CoreExpr
        | BuildLocatedDefine of SourceSpan * string option * BindingGuard * string * CoreExpr
        | BuildLocatedOperate of SourceSpan * string option * LispVal list

    let analyze (value: LispVal) : CoreExpr =
        let mutable current = value
        let mutable pendingOperands = []
        let mutable result = None

        while result.IsNone do
            match current with
            | Atom id -> result <- Some(CVar id)
            | Bool _
            | Keyword _
            | Inert
            | Nil
            | Obj _
            | Vector _
            | Encapsulation _
            | Environment _
            | PrimitiveOperative _
            | ContractedCombiner _
            | Operative _
            | Applicative _
            | Continuation _
            | PromptTag _
            | Resumption _
            | IOFunc _
            | Port _
            | Status _ -> result <- Some(CLit current)
            | List [] -> result <- Some(CLit(List []))
            | DottedList _ as form -> result <- Some(CResidual form)
            | List (Atom name :: args) ->
                // Desugar Clojure-style CLR calls before binding analysis so the
                // hybrid compiler sees ordinary `.` / `new` / `.get` combinations.
                match tryRewrite name args with
                | Some rewritten -> current <- rewritten
                | None -> result <- Some(COperate(CVar name, args))
            | List (op :: args) ->
                // Kernel has no syntactically privileged operator names. Preserve operand
                // trees exactly and let runtime binding lookup select operative semantics.
                // Specialized forms require binding-identity guards, which this analyzer
                // intentionally does not yet have.
                pendingOperands <- args :: pendingOperands
                current <- op
            | other -> result <- Some(CResidual other)

        let mutable analyzed = result.Value
        for operands in pendingOperands do
            analyzed <- COperate(analyzed, operands)
        analyzed

    let analyzeForms (forms: LispVal list) : CoreExpr list =
        List.map analyze forms

    /// Specialized `if` and `define` lower their sub-forms into Core rather than
    /// leaving them as operands for the runtime primitive. `CIntrinsicOperate` hands
    /// the primitive raw syntax, which it then evaluates through the interpreter, so
    /// leaving them there kept every conditional and every definition inside a
    /// compiled body interpreted. The located analyzer below lowers them the same way.
    let analyzeGuarded env (value: LispVal) : CoreExpr =
        let mutable pending = [AnalyzeGuardedForm value]
        let mutable completed : CoreExpr list = []

        let takeCompleted count =
            let mutable expressions = []
            for _ in 1..count do
                match completed with
                | expression :: rest ->
                    expressions <- expression :: expressions
                    completed <- rest
                | [] -> invalidOp "Guarded analysis stack is incomplete"
            expressions

        while not pending.IsEmpty do
            let work = pending.Head
            pending <- pending.Tail
            match work with
            | AnalyzeGuardedForm form ->
                match form with
                // Both spellings: `$if` is the report's name (R-1RK 4.5.2), `if` the
                // dialect's. They denote one combiner, so both deserve the guard.
                | List (Atom ("if" | "$if" as name) :: [condition; consequent; alternative] as whole) ->
                    let fallback = COperate(CVar name, List.tail whole)
                    match tryCreateBindingGuard env name PrimitiveIf with
                    | Some guard ->
                        pending <-
                            AnalyzeGuardedForm condition
                            :: AnalyzeGuardedForm consequent
                            :: AnalyzeGuardedForm alternative
                            :: BuildGuardedIf(guard, fallback)
                            :: pending
                    | None -> completed <- fallback :: completed
                | List (Atom ("define" | "$define!" as definer) :: [Atom name; rhs] as whole) ->
                    let fallback = COperate(CVar definer, List.tail whole)
                    match tryCreateBindingGuard env definer PrimitiveDefine with
                    | Some guard ->
                        pending <-
                            AnalyzeGuardedForm rhs
                            :: BuildGuardedDefine(guard, name, fallback)
                            :: pending
                    | None -> completed <- fallback :: completed
                | List (Atom name :: operands) ->
                    // Prefer a real binding over CLR call sugar (same rule as Eval).
                    match getVar' env name with
                    | Some _ -> completed <- COperate(CVar name, operands) :: completed
                    | None ->
                        match tryRewrite name operands with
                        | Some rewritten -> pending <- AnalyzeGuardedForm rewritten :: pending
                        | None -> completed <- COperate(CVar name, operands) :: completed
                | List (op :: operands) ->
                    pending <- AnalyzeGuardedForm op :: BuildGuardedOperate operands :: pending
                | other -> completed <- analyze other :: completed
            | BuildGuardedIf (guard, fallback) ->
                match takeCompleted 3 with
                | [condition; consequent; alternative] ->
                    completed <-
                        CGuarded(guard, CIf(condition, consequent, alternative), fallback)
                        :: completed
                | _ -> invalidOp "Guarded conditional analysis is incomplete"
            | BuildGuardedDefine (guard, name, fallback) ->
                match takeCompleted 1 with
                | [rhs] ->
                    completed <- CGuarded(guard, CDefine(CVar name, rhs), fallback) :: completed
                | _ -> invalidOp "Guarded definition analysis is incomplete"
            | BuildGuardedOperate operands ->
                match takeCompleted 1 with
                | [operator] -> completed <- COperate(operator, operands) :: completed
                | _ -> invalidOp "Guarded operation analysis is incomplete"

        match completed with
        | [result] -> result
        | _ -> invalidOp "Guarded analysis did not produce one expression"

    let analyzeFormsGuarded env forms =
        List.map (analyzeGuarded env) forms

    let analyzeLocatedGuarded env (source: string) (value: Source.LocatedValue) =
        let sourceLines = source.Replace("\r\n", "\n").Split('\n')
        let sourceLineAt line =
            if line < 1L then None
            else sourceLines |> Array.tryItem (int line - 1)
        let isLocatedAtom (value: Source.LocatedValue) =
            match value.kind with
            | Source.LAtom _ -> true
            | _ -> false

        let mutable pending = [AnalyzeLocated value]
        let mutable completed = []

        let takeCompleted count =
            let mutable expressions = []
            for _ in 1..count do
                match completed with
                | expression :: rest ->
                    expressions <- expression :: expressions
                    completed <- rest
                | [] -> invalidOp "Located analysis stack is incomplete"
            expressions

        while not pending.IsEmpty do
            let work = pending.Head
            pending <- pending.Tail
            match work with
            | AnalyzeLocated located ->
                let sourceLine = sourceLineAt located.span.startPosition.line
                match located.kind with
                | Source.LList (operator :: operands) when not (isLocatedAtom operator) ->
                    pending <-
                        AnalyzeLocated operator
                        :: BuildLocatedOperate(
                            located.span,
                            sourceLine,
                            List.map Source.toLispVal operands)
                        :: pending
                | _ ->
                    let expression = analyzeGuarded env (Source.toLispVal located)
                    match located.kind, expression with
                    | Source.LList [_; condition; consequent; alternative],
                      CGuarded (guard, CIf _, fallback) ->
                        pending <-
                            AnalyzeLocated condition
                            :: AnalyzeLocated consequent
                            :: AnalyzeLocated alternative
                            :: BuildLocatedIf(located.span, sourceLine, guard, fallback)
                            :: pending
                    | Source.LList [_; { kind = Source.LAtom name }; rhs],
                      CGuarded (guard, CDefine _, fallback) ->
                        pending <-
                            AnalyzeLocated rhs
                            :: BuildLocatedDefine(located.span, sourceLine, guard, name, fallback)
                            :: pending
                    | Source.LList (operator :: operands), COperate (_, rawOperands) ->
                        let isClrSugar =
                            match operator.kind with
                            | Source.LAtom name when getVar' env name |> Option.isNone ->
                                tryRewrite name (List.map Source.toLispVal operands)
                                |> Option.isSome
                            | _ -> false
                        if isClrSugar then
                            completed <- CLocated(located.span, sourceLine, expression) :: completed
                        else
                            pending <-
                                AnalyzeLocated operator
                                :: BuildLocatedOperate(located.span, sourceLine, rawOperands)
                                :: pending
                    | _ -> completed <- CLocated(located.span, sourceLine, expression) :: completed
            | BuildLocatedIf (span, sourceLine, guard, fallback) ->
                match takeCompleted 3 with
                | [condition; consequent; alternative] ->
                    completed <-
                        CLocated(
                            span,
                            sourceLine,
                            CGuarded(guard, CIf(condition, consequent, alternative), fallback))
                        :: completed
                | _ -> invalidOp "Located conditional analysis is incomplete"
            | BuildLocatedDefine (span, sourceLine, guard, name, fallback) ->
                match takeCompleted 1 with
                | [rhs] ->
                    completed <-
                        CLocated(span, sourceLine, CGuarded(guard, CDefine(CVar name, rhs), fallback))
                        :: completed
                | _ -> invalidOp "Located definition analysis is incomplete"
            | BuildLocatedOperate (span, sourceLine, operands) ->
                match takeCompleted 1 with
                | [operator] ->
                    completed <- CLocated(span, sourceLine, COperate(operator, operands)) :: completed
                | _ -> invalidOp "Located operation analysis is incomplete"

        match completed with
        | [result] -> result
        | _ -> invalidOp "Located analysis did not produce one expression"

    /// Reify CoreExpr back to a LispVal tree for residual evaluation.
    let toLispVal expression =
        let mutable pending = [Reify expression]
        let mutable completed = []

        let takeCompleted count =
            let mutable values = []
            for _ in 1..count do
                match completed with
                | value :: rest ->
                    values <- value :: values
                    completed <- rest
                | [] -> invalidOp "Core reification stack is incomplete"
            values

        while not pending.IsEmpty do
            let work = pending.Head
            pending <- pending.Tail
            match work with
            | Reify current ->
                match current with
                | CLit value -> completed <- value :: completed
                | CVar name -> completed <- Atom name :: completed
                | CQuote value -> completed <- List [Atom "quote"; value] :: completed
                | CIf(condition, consequent, alternative) ->
                    pending <-
                        Reify condition
                        :: Reify consequent
                        :: Reify alternative
                        :: BuildIf
                        :: pending
                | CSeq expressions ->
                    pending <- BuildSequence expressions.Length :: pending
                    for child in List.rev expressions do
                        pending <- Reify child :: pending
                | CDefine(lhs, rhs) ->
                    pending <- Reify lhs :: Reify rhs :: BuildDefine :: pending
                | CVau(formals, envarg, body) ->
                    pending <- BuildVau(formals, envarg, body.Length) :: pending
                    for child in List.rev body do
                        pending <- Reify child :: pending
                | CApp(operator, args) ->
                    pending <- BuildApp args.Length :: pending
                    for child in List.rev args do
                        pending <- Reify child :: pending
                    pending <- Reify operator :: pending
                | COperate(operator, operands) ->
                    pending <- Reify operator :: BuildOperate operands :: pending
                | CIntrinsicOperate(PrimitiveIf, operands) ->
                    completed <- List (Atom "if" :: operands) :: completed
                | CIntrinsicOperate(PrimitiveDefine, operands) ->
                    completed <- List (Atom "define" :: operands) :: completed
                | CGuarded(_, _, fallback)
                | CContractFold(_, _, fallback) ->
                    pending <- Reify fallback :: pending
                | CEval(environmentExpression, valueExpression) ->
                    pending <-
                        Reify environmentExpression
                        :: Reify valueExpression
                        :: BuildEval
                        :: pending
                | CReset body -> pending <- Reify body :: BuildReset :: pending
                | CResidual value -> completed <- value :: completed
                | CLocated(_, _, inner) -> pending <- Reify inner :: pending
            | BuildIf ->
                match takeCompleted 3 with
                | [condition; consequent; alternative] ->
                    completed <- List [Atom "if"; condition; consequent; alternative] :: completed
                | _ -> invalidOp "Conditional reification is incomplete"
            | BuildSequence count ->
                completed <- List (Atom "sequence" :: takeCompleted count) :: completed
            | BuildDefine ->
                match takeCompleted 2 with
                | [lhs; rhs] -> completed <- List [Atom "define"; lhs; rhs] :: completed
                | _ -> invalidOp "Definition reification is incomplete"
            | BuildVau(formals, envarg, bodyCount) ->
                completed <-
                    List (Atom "vau" :: formals :: Atom envarg :: takeCompleted bodyCount)
                    :: completed
            | BuildApp argumentCount ->
                completed <- List (takeCompleted (argumentCount + 1)) :: completed
            | BuildOperate operands ->
                match takeCompleted 1 with
                | [operator] -> completed <- List (operator :: operands) :: completed
                | _ -> invalidOp "Operation reification is incomplete"
            | BuildEval ->
                match takeCompleted 2 with
                | [environmentExpression; valueExpression] ->
                    completed <- List [Atom "eval"; environmentExpression; valueExpression] :: completed
                | _ -> invalidOp "Eval reification is incomplete"
            | BuildReset ->
                match takeCompleted 1 with
                | [body] -> completed <- List [Atom "reset"; body] :: completed
                | _ -> invalidOp "Reset reification is incomplete"

        match completed with
        | [result] -> result
        | _ -> invalidOp "Core reification did not produce one value"
