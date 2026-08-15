namespace IronKernel

module PartialEval =

    open Ast
    open Contracts
    open Eval
    open Ir

    type private EvaluationWork =
        | Evaluate of CoreExpr
        | BuildIf
        | BuildSequence of int
        | BuildDefine of CoreExpr
        | BuildGuarded of SymbolTable.BindingGuard * CoreExpr
        | BuildLocated of SourceSpan * string option

    let private isStaticLiteral = function
        | Bool _
        | Inert
        | Nil
        | Keyword _
        | List [] -> true
        | Obj value ->
            isNull value
            || value :? string
            || value :? byte
            || value :? int
            || value :? int64
            || value :? float32
            || value :? double
        | _ -> false

    let private isFoldedValue = isStaticLiteral

    let partialEvaluate env expression =
        let mutable pending = [Evaluate expression]
        let mutable completed = []

        let takeCompleted count =
            let mutable expressions = []
            for _ in 1..count do
                match completed with
                | expression :: rest ->
                    expressions <- expression :: expressions
                    completed <- rest
                | [] -> invalidOp "Partial evaluation stack is incomplete"
            expressions

        while not pending.IsEmpty do
            let work = pending.Head
            pending <- pending.Tail
            match work with
            | Evaluate current ->
                match current with
                | COperate(CVar name, operands) as fallback
                    when List.forall isStaticLiteral operands ->
                    let folded =
                        match tryCreateContractGuard env name with
                        | Some (guard, _) ->
                            match eval env (newContinuation env) (ofList(Atom name :: operands)) with
                            | Choice2Of2 value when isFoldedValue value ->
                                CContractFold(guard, value, fallback)
                            | _ -> fallback
                        | None -> fallback
                    completed <- folded :: completed
                | CIf(condition, consequent, alternative) ->
                    pending <- BuildIf :: pending
                    pending <- Evaluate alternative :: pending
                    pending <- Evaluate consequent :: pending
                    pending <- Evaluate condition :: pending
                | CSeq expressions ->
                    pending <- BuildSequence expressions.Length :: pending
                    for child in List.rev expressions do
                        pending <- Evaluate child :: pending
                | CDefine(lhs, rhs) ->
                    pending <- Evaluate rhs :: BuildDefine lhs :: pending
                | CGuarded(guard, specialized, fallback) ->
                    pending <- Evaluate specialized :: BuildGuarded(guard, fallback) :: pending
                | CLocated(span, sourceLine, inner) ->
                    pending <- Evaluate inner :: BuildLocated(span, sourceLine) :: pending
                | other -> completed <- other :: completed
            | BuildIf ->
                match takeCompleted 3 with
                | [condition; consequent; alternative] ->
                    completed <- CIf(condition, consequent, alternative) :: completed
                | _ -> invalidOp "Partial if evaluation is incomplete"
            | BuildSequence count ->
                completed <- CSeq(takeCompleted count) :: completed
            | BuildDefine lhs ->
                match takeCompleted 1 with
                | [rhs] -> completed <- CDefine(lhs, rhs) :: completed
                | _ -> invalidOp "Partial define evaluation is incomplete"
            | BuildGuarded (guard, fallback) ->
                match takeCompleted 1 with
                | [specialized] -> completed <- CGuarded(guard, specialized, fallback) :: completed
                | _ -> invalidOp "Partial guarded evaluation is incomplete"
            | BuildLocated (span, sourceLine) ->
                match takeCompleted 1 with
                | [inner] -> completed <- CLocated(span, sourceLine, inner) :: completed
                | _ -> invalidOp "Partial located evaluation is incomplete"

        match completed with
        | [result] -> result
        | _ -> invalidOp "Partial evaluation did not produce one result"
