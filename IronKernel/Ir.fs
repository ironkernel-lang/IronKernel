namespace IronKernel

/// Core intermediate representation for the Kernel compiler.
/// Surface programs remain homoiconic LispVal trees; analysis produces CoreExpr.
module Ir =

    open Ast
    open SymbolTable
    open Contracts

    /// Explicit core forms after analysis. Residual wraps trees that stay interpreted.
    /// COperate retains raw operand syntax so runtime combiner dispatch can distinguish
    /// operative calls from applicative calls without changing Kernel semantics.
    type CoreExpr =
        | CLit of LispVal
        | CVar of string
        | CQuote of LispVal
        | CIf of CoreExpr * CoreExpr * CoreExpr
        | CSeq of CoreExpr list
        | CDefine of CoreExpr * CoreExpr
        | CVau of formals: LispVal * envarg: string * body: CoreExpr list
        | CApp of op: CoreExpr * args: CoreExpr list
        | COperate of op: CoreExpr * operands: LispVal list
        | CIntrinsicOperate of identity: PrimitiveIdentity * operands: LispVal list
        | CGuarded of guard: BindingGuard * specialized: CoreExpr * fallback: CoreExpr
        | CContractFold of guard: ContractGuard * folded: LispVal * fallback: CoreExpr
        | CEval of envExpr: CoreExpr * expr: CoreExpr
        | CReset of CoreExpr
        | CResidual of LispVal
        | CLocated of span: SourceSpan * sourceLine: string option * expression: CoreExpr

    type private CoreRenderWork =
        | RenderCore of CoreExpr
        | Append of string

    let showCore expression =
        let output = System.Text.StringBuilder()
        let mutable pending = [RenderCore expression]

        let prependExpressions expressions =
            let mutable hasLaterExpression = false
            for child in List.rev expressions do
                if hasLaterExpression then
                    pending <- RenderCore child :: Append " " :: pending
                else
                    pending <- RenderCore child :: pending
                    hasLaterExpression <- true

        while not pending.IsEmpty do
            let work = pending.Head
            pending <- pending.Tail
            match work with
            | Append text -> output.Append(text) |> ignore
            | RenderCore current ->
                match current with
                | CLit value -> output.Append("lit:").Append(showVal value) |> ignore
                | CVar name -> output.Append("var:").Append(name) |> ignore
                | CQuote value -> output.Append("quote:").Append(showVal value) |> ignore
                | CIf(condition, consequent, alternative) ->
                    pending <-
                        Append "(if "
                        :: RenderCore condition
                        :: Append " "
                        :: RenderCore consequent
                        :: Append " "
                        :: RenderCore alternative
                        :: Append ")"
                        :: pending
                | CSeq expressions ->
                    pending <- Append ")" :: pending
                    prependExpressions expressions
                    pending <- Append "(seq " :: pending
                | CDefine(lhs, rhs) ->
                    pending <-
                        Append "(define "
                        :: RenderCore lhs
                        :: Append " "
                        :: RenderCore rhs
                        :: Append ")"
                        :: pending
                | CVau(formals, envarg, _) ->
                    output
                        .Append("(vau ")
                        .Append(showVal formals)
                        .Append(" ")
                        .Append(envarg)
                        .Append(" ...)")
                    |> ignore
                | CApp(operator, args) ->
                    pending <- Append ")" :: pending
                    prependExpressions args
                    pending <- Append " " :: pending
                    pending <- RenderCore operator :: pending
                    pending <- Append "(" :: pending
                | COperate(operator, _) ->
                    pending <-
                        Append "(operate "
                        :: RenderCore operator
                        :: Append " ...)"
                        :: pending
                | CIntrinsicOperate(identity, _) ->
                    output.Append("(intrinsic ").Append(sprintf "%A" identity).Append(" ...)") |> ignore
                | CGuarded(guard, specialized, _) ->
                    pending <-
                        Append(sprintf "(guard %s " guard.name)
                        :: RenderCore specialized
                        :: Append ")"
                        :: pending
                | CContractFold(guard, folded, _) ->
                    output
                        .Append(sprintf "(contract-fold %s@%d " guard.name guard.version)
                        .Append(showVal folded)
                        .Append(")")
                    |> ignore
                | CEval(environmentExpression, valueExpression) ->
                    pending <-
                        Append "(eval "
                        :: RenderCore environmentExpression
                        :: Append " "
                        :: RenderCore valueExpression
                        :: Append ")"
                        :: pending
                | CReset body ->
                    pending <- Append "(reset " :: RenderCore body :: Append ")" :: pending
                | CResidual value -> output.Append("residual:").Append(showVal value) |> ignore
                | CLocated(_, _, inner) -> pending <- RenderCore inner :: pending

        output.ToString()
