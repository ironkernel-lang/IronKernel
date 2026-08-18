namespace IronKernel

module Source =

    open Ast

    type LocatedValue = {
        kind : LocatedValueKind
        span : SourceSpan
    }

    and LocatedValueKind =
        | LAtom of string
        | LList of LocatedValue list
        | LDottedList of LocatedValue list * LocatedValue
        | LVector of LocatedValue array
        | LLiteral of LispVal
        | LQuote of LocatedValue

    type private ConversionWork =
        | Convert of LocatedValue
        | BuildList of int
        | BuildDottedList of int
        | BuildVector of int
        | BuildQuote

    let spanOf value = value.span

    let toLispVal value =
        let mutable pending = [Convert value]
        let mutable completed = []

        let takeCompleted count =
            let mutable values = []
            for _ in 1..count do
                match completed with
                | value :: rest ->
                    values <- value :: values
                    completed <- rest
                | [] -> invalidOp "Located value conversion stack is incomplete"
            values

        while not pending.IsEmpty do
            let work = pending.Head
            pending <- pending.Tail
            match work with
            | Convert located ->
                match located.kind with
                | LAtom name -> completed <- Atom name :: completed
                | LList values ->
                    pending <- BuildList values.Length :: pending
                    for child in List.rev values do
                        pending <- Convert child :: pending
                | LDottedList (head, tail) ->
                    pending <- BuildDottedList head.Length :: pending
                    pending <- Convert tail :: pending
                    for child in List.rev head do
                        pending <- Convert child :: pending
                | LVector values ->
                    pending <- BuildVector values.Length :: pending
                    for index = values.Length - 1 downto 0 do
                        pending <- Convert values.[index] :: pending
                | LLiteral literal -> completed <- literal :: completed
                | LQuote quoted ->
                    pending <- Convert quoted :: BuildQuote :: pending
            | BuildList count ->
                completed <- ofList (takeCompleted count) :: completed
            | BuildDottedList headCount ->
                match takeCompleted (headCount + 1) |> List.splitAt headCount with
                | head, [tail] -> completed <- (ofDotted head tail) :: completed
                | _ -> invalidOp "Located dotted list conversion is incomplete"
            | BuildVector count ->
                completed <- Vector(Array.ofList (takeCompleted count)) :: completed
            | BuildQuote ->
                match takeCompleted 1 with
                | [quoted] -> completed <- ofList [Atom "quote"; quoted] :: completed
                | _ -> invalidOp "Located quote conversion is incomplete"

        match completed with
        | [result] -> result
        | _ -> invalidOp "Located value conversion did not produce one result"

    let sourceLineAt (source: string) (line: int64) =
        if line < 1L then None
        else
            source.Replace("\r\n", "\n").Split('\n')
            |> Array.tryItem (int line - 1)

    let contains outer inner =
        outer.sourceName = inner.sourceName
        && outer.startPosition.offset <= inner.startPosition.offset
        && outer.endPosition.offset >= inner.endPosition.offset
