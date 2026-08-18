namespace IronKernel

module Parser =

    open FParsec
    open Ast
    open Errors
    open Source

    let symbol : Parser<char,unit> = anyOf  "!#$%|*+-/:<=>?@^_~."

    let comment = pchar ';' >>. restOfLine true
    let whiteSpace = anyOf " \t\r\n" |>> fun x -> string x

    let ws  = skipMany  (whiteSpace <|> comment)
    let ws1 = skipMany1 (whiteSpace <|> comment)

    let endBy p sep = many ( p .>> sep)

    let stringLiteral  : Parser<string,unit>=
        let normalCharSnippet = manySatisfy (fun c -> c <> '\\' && c <> '"')
        let escapedChar = pstring "\\" >>. (anyOf "\\nrt\"" |>> function
                                                            | 'n' -> "\n"
                                                            | 'r' -> "\r"
                                                            | 't' -> "\t"
                                                            | c   -> string c)
        between (pstring "\"") (pstring "\"")
                (stringsSepBy normalCharSnippet escapedChar)


    let parseString  : Parser<LispVal,unit> = stringLiteral |>> makeObj

    let parseAtom : Parser<LispVal,unit> =
        parse {
            let! first = letter <|> symbol
            let! rest = manyChars (letter <|> digit <|> symbol)

            return
                if first.Equals(':') then Keyword rest
                else
                    let atom = first.ToString() + rest
                    match atom with
                    | "#t" -> Bool(true)
                    | "#f" -> Bool(false)
                    | "#inert" -> Inert
                    | "#ignore" -> Ignore
                    // R-1RK 12.4 gives the exact infinities of 12.3.2 an external
                    // representation. They read as atoms because `#`, `+` and `-` are
                    // all symbol characters, so they are recognised here rather than
                    // in the number parser.
                    | "#e+infinity" -> Obj(box ExactPositiveInfinity)
                    | "#e-infinity" -> Obj(box ExactNegativeInfinity)
                    | _    -> Atom atom }

    // We want to support decimal or hexadecimal numbers with an optional minus
    // sign. Integers may have an 'L' suffix to indicate that the number should
    // be parsed as a 64-bit integer.
    let numberFormat =     NumberLiteralOptions.AllowMinusSign
                       ||| NumberLiteralOptions.AllowFraction
                       ||| NumberLiteralOptions.AllowExponent
                       ||| NumberLiteralOptions.AllowHexadecimal
                       ||| NumberLiteralOptions.AllowSuffix

    let pnumber : Parser<LispVal, unit> =
        let parser = numberLiteral numberFormat "number"
        fun stream ->
            let reply = parser stream
            if reply.Status = Ok then
                let nl = reply.Result // the parsed NumberLiteral
                if nl.SuffixLength = 0
                   || (   nl.IsInteger
                       && nl.SuffixLength = 1 && nl.SuffixChar1 = 'L')
                then
                    try
                        // R-1RK 12.3.2 requires exact integers of arbitrary size, so a
                        // literal takes the narrowest exact type that holds it and falls
                        // back to BigInteger rather than failing to parse. The `L`
                        // suffix still forces at least 64-bit.
                        //
                        // Hexadecimal keeps F#'s own conversions and its fixed widths:
                        // they understand the `0x` prefix that Int32.TryParse rejects,
                        // and they are what decides that 0xFFFFFFFF is -1.
                        let integerLiteral (text: string) forceLong =
                            if nl.IsHexadecimal then
                                if forceLong then box (int64 text) else box (int32 text)
                            else
                                match System.Int32.TryParse text with
                                | true, value when not forceLong -> box value
                                | _ ->
                                    match System.Int64.TryParse text with
                                    | true, value -> box value
                                    | _ -> box (System.Numerics.BigInteger.Parse text)
                        /// R-1RK 12.4 gives exact ratios an external representation, so a
                        /// value that prints as 1/3 reads back as itself. Only digits may
                        /// follow the slash, which keeps `(/ 1 3)` -- where the slash is a
                        /// separate token -- reading as a call as it always has.
                        let ratioDenominator () =
                            if nl.SuffixLength > 0 || nl.IsHexadecimal || stream.Peek() <> '/' then None
                            else
                                let mutable length = 1
                                while System.Char.IsDigit(stream.Peek(length)) do
                                    length <- length + 1
                                if length = 1 then None
                                else Some(stream.Read(length).Substring(1))
                        let result =
                            if nl.IsInteger then
                                match ratioDenominator () with
                                | Some denominator ->
                                    let denominator = System.Numerics.BigInteger.Parse denominator
                                    if denominator.IsZero then
                                        raise (System.FormatException "a ratio literal cannot have a zero denominator")
                                    let ratio =
                                        makeExactRatio
                                            (System.Numerics.BigInteger.Parse nl.String) denominator
                                    // A denominator that reduces to one leaves an ordinary
                                    // integer, exactly as dividing would.
                                    if ratio.Denominator.IsOne then
                                        Obj(Arithmetic.ofBig ratio.Numerator)
                                    else Obj(box ratio)
                                | None -> Obj(integerLiteral nl.String (nl.SuffixLength > 0))
                            else
                                if nl.IsHexadecimal then
                                    float (floatOfHexString nl.String) :> obj |> Obj
                                else
                                    float (float nl.String) :> obj |> Obj
                        Reply(result)
                    with
                    | :? System.OverflowException as e ->
                        stream.Skip(-nl.String.Length)
                        Reply(FatalError, messageError e.Message)
                    | :? System.FormatException as e ->
                        stream.Skip(-nl.String.Length)
                        Reply(FatalError, messageError e.Message)
                else
                    stream.Skip(-nl.SuffixLength)
                    Reply(Error, messageError "invalid number suffix")
            else // reconstruct error reply
                Reply(reply.Status, reply.Error)

    let parseNumber = pnumber

    let private sourcePosition (position: FParsec.Position) : SourcePosition =
        { offset = position.Index
          line = position.Line
          column = position.Column }

    let private sourceSpan (startPosition: FParsec.Position) (endPosition: FParsec.Position) =
        { sourceName = startPosition.StreamName
          startPosition = sourcePosition startPosition
          endPosition = sourcePosition endPosition }

    let private locatedDatum parser : Parser<LocatedValue, unit> =
        parse {
            let! startPosition = getPosition
            let! value = parser
            let! endPosition = getPosition
            let kind =
                match value with
                | Atom name -> LAtom name
                | other -> LLiteral other
            return { kind = kind; span = sourceSpan startPosition endPosition }
        }

    let parseLocatedString = locatedDatum parseString
    let parseLocatedNumber = locatedDatum parseNumber
    let parseLocatedAtom = locatedDatum parseAtom

    let private parseLocatedExpr, parseLocatedExprRef =
        createParserForwardedToRef<LocatedValue, unit> ()

    let private parseLocatedDottedMarker =
        locatedDatum (skipChar '&' >>% Atom "&")

    let private parseLocatedList : Parser<LocatedValue list,unit> =
        sepEndBy (parseLocatedDottedMarker <|> parseLocatedExpr) ws1
    let private parseLocatedArray : Parser<LocatedValue array,unit> =
        sepEndBy parseLocatedExpr ws1 |>> List.toArray
    let private parseLocatedQuoted : Parser<LocatedValue,unit> =
        parse {
            let! startPosition = getPosition
            do! skipChar '\''
            let! quoted = parseLocatedExpr
            let! endPosition = getPosition
            return
                { kind = LQuote quoted
                  span = sourceSpan startPosition endPosition }
        }

    do parseLocatedExprRef.Value <-
        parseLocatedString
        <|> parseLocatedNumber
        <|> parseLocatedAtom
        <|> parseLocatedQuoted
        <|> parse {
                let! startPosition = getPosition
                do! skipChar '('
                do! ws
                let! values = parseLocatedList
                let! kind =
                    let isDottedMarker value =
                        match value.kind with
                        | LAtom "&" -> true
                        | _ -> false
                    match values |> List.tryFindIndex isDottedMarker with
                    | None -> preturn (LList values)
                    | Some markerIndex ->
                        let head = List.take markerIndex values
                        match List.skip (markerIndex + 1) values with
                        | [tail] when not (isDottedMarker tail) -> preturn (LDottedList(head, tail))
                        | _ -> fail "dotted list requires exactly one tail"
                do! skipChar ')'
                let! endPosition = getPosition
                return
                    { kind = kind
                      span = sourceSpan startPosition endPosition }
            }
        <|> parse {
                let! startPosition = getPosition
                do! skipChar '['
                do! ws
                let! values = parseLocatedArray
                do! skipChar ']'
                let! endPosition = getPosition
                return
                    { kind = LVector values
                      span = sourceSpan startPosition endPosition }
            }

    let parseExpr : Parser<LispVal, unit> = parseLocatedExpr |>> toLispVal

    let private conciseParseMessage (message: string) =
        let lines = message.Replace("\r\n", "\n").Split('\n')
        match
            lines
            |> Array.tryFindIndex (fun line ->
                line.StartsWith("Expecting", System.StringComparison.Ordinal)
                || line.StartsWith("Unexpected", System.StringComparison.Ordinal)
                || line.StartsWith("The parser", System.StringComparison.Ordinal))
        with
        | Some index -> System.String.Join(System.Environment.NewLine, lines.[index..])
        | None -> "invalid syntax"

    let private maximumNestingDepth = 256

    let private tryNestingError sourceName (input: string) =
        let mutable index = 0
        let mutable line = 1L
        let mutable column = 1L
        let mutable depth = 0
        let mutable inString = false
        let mutable escaped = false
        let mutable inComment = false
        let mutable previousWasCarriageReturn = false
        let mutable error = None

        while index < input.Length && error.IsNone do
            let character = input.[index]
            if inComment then
                if character = '\r' || character = '\n' then
                    inComment <- false
            elif inString then
                if escaped then
                    escaped <- false
                elif character = '\\' then
                    escaped <- true
                elif character = '"' then
                    inString <- false
            else
                match character with
                | ';' -> inComment <- true
                | '"' -> inString <- true
                | '('
                | '[' ->
                    depth <- depth + 1
                    if depth > maximumNestingDepth then
                        let startPosition =
                            { offset = int64 index
                              line = line
                              column = column }
                        let endPosition =
                            { startPosition with
                                offset = startPosition.offset + 1L
                                column = startPosition.column + 1L }
                        let span =
                            { sourceName = sourceName
                              startPosition = startPosition
                              endPosition = endPosition }
                        error <-
                            Some(
                                LocatedError(
                                    span,
                                    sourceLineAt input line,
                                    Parser(sprintf "maximum nesting depth of %d exceeded" maximumNestingDepth)))
                | ')'
                | ']' -> depth <- max 0 (depth - 1)
                | _ -> ()

            if character = '\r' then
                line <- line + 1L
                column <- 1L
                previousWasCarriageReturn <- true
            elif character = '\n' then
                if not previousWasCarriageReturn then
                    line <- line + 1L
                column <- 1L
                previousWasCarriageReturn <- false
            else
                column <- column + 1L
                previousWasCarriageReturn <- false
            index <- index + 1

        error

    let private readLocatedOrThrow parser sourceName input =
        match tryNestingError sourceName input with
        | Some error -> throwError error
        | None ->
            match runParserOnString parser () sourceName input with
            | Success(result,_,_) -> Choice2Of2 result
            | Failure(message, parserError, _) ->
                let position = parserError.Position
                let point = sourcePosition position
                let span =
                    { sourceName = position.StreamName
                      startPosition = point
                      endPosition = point }
                let line = sourceLineAt input position.Line
                throwError (LocatedError(span, line, Parser(conciseParseMessage message)))

    let readLocatedExpr sourceName input =
        readLocatedOrThrow (ws >>. parseLocatedExpr .>> ws .>> eof) sourceName input

    let readLocatedExprList sourceName input =
        readLocatedOrThrow (ws >>. many (parseLocatedExpr .>> ws) .>> eof) sourceName input

    let readExprFromSource sourceName input =
        match readLocatedExpr sourceName input with
        | Choice1Of2 error -> throwError error
        | Choice2Of2 value -> succeed (toLispVal value)

    let readExprListFromSource sourceName input =
        match readLocatedExprList sourceName input with
        | Choice1Of2 error -> throwError error
        | Choice2Of2 values -> values |> List.map toLispVal |> succeed

    let readExpr = readExprFromSource ""
    let readExprList = readExprListFromSource ""
