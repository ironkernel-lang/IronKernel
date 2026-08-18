namespace IronKernel

module CorePackage =

    open System
    open System.IO
    open System.Text
    open Ast
    open Ir
    open SymbolTable

    let private magic = Encoding.ASCII.GetBytes("IKC2")
    let private maxDepth = 256
    let private maxCollectionLength = 1_000_000
    let private maxStringBytes = 16 * 1024 * 1024

    let private checkDepth depth =
        if depth > maxDepth then
            raise (InvalidDataException("IKC Core IR exceeds the maximum nesting depth"))

    let private writeString (writer: BinaryWriter) (value: string) =
        let bytes = Encoding.UTF8.GetBytes value
        if bytes.Length > maxStringBytes then
            raise (InvalidDataException("IKC string exceeds the maximum length"))
        writer.Write bytes.Length
        writer.Write bytes

    let private readLength (reader: BinaryReader) kind maximum =
        let length = reader.ReadInt32()
        if length < 0 || length > maximum then
            raise (InvalidDataException(sprintf "Invalid IKC %s length: %d" kind length))
        length

    let private readString (reader: BinaryReader) =
        let length = readLength reader "string" maxStringBytes
        let bytes = reader.ReadBytes length
        if bytes.Length <> length then raise (EndOfStreamException("Truncated IKC string"))
        Encoding.UTF8.GetString bytes

    let rec private writeValue depth (writer: BinaryWriter) value =
        checkDepth depth
        let writeValues values =
            if List.length values > maxCollectionLength then
                raise (InvalidDataException("IKC value collection exceeds the maximum length"))
            writer.Write(List.length values)
            values |> List.iter (writeValue (depth + 1) writer)
        match value with
        | Atom name -> writer.Write 0uy; writeString writer name
        | List values -> writer.Write 1uy; writeValues values
        | DottedList(head, tail) ->
            writer.Write 2uy
            writeValues head
            writeValue (depth + 1) writer tail
        | Bool value -> writer.Write 3uy; writer.Write value
        | Inert -> writer.Write 4uy
        | Nil -> writer.Write 5uy
        | Keyword name -> writer.Write 6uy; writeString writer name
        | Obj null -> writer.Write 7uy
        | Obj (:? string as value) -> writer.Write 8uy; writeString writer value
        | Obj (:? byte as value) -> writer.Write 9uy; writer.Write value
        | Obj (:? int as value) -> writer.Write 10uy; writer.Write value
        | Obj (:? int64 as value) -> writer.Write 11uy; writer.Write value
        | Obj (:? float32 as value) -> writer.Write 12uy; writer.Write value
        | Obj (:? double as value) -> writer.Write 13uy; writer.Write value
        | Vector values ->
            if values.Length > maxCollectionLength then
                raise (InvalidDataException("IKC vector exceeds the maximum length"))
            writer.Write 14uy
            writer.Write values.Length
            values |> Array.iter (writeValue (depth + 1) writer)
        | unsupported ->
            raise (InvalidDataException("Unsupported IKC constant: " + showVal unsupported))

    let rec private readValue depth (reader: BinaryReader) =
        checkDepth depth
        let readValues () =
            let count = readLength reader "value collection" maxCollectionLength
            List.init count (fun _ -> readValue (depth + 1) reader)
        match reader.ReadByte() with
        | 0uy -> Atom(readString reader)
        | 1uy -> ofList(readValues ())
        | 2uy -> ofDotted (readValues ()) (readValue (depth + 1) reader)
        | 3uy -> Bool(reader.ReadBoolean())
        | 4uy -> Inert
        // Normalised to the `List` spelling of the empty list: a decoded `Nil` was not
        // `eqv?` to an empty list built at runtime. See Eval's note.
        | 5uy -> ofList []
        | 6uy -> Keyword(readString reader)
        | 7uy -> Obj null
        | 8uy -> Obj(box (readString reader))
        | 9uy -> Obj(box (reader.ReadByte()))
        | 10uy -> Obj(box (reader.ReadInt32()))
        | 11uy -> Obj(box (reader.ReadInt64()))
        | 12uy -> Obj(box (reader.ReadSingle()))
        | 13uy -> Obj(box (reader.ReadDouble()))
        | 14uy ->
            let count = readLength reader "vector" maxCollectionLength
            Vector(Array.init count (fun _ -> readValue (depth + 1) reader))
        | tag -> raise (InvalidDataException(sprintf "Unknown IKC value tag: %d" tag))

    let private writeIdentity (writer: BinaryWriter) = function
        | PrimitiveIf -> writer.Write 0uy
        | PrimitiveDefine -> writer.Write 1uy
        | PrimitiveSequence -> writer.Write 2uy

    let private readIdentity (reader: BinaryReader) =
        match reader.ReadByte() with
        | 0uy -> PrimitiveIf
        | 1uy -> PrimitiveDefine
        | 2uy -> PrimitiveSequence
        | tag -> raise (InvalidDataException(sprintf "Unknown IKC primitive identity: %d" tag))

    let private writePosition (writer: BinaryWriter) position =
        writer.Write position.offset
        writer.Write position.line
        writer.Write position.column

    let private readPosition (reader: BinaryReader) =
        { offset = reader.ReadInt64()
          line = reader.ReadInt64()
          column = reader.ReadInt64() }

    let rec private writeExpression depth (writer: BinaryWriter) expression =
        checkDepth depth
        let writeExpressions expressions =
            if List.length expressions > maxCollectionLength then
                raise (InvalidDataException("IKC expression collection exceeds the maximum length"))
            writer.Write(List.length expressions)
            expressions |> List.iter (writeExpression (depth + 1) writer)
        match expression with
        | CLit value -> writer.Write 0uy; writeValue (depth + 1) writer value
        | CVar name -> writer.Write 1uy; writeString writer name
        | CQuote value -> writer.Write 2uy; writeValue (depth + 1) writer value
        | CIf(condition, consequent, alternative) ->
            writer.Write 3uy
            writeExpression (depth + 1) writer condition
            writeExpression (depth + 1) writer consequent
            writeExpression (depth + 1) writer alternative
        | CSeq expressions -> writer.Write 4uy; writeExpressions expressions
        | CDefine(lhs, rhs) ->
            writer.Write 5uy
            writeExpression (depth + 1) writer lhs
            writeExpression (depth + 1) writer rhs
        | CVau(formals, envarg, body) ->
            writer.Write 6uy
            writeValue (depth + 1) writer formals
            writeString writer envarg
            writeExpressions body
        | CApp(operator, arguments) ->
            writer.Write 7uy
            writeExpression (depth + 1) writer operator
            writeExpressions arguments
        | COperate(operator, operands) ->
            writer.Write 8uy
            writeExpression (depth + 1) writer operator
            if List.length operands > maxCollectionLength then
                raise (InvalidDataException("IKC operand collection exceeds the maximum length"))
            writer.Write(List.length operands)
            operands |> List.iter (writeValue (depth + 1) writer)
        | CIntrinsicOperate(identity, operands) ->
            writer.Write 9uy
            writeIdentity writer identity
            if List.length operands > maxCollectionLength then
                raise (InvalidDataException("IKC operand collection exceeds the maximum length"))
            writer.Write(List.length operands)
            operands |> List.iter (writeValue (depth + 1) writer)
        | CGuarded(guard, specialized, fallback) ->
            writer.Write 10uy
            writeString writer guard.name
            writeIdentity writer guard.expectedIdentity
            writeExpression (depth + 1) writer specialized
            writeExpression (depth + 1) writer fallback
        | CContractFold(_, _, fallback) -> writeExpression depth writer fallback
        | CEval(environmentExpression, valueExpression) ->
            writer.Write 11uy
            writeExpression (depth + 1) writer environmentExpression
            writeExpression (depth + 1) writer valueExpression
        | CReset body -> writer.Write 12uy; writeExpression (depth + 1) writer body
        | CResidual value -> writer.Write 13uy; writeValue (depth + 1) writer value
        | CLocated(span, sourceLine, inner) ->
            writer.Write 14uy
            writePosition writer span.startPosition
            writePosition writer span.endPosition
            match sourceLine with
            | Some line -> writer.Write true; writeString writer line
            | None -> writer.Write false
            writeExpression (depth + 1) writer inner

    let rec private readExpression depth env sourceName (reader: BinaryReader) =
        checkDepth depth
        let readExpressions () =
            let count = readLength reader "expression collection" maxCollectionLength
            List.init count (fun _ -> readExpression (depth + 1) env sourceName reader)
        let readOperands () =
            let count = readLength reader "operand collection" maxCollectionLength
            List.init count (fun _ -> readValue (depth + 1) reader)
        match reader.ReadByte() with
        | 0uy -> CLit(readValue (depth + 1) reader)
        | 1uy -> CVar(readString reader)
        | 2uy -> CQuote(readValue (depth + 1) reader)
        | 3uy ->
            CIf(
                readExpression (depth + 1) env sourceName reader,
                readExpression (depth + 1) env sourceName reader,
                readExpression (depth + 1) env sourceName reader)
        | 4uy -> CSeq(readExpressions ())
        | 5uy ->
            CDefine(
                readExpression (depth + 1) env sourceName reader,
                readExpression (depth + 1) env sourceName reader)
        | 6uy ->
            let formals = readValue (depth + 1) reader
            let envarg = readString reader
            CVau(formals, envarg, readExpressions ())
        | 7uy ->
            let operator = readExpression (depth + 1) env sourceName reader
            CApp(operator, readExpressions ())
        | 8uy ->
            let operator = readExpression (depth + 1) env sourceName reader
            COperate(operator, readOperands ())
        | 9uy -> CIntrinsicOperate(readIdentity reader, readOperands ())
        | 10uy ->
            let name = readString reader
            let identity = readIdentity reader
            let specialized = readExpression (depth + 1) env sourceName reader
            let fallback = readExpression (depth + 1) env sourceName reader
            match tryCreateBindingGuard env name identity with
            | Some guard -> CGuarded(guard, specialized, fallback)
            | None -> fallback
        | 11uy ->
            CEval(
                readExpression (depth + 1) env sourceName reader,
                readExpression (depth + 1) env sourceName reader)
        | 12uy -> CReset(readExpression (depth + 1) env sourceName reader)
        | 13uy -> CResidual(readValue (depth + 1) reader)
        | 14uy ->
            let span =
                { sourceName = sourceName
                  startPosition = readPosition reader
                  endPosition = readPosition reader }
            let sourceLine = if reader.ReadBoolean() then Some(readString reader) else None
            CLocated(span, sourceLine, readExpression (depth + 1) env sourceName reader)
        | tag -> raise (InvalidDataException(sprintf "Unknown IKC expression tag: %d" tag))

    let write (stream: Stream) expressions =
        use writer = new BinaryWriter(stream, Encoding.UTF8, true)
        writer.Write magic
        if List.length expressions > maxCollectionLength then
            raise (InvalidDataException("IKC form collection exceeds the maximum length"))
        writer.Write(List.length expressions)
        expressions |> List.iter (writeExpression 0 writer)
        writer.Flush()

    let read env sourceName (stream: Stream) =
        use reader = new BinaryReader(stream, Encoding.UTF8, true)
        let header = reader.ReadBytes magic.Length
        if header.Length <> magic.Length then raise (EndOfStreamException("Truncated IKC header"))
        match Encoding.ASCII.GetString header with
        | "IKC1" -> raise (InvalidDataException("IKC1 source packages are unsupported; rebuild the package as IKC2"))
        | "IKC2" ->
            let count = readLength reader "form collection" maxCollectionLength
            let forms = List.init count (fun _ -> readExpression 0 env sourceName reader)
            if stream.Position <> stream.Length then
                raise (InvalidDataException("IKC package contains trailing data"))
            forms
        | _ -> raise (InvalidDataException("Not an IronKernel compiled package (missing IKC2 header)"))