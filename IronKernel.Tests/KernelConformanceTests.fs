module IronKernel.Tests.KernelConformanceTests

open System
open System.IO
open System.Reflection
open System.Text
open System.Text.Json
open Xunit

open IronKernel.Ast
open IronKernel.Emit
open IronKernel.Errors
open IronKernel.SymbolTable
open IronKernel.Tests.TestHelpers

/// Conformance status against the Kernel Revised-1 Report (R-1RK).
///
/// The feature list in `docs/kernel-r-1rk-features.json` is extracted from the
/// report's table of contents by `tools/extract-r-1rk-features.py`, so what has to
/// be covered is decided by the report rather than by what happens to be
/// implemented. This suite probes a real bootstrapped environment and writes the
/// status matrix to `docs/kernel-conformance.md`.
///
/// The matrix is regenerated and diffed rather than hand-maintained: a hand-written
/// status table drifts from the implementation and then overstates it.

let private repoRoot () =
    let start = Directory.GetCurrentDirectory()
    let rec search (dir: DirectoryInfo) =
        if isNull (box dir) then failwith "repository root not found"
        elif File.Exists(Path.Combine(dir.FullName, "IronKernel.sln")) then dir.FullName
        else search dir.Parent
    search (DirectoryInfo start)

type private Feature = {
    Entry: string
    Chapter: string
    ChapterTitle: string
    Section: string
    SectionTitle: string
    Title: string
    Bindings: string list
    Optional: bool
}

let private features () =
    let path = Path.Combine(repoRoot (), "docs", "kernel-r-1rk-features.json")
    use document = JsonDocument.Parse(File.ReadAllText path)
    [ for element in document.RootElement.GetProperty("entries").EnumerateArray() ->
        { Entry = element.GetProperty("entry").GetString()
          Chapter = element.GetProperty("chapter").GetString()
          ChapterTitle = element.GetProperty("chapterTitle").GetString()
          Section = element.GetProperty("section").GetString()
          SectionTitle = element.GetProperty("sectionTitle").GetString()
          Title = element.GetProperty("title").GetString()
          Bindings =
            [ for b in element.GetProperty("bindings").EnumerateArray() -> b.GetString() ]
          Optional = element.GetProperty("optional").GetBoolean() } ]

/// IronKernel is a dialect: it drops the `$` sigil the report uses to mark
/// operatives, and spells `$define!` as `define`. These are deliberate renamings,
/// listed explicitly rather than derived by stripping `$`, so that a coincidental
/// name match can never be mistaken for the report's feature.
let private aliases () =
    dict [
        "$and?", "and?"
        "$bindings->environment", "bindings->environment"
        "$cond", "cond"
        "$define!", "define"
        "$if", "if"
        "$import!", "import!"
        "$lambda", "lambda"
        "$let", "let"
        "$let*", "let*"
        "$let-redirect", "let-redirect"
        "$let/cc", "let/cc"
        "$letrec", "letrec"
        "$letrec*", "letrec*"
        "$or?", "or?"
        "$provide!", "provide!"
        "$remote-eval", "remote-eval"
        "$sequence", "sequence"
        "$set!", "set!"
        "$vau", "vau"
    ]

/// Behavioural checks keyed by report entry. Each is an expression that must
/// evaluate to true. Comparing against a boolean rather than against printed output
/// keeps the checks independent of external representation, which IronKernel spells
/// differently from the report.
///
/// A passing check means the entry has been exercised, not that every requirement in
/// it has been verified. The matrix says so, and `verified` should be read that way.
let private behaviouralChecks () : (string * string list) list = [
    "4.5.2", [ "(eqv? (if #t 1 2) 1)"
               "(eqv? (if #f 1 2) 2)"
               // The unselected branch must not be evaluated.
               "(eqv? (if #t 1 no-such-variable) 1)" ]
    "4.6.1", [ "(pair? (cons 1 2))"; "(eqv? (pair? ()) #f)" ]
    "4.6.2", [ "(null? ())"; "(eqv? (null? (cons 1 2)) #f)" ]
    "4.6.3", [ "(eqv? (car (cons 1 2)) 1)"; "(eqv? (cdr (cons 1 2)) 2)" ]
    "4.8.1", [ "(environment? (get-current-environment))" ]
    "4.8.3", [ "(eqv? (eval (get-current-environment) (list + 1 2)) 3)" ]
    "4.8.4", [ "(environment? (make-environment))" ]
    "4.10.3", [ // An operative receives its operands unevaluated.
                "(eqv? (car ((vau xs _ xs) foo)) 'foo)" ]
    "4.10.4", [ "(eqv? ((wrap (vau (x) _ x)) (+ 1 2)) 3)" ]
    "4.10.5", [ "(eqv? ((unwrap (lambda (x) x)) bar) 'bar)" ]
    "5.1.1", [ "(eqv? (sequence 1 2 3) 3)" ]
    "5.2.1", [ "(eqv? (car (list 7 8)) 7)"; "(eqv? (length (list 7 8)) 2)" ]
    "5.2.2", [ "(eqv? (cdr (list* 1 2)) 2)" ]
    "5.3.1", [ "(eqv? (car ((vau xs _ xs) foo)) 'foo)" ]
    "5.3.2", [ "(eqv? ((lambda (x) (* x 2)) 4) 8)" ]
    "5.4.1", [ "(eqv? (car (list 1 2)) 1)"; "(eqv? (car (cdr (list 1 2))) 2)" ]
    "5.5.1", [ "(eqv? (apply + (list 1 2)) 3)" ]
    "5.6.1", [ "(eqv? (cond ((eqv? 1 2) 'a) (#t 'b)) 'b)" ]
    "5.9.1", [ "(eqv? (car (map (lambda (x) (* x 2)) (list 3))) 6)" ]
    "5.10.1", [ "(eqv? (let ((x 5)) x) 5)" ]
    "6.1.1", [ "(not? #f)"; "(eqv? (not? #t) #f)" ]
    "6.1.4", [ "(and? #t #t)"; "(eqv? (and? #t #f) #f)"
               // Operative short-circuit: the second operand must not be evaluated.
               "(eqv? (and? #f (/ 1 0)) #f)" ]
    "6.1.5", [ "(or? #f #t)"; "(eqv? (or? #f #f) #f)"; "(or? #t (/ 1 0))" ]
    "6.3.1", [ "(eqv? (length (list 1 2 3)) 3)"; "(eqv? (length ()) 0)" ]
    "6.7.2", [ "(environment? (get-current-environment))" ]
    "6.7.4", [ "(eqv? (let* ((x 1) (y (+ x 1))) y) 2)" ]
    "6.7.5", [ "(eqv? (letrec ((f (lambda (n) (if (eqv? n 0) 0 (f (- n 1)))))) (f 3)) 0)" ]
    "6.7.9", [ "(eqv? (remote-eval (+ 1 2) (get-current-environment)) 3)" ]
    "6.8.1", [ "(let ((e (get-current-environment))) (sequence (set! e zz 7) (eqv? zz 7)))" ]
    "6.9.1", [ "(eqv? (sequence (for-each (list 1) (lambda (x) x)) 1) 1)" ]
    "7.2.2", [ "(eqv? (call/cc (lambda (k) (k 42))) 42)" ]
    "7.3.2", [ "(eqv? (let/cc k (k 9)) 9)" ]
    "8.1.1", [ "(let ((t (make-encapsulation-type))) (let ((e ((car t) 1)) (p (car (cdr t)))) (p e)))" ]
    "9.1.1", [ "(promise? (memoize 1))" ]
    "9.1.2", [ "(eqv? (force (memoize 5)) 5)" ]
    "9.1.4", [ "(eqv? (force (memoize 5)) 5)" ]
    "12.5.4", [ "(eqv? (+ 1 2) 3)" ]
    "12.5.5", [ "(eqv? (* 3 4) 12)" ]
    "12.5.6", [ "(eqv? (- 5 2) 3)" ]
    "12.5.7", [ "(zero? 0)"; "(eqv? (zero? 1) #f)" ]
    "12.8.2", [ "(eqv? (/ 8 2) 4)" ]
]

/// Divergences the matrix cannot express as a status, recorded so that a `verified`
/// row is not read as "identical to the report".
let private divergences () = [
    "3.6", "External representations differ: IronKernel prints a number as "
           + "`<obj 3 : Int32>` rather than `3`."
    "4.8.3", "`eval` takes its arguments in the opposite order to the report: "
             + "IronKernel is `(eval environment expression)`, the report is "
             + "`(eval expression environment)`."
    "6.1.2", "`and?` short-circuits in IronKernel, so it behaves as the report's "
             + "operative `$and?` (6.1.4) rather than the applicative `and?`, which "
             + "must evaluate every argument."
    "6.1.3", "`or?` short-circuits, matching `$or?` (6.1.5) rather than the "
             + "applicative `or?`."
    "1.3.7", "IronKernel drops the `$` sigil the report uses for operatives, so "
             + "`$if` is `if` and `$define!` is `define`. See the alias column."
]

let private conformanceEnv () =
    match bootstrapEnv () with
    | Choice1Of2 error -> failwith (showError error)
    | Choice2Of2 env -> env

type private Resolution =
    | Exact
    | ViaAlias of string
    | Absent

let private resolve env binding =
    match getVar' env binding with
    | Some _ -> Exact
    | None ->
        match (aliases ()).TryGetValue binding with
        | true, alias ->
            match getVar' env alias with
            | Some _ -> ViaAlias alias
            | None -> Absent
        | _ -> Absent

type private Status =
    | Verified
    | Bound
    | Partial
    | Absent'

let private runCheck env expression =
    try
        match evalIn env expression with
        | Bool true -> true
        | _ -> false
    with _ -> false

let private statusOf env (feature: Feature) =
    let resolutions = feature.Bindings |> List.map (fun b -> b, resolve env b)
    let present = resolutions |> List.filter (fun (_, r) -> r <> Absent) |> List.length
    let checks = behaviouralChecks () |> List.tryFind (fun (e, _) -> e = feature.Entry)
    let checksPass =
        match checks with
        | Some (_, cases) when not cases.IsEmpty -> cases |> List.forall (runCheck env)
        | _ -> false
    let status =
        if present = 0 then Absent'
        elif present < resolutions.Length then Partial
        elif checksPass then Verified
        else Bound
    status, resolutions, (checks |> Option.map (snd >> List.length) |> Option.defaultValue 0)

let private describe = function
    | Verified -> "verified"
    | Bound -> "bound"
    | Partial -> "partial"
    | Absent' -> "absent"

let private renderMatrix () =
    let env = conformanceEnv ()
    let rows = features () |> List.map (fun f -> f, statusOf env f)
    let output = StringBuilder()
    let appendLine (text: string) = output.Append(text).Append('\n') |> ignore

    appendLine "# Kernel R-1RK conformance status"
    appendLine ""
    appendLine "Generated by `IronKernel.Tests/KernelConformanceTests.fs`. Do not edit by hand;"
    appendLine "run the suite with `IRONKERNEL_UPDATE_CONFORMANCE=1` to regenerate."
    appendLine ""
    appendLine "Features are those of the [Revised-1 Report on the Kernel Programming Language]"
    appendLine "(https://ftp.cs.wpi.edu/pub/techreports/pdf/05-07.pdf) (WPI TR 05-07), extracted"
    appendLine "from its table of contents by `tools/extract-r-1rk-features.py` into"
    appendLine "`docs/kernel-r-1rk-features.json`. The report decides what must be covered, so"
    appendLine "features IronKernel has never implemented still appear here."
    appendLine ""
    appendLine "| Status | Meaning |"
    appendLine "|---|---|"
    appendLine "| `verified` | Every binding resolves **and** a behavioural check for this entry passes. The check exercises the entry; it does not prove every requirement in it. |"
    appendLine "| `bound` | Every binding resolves, but nothing checks its behaviour yet. **This is not evidence of conformance.** |"
    appendLine "| `partial` | Some bindings of the entry resolve and others do not. |"
    appendLine "| `absent` | No binding of the entry resolves. |"
    appendLine ""
    appendLine "IronKernel is a dialect, and drops the `$` sigil the report uses for operatives"
    appendLine "(`$if` is spelled `if`, `$define!` is spelled `define`). Where a feature resolves"
    appendLine "under such a name the matrix records it as an alias, so the divergence is visible"
    appendLine "rather than hidden behind a pass."
    appendLine ""

    let counted status = rows |> List.filter (fun (_, (s, _, _)) -> s = status) |> List.length
    let total = List.length rows
    appendLine "## Summary"
    appendLine ""
    appendLine "| | Entries | Share |"
    appendLine "|---|---:|---:|"
    for status in [Verified; Bound; Partial; Absent'] do
        let n = counted status
        appendLine (sprintf "| `%s` | %d | %.0f%% |" (describe status) n (100.0 * float n / float total))
    appendLine (sprintf "| **total** | **%d** | |" total)
    appendLine ""
    let optional = rows |> List.filter (fun (f, _) -> f.Optional) |> List.length
    appendLine (sprintf "%d of %d entries belong to modules the report marks optional; an" optional total)
    appendLine "implementation may omit them and still conform."
    appendLine ""
    appendLine "## Known divergences"
    appendLine ""
    appendLine "Differences a status cannot express. A `verified` row means the entry was"
    appendLine "exercised, not that IronKernel matches the report exactly."
    appendLine ""
    appendLine "| Report | Divergence |"
    appendLine "|---|---|"
    for entry, text in divergences () do
        appendLine (sprintf "| %s | %s |" entry text)
    appendLine ""

    for chapter in rows |> List.map (fun (f, _) -> f.Chapter) |> List.distinct |> List.sortBy int do
        let chapterRows = rows |> List.filter (fun (f, _) -> f.Chapter = chapter)
        let title = chapterRows |> List.head |> fst |> fun f -> f.ChapterTitle
        appendLine (sprintf "## %s %s" chapter title)
        appendLine ""
        appendLine "| Entry | Feature | Module | Status | Notes |"
        appendLine "|---|---|---|---|---|"
        for feature, (status, resolutions, checkCount) in chapterRows do
            let notes =
                [ if feature.Optional then yield "optional module"
                  for binding, resolution in resolutions do
                      match resolution with
                      | ViaAlias alias -> yield sprintf "`%s` as `%s`" binding alias
                      | Absent when resolutions.Length > 1 -> yield sprintf "`%s` absent" binding
                      | _ -> ()
                  if checkCount > 0 then yield sprintf "%d behavioural check(s)" checkCount ]
                |> String.concat "; "
            appendLine (
                sprintf "| %s | `%s` | %s | `%s` | %s |"
                    feature.Entry feature.Title feature.SectionTitle (describe status) notes)
        appendLine ""

    output.ToString()

let private matrixPath () = Path.Combine(repoRoot (), "docs", "kernel-conformance.md")

[<Fact>]
let ``conformance matrix is current`` () =
    let rendered = renderMatrix ()
    if Environment.GetEnvironmentVariable "IRONKERNEL_UPDATE_CONFORMANCE" = "1" then
        File.WriteAllText(matrixPath (), rendered)
    else
        let committed =
            if File.Exists (matrixPath ()) then File.ReadAllText(matrixPath ()).Replace("\r\n", "\n")
            else ""
        Assert.True(
            (committed = rendered.Replace("\r\n", "\n")),
            "docs/kernel-conformance.md is out of date. Regenerate it with "
            + "IRONKERNEL_UPDATE_CONFORMANCE=1 dotnet test --filter conformance")

[<Fact>]
let ``every behavioural check names a real report entry`` () =
    let known = features () |> List.map (fun f -> f.Entry) |> Set.ofList
    for entry, _ in behaviouralChecks () do
        Assert.True(known.Contains entry, sprintf "unknown R-1RK entry: %s" entry)

[<Fact>]
let ``every alias target is a binding the report defines`` () =
    let known = features () |> List.collect (fun f -> f.Bindings) |> Set.ofList
    for pair in aliases () do
        Assert.True(known.Contains pair.Key, sprintf "alias for unknown feature: %s" pair.Key)

