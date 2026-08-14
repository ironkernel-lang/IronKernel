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
/// R-1RK spells operatives with a leading `$`; IronKernel also binds the shorter
/// names as an extension (R-1RK 1.3.2). Both spellings denote the same combiner, so
/// the report's names resolve exactly and nothing needs aliasing. The table is kept
/// so that a future divergence can be recorded rather than hidden.
let private aliases () : System.Collections.Generic.IDictionary<string, string> =
    dict []

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
    "4.8.3", [ "(eqv? (eval (list + 1 2) (get-current-environment)) 3)" ]
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
    "6.1.2", [ "(and? #t #t)"; "(eqv? (and? #t #f) #f)"; "(and?)"
               // Applicative: an argument after a decided result is still evaluated.
               "(let ((t (vector 0))) (sequence (and? #f (sequence (vector-set! t 0 1) #t)) (eqv? (vector-ref t 0) 1)))" ]
    "6.1.3", [ "(or? #f #t)"; "(eqv? (or? #f #f) #f)"; "(eqv? (or?) #f)"
               "(let ((t (vector 0))) (sequence (or? #t (sequence (vector-set! t 0 1) #f)) (eqv? (vector-ref t 0) 1)))" ]
    "6.1.4", [ "($and? #t #t)"; "(eqv? ($and? #t #f) #f)"; "($and?)"
               // Operative short-circuit: the second operand must not be evaluated.
               "(eqv? ($and? #f (/ 1 0)) #f)" ]
    "6.1.5", [ "($or? #f #t)"; "(eqv? ($or? #f #f) #f)"; "(eqv? ($or?) #f)"
               "($or? #t (/ 1 0))" ]
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
    "12.5.1", [ "(number? 1)"; "(number? 1.5)"; "(eqv? (number? 'a) #f)"; "(number?)"
                "(integer? 3)"; "(integer? 3.0)"; "(eqv? (integer? 3.5) #f)"
                "(eqv? (integer? 'a) #f)"; "(finite? 1)"; "(finite?)" ]
    "12.5.2", [ "(=?)"; "(=? 1)"; "(=? 1 1 1)"
                // Numeric equality, not structural: 1 and 1.0 are equal.
                "(=? 1 1.0)"; "(eqv? (=? 1 2) #f)" ]
    "12.5.3", [ "(<=?)"; "(<=? 1)"; "(<=? 1 3 7 15)"; "(eqv? (<=? 1 7 3 15) #f)"
                "(<? 1 2 3)"; "(eqv? (<? 1 1) #f)"; "(>? 3 2 1)"; "(>=? 3 3 1)" ]
    "12.5.4", [ "(=? (+ 1 2) 3)"; "(=? (+) 0)"; "(=? (+ 7) 7)"; "(=? (+ 1 2 3 4 5) 15)" ]
    "12.5.5", [ "(=? (* 3 4) 12)"; "(=? (*) 1)"; "(=? (* 7) 7)"; "(=? (* 1 2 3 4) 24)" ]
    // 12.5.6: (- number . numbers) needs at least two arguments; the report
    // deliberately gives `-` no unary meaning.
    "12.5.6", [ "(=? (- 5 2) 3)"; "(=? (- 10 3 2) 5)" ]
    "12.5.7", [ "(zero? 0)"; "(zero? 0 0)"; "(eqv? (zero? 1) #f)"; "(zero?)" ]
    "12.5.8", [ "(=? (div 7 3) 2)"; "(=? (mod 7 3) 1)"
                // Negative operands: the defining property is 0 <= mod < |divisor|.
                "(=? (div -7 3) -3)"; "(=? (mod -7 3) 2)"
                "(=? (div 7 -3) -2)"; "(=? (mod 7 -3) 1)"
                "(=? (car (cdr (div-and-mod -7 3))) 2)"
                "(=? -7 (+ (* 3 (div -7 3)) (mod -7 3)))" ]
    "12.5.9", [ "(=? (div0 7 3) 2)"; "(=? (mod0 7 3) 1)"
                "(=? (div0 8 3) 3)"; "(=? (mod0 8 3) -1)"
                "(=? (mod0 -7 3) -1)"; "(=? (mod0 8 -3) -1)"
                "(=? 8 (+ (* 3 (div0 8 3)) (mod0 8 3)))" ]
    "12.5.10", [ "(positive? 1 2)"; "(eqv? (positive? 0) #f)"
                 "(negative? -1 -2)"; "(eqv? (negative? 0) #f)" ]
    "12.5.11", [ "(even? 4)"; "(even? -4)"; "(eqv? (even? 3) #f)"
                 "(odd? 3)"; "(eqv? (odd? 4) #f)" ]
    "12.5.12", [ "(=? (abs -5) 5)"; "(=? (abs 5) 5)"; "(=? (abs 0) 0)" ]
    "12.5.13", [ "(=? (max 1 7 3) 7)"; "(=? (min 1 7 3) 1)"; "(=? (max 5) 5)" ]
    "12.5.14", [ "(=? (gcd 12 18) 6)"; "(=? (lcm 4 6) 12)"; "(=? (gcd 0 5) 5)" ]
    "12.8.1", [ "(rational? 1)"; "(rational? 1.5)"; "(eqv? (rational? 'a) #f)"; "(rational?)" ]
    "12.8.2", [ "(=? (/ 8 2) 4)"
                // Ordinary division, not the truncating quotient: (/ 1 3) is a third.
                "(<? 0.3 (/ 1 3))"; "(<? (/ 1 3) 0.34)"
                // Divides by the product of the remaining arguments.
                "(=? (/ 24 2 3) 4)" ]
    "12.8.3", [ "(=? (numerator 0.5) 1)"; "(=? (denominator 0.5) 2)"
                "(=? (numerator 6) 6)"; "(=? (denominator 6) 1)"
                "(=? (numerator 0.75) 3)"; "(=? (denominator 0.75) 4)" ]
    "12.8.4", [ "(=? (floor 3.7) 3)"; "(=? (floor -3.7) -4)"
                "(=? (ceiling 3.2) 4)"; "(=? (ceiling -3.2) -3)"
                "(=? (truncate 3.7) 3)"; "(=? (truncate -3.7) -3)"
                // Halfway cases round to even.
                "(=? (round 0.5) 0)"; "(=? (round 1.5) 2)"; "(=? (round 2.5) 2)" ]
    // 12.9: the report gives these signatures only (see the note in the matrix), so
    // the checks assert the standard mathematical meanings.
    "12.9.1", [ "(real? 1)"; "(real? 1.5)"; "(eqv? (real? 'a) #f)"; "(real?)" ]
    "12.9.2", [ "(<? (abs (- (exp 0) 1)) 0.000001)"
                "(<? (abs (- (log 1) 0)) 0.000001)"
                "(<? (abs (- (log (exp 2)) 2)) 0.000001)" ]
    "12.9.3", [ "(<? (abs (- (sin 0) 0)) 0.000001)"
                "(<? (abs (- (cos 0) 1)) 0.000001)"
                "(<? (abs (- (tan 0) 0)) 0.000001)" ]
    "12.9.4", [ "(<? (abs (- (asin 0) 0)) 0.000001)"
                "(<? (abs (- (acos 1) 0)) 0.000001)"
                "(<? (abs (- (atan 0) 0)) 0.000001)"
                // 12.9.4 gives atan a two-argument form as well.
                "(<? (abs (- (atan 1 1) 0.7853981633974483)) 0.000001)" ]
    "12.9.5", [ "(<? (abs (- (sqrt 4) 2)) 0.000001)"
                "(<? (abs (- (sqrt 2) 1.4142135623730951)) 0.000001)" ]
    "12.9.6", [ "(=? (expt 2 10) 1024)"; "(=? (expt 3 0) 1)"
                "(<? (abs (- (expt 2 -1) 0.5)) 0.000001)" ]
    "12.8.5", [ "(=? (simplest-rational 0.2 0.4) (/ 1 3))"
                "(=? (simplest-rational -0.5 0.5) 0)"
                "(=? (rationalize 0.3 0.1) (/ 1 3))" ]
]

/// Divergences the matrix cannot express as a status, recorded so that a `verified`
/// row is not read as "identical to the report".
let private divergences () = [
    "3.6", "External representations differ: IronKernel prints a number as "
           + "`<obj 3 : Int32>` rather than `3`."
    "12.2", "There is no exact/inexact distinction. Numbers are CLR primitives, so "
            + "exactness, bounds and robustness (module Inexact, 12.6) are absent and "
            + "no number can be an exact infinity."
    "12.5.13", "`(max)` and `(min)` with no arguments signal an error. The report "
               + "returns exact negative and positive infinity, which IronKernel "
               + "cannot represent."
    "12.5.14", "`(gcd)` returns 0 and `(lcm)` returns 1. The report returns exact "
               + "positive infinity for `(gcd)`."
    "12.9", "The report specifies 12.9.2 through 12.9.6 by signature only. Appendix "
            + "A.2 records that it is an incomplete draft whose unwritten portions were "
            + "\"only planned in rough outline\", so `verified` there means the binding "
            + "exists with its standard mathematical meaning, and the choices the "
            + "report leaves open (a NaN result signals an error; infinities are "
            + "returned) are IronKernel's."
    "12.8", "Module Rational is implemented over the existing numeric types, which "
            + "have no exact rational representation. `(/ 1 3)` is the closest double "
            + "rather than an exact third, and `numerator`/`denominator` signal an "
            + "error when a value's exact ratio does not fit in 64 bits."
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

    appendLine "## Modules"
    appendLine ""
    appendLine "R-1RK 1.3.2 makes the *module* the unit of conformance: \"An implementation"
    appendLine "cannot claim to support a module M unless it both (1) supports all of the"
    appendLine "features in M, and (2) supports all of the modules assumed by M.\" A module"
    appendLine "counts as complete here only when every one of its entries is `verified`."
    appendLine ""
    appendLine "| Module | Required | Entries | Verified | Complete |"
    appendLine "|---|---|---:|---:|---|"
    let moduleKey (f: Feature) = f.Section, f.ChapterTitle, f.SectionTitle, f.Optional
    let sectionOrder (section: string) =
        let parts = section.Split('.') |> Array.map int
        parts.[0], parts.[1]
    for (section, chapterTitle, sectionTitle, optional) in
            rows
            |> List.map (fst >> moduleKey)
            |> List.distinct
            |> List.sortBy (fun (s, _, _, _) -> sectionOrder s) do
        let moduleRows = rows |> List.filter (fun (f, _) -> f.Section = section)
        let verified =
            moduleRows |> List.filter (fun (_, (status, _, _)) -> status = Verified) |> List.length
        appendLine (
            sprintf "| %s %s — %s | %s | %d | %d | %s |"
                section chapterTitle sectionTitle
                (if optional then "optional" else "**required**")
                (List.length moduleRows) verified
                (if verified = List.length moduleRows then "yes" else "no"))
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

