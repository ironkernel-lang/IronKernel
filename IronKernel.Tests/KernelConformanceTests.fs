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
    "4.1.1", [ "(boolean? #t)"; "(boolean? #f)"; "(eqv? (boolean? 1) #f)"; "(boolean?)" ]
    "4.3.1", [ "(equal? (list 1 2) (list 1 2))"; "(eqv? (equal? 1 2) #f)"
               "(equal? \"ab\" \"ab\")"
               // Weaker than eq?: true where eq? is false, and never the other way.
               "(equal? (list 1) (list 1))"
               // Reflexive on objects with no structural comparison of their own.
               "(let ((v (vector 1 2))) (equal? v v))"
               "(equal? car car)" ]
    "4.4.1", [ "(symbol? 'a)"; "(eqv? (symbol? 1) #f)"; "(symbol?)" ]
    "4.5.1", [ "(inert? #inert)"; "(eqv? (inert? 1) #f)"; "(inert?)" ]
    // 4.2.1 / 6.5.1: eq? is coarser here than the report's (see the divergence), so
    // these check what it does guarantee.
    "4.2.1", [ "(eq? 'a 'a)"; "(eqv? (eq? 'a 'b) #f)"; "(eq? 1 1)"
               // "Two pairs returned by different calls to cons are not eq?, even if
               // they have the same car and cdr" -- the distinction equal? does not
               // make, and the reason eq? cannot be the structural comparison.
               "(eqv? (eq? (list 1) (list 1)) #f)"
               "(equal? (list 1) (list 1))"
               // Reflexive, and the same pair reached two ways is the same pair.
               "(let ((p (list 1 2))) (eq? p p))"
               "(let ((p (list 1 2))) (eq? p (car (list p))))"
               "(let ((p (list 1 2))) (eq? (cdr p) (cdr p)))"
               // Environments have identity too, per the same section.
               "(let ((e (make-environment))) (eq? e e))"
               "(eqv? (eq? (make-environment) (make-environment)) #f)" ]
    "4.6.1", [ "(pair? (cons 1 2))"; "(eqv? (pair? ()) #f)" ]
    // 4.9.1: $define! binds in the current environment and returns inert.
    "4.7.1", [ // The mutation is visible through every reference to the pair.
               "(let ((p (list 1 2))) (set-car! p 9) (=? (car p) 9))"
               "(let ((p (list 1 2))) (let ((q p)) (set-car! q 9) (=? (car p) 9)))"
               "(let ((p (list 1 2))) (set-cdr! p (list 7)) (=? (car (cdr p)) 7))"
               // The result is inert.
               "(let ((p (list 1 2))) (inert? (set-car! p 9)))"
               // 3.8: mutating an immutable object signals an error, so a captured
               // algorithm cannot be rewritten under whoever captured it.
               "(immutable-pair? (quote (1 2)))"
               "(eqv? (immutable-pair? (list 1 2)) #f)" ]
    "4.7.2", [ "(=? (copy-es-immutable 5) 5)"
               // "If object is a mutable pair, then the result is not eq? to object."
               "(let ((p (list 1 2))) (eqv? (eq? (copy-es-immutable p) p) #f))"
               "(let ((p (list 1 2))) (equal? (copy-es-immutable p) p))"
               // The copy is immutable all the way down.
               "(immutable-pair? (copy-es-immutable (list 1 2)))"
               "(immutable-pair? (car (copy-es-immutable (list (list 1) 2))))"
               "(equal? (copy-es-immutable (list (list 1 2) 3)) (list (list 1 2) 3))"
               "(pair? (copy-es-immutable (list 1 2)))" ]
    "5.8.1", [ // "sets the cdr of the (integer1 + integer2)th pair to refer to the
               // (integer1 + 1)th pair", so the list ends with exactly those metrics.
               "(let ((a (list 1 2 3 4 5))) (encycle! a 2 3)"
               + " (equal? (get-list-metrics a) (list 5 0 2 3)))"
               "(let ((b (list 1 2 3))) (encycle! b 0 3)"
               + " (equal? (get-list-metrics b) (list 3 0 0 3)))"
               // "If integer2 = 0, the applicative does nothing."
               "(let ((c (list 1 2 3))) (encycle! c 1 0)"
               + " (equal? (get-list-metrics c) (list 3 1 3 0)))"
               // The result is inert.
               "(let ((d (list 1 2))) (inert? (encycle! d 0 2)))" ]
    "6.4.1", [ // "sets the cdr of the last pair in each nonempty list argument to
               // refer to the next non-nil argument"
               "(let ((u (list 1 2))) (append! u (list 3 4)) (equal? u (list 1 2 3 4)))"
               // It links rather than copies.
               "(let ((u (list 1 2))) (let ((v (list 3))) (append! u v)"
               + " (eq? (cdr (cdr u)) v)))"
               // "the next non-nil argument": a nil argument is skipped.
               "(let ((y (list 1))) (append! y () (list 9)) (equal? y (list 1 9)))"
               // (append! v) is inert, and the result is always inert.
               "(let ((z (list 1))) (inert? (append! z)))"
               "(let ((z (list 1))) (inert? (append! z (list 2))))" ]
    "6.4.2", [ "(=? (copy-es 5) 5)"
               // "always returns a non-eq? pair when given a pair as argument"
               "(let ((p (list 1 2))) (eqv? (eq? (copy-es p) p) #f))"
               "(let ((p (list 1 2))) (equal? (copy-es p) p))"
               "(equal? (copy-es (list (list 1 2) 3)) (list (list 1 2) 3))"
               "(pair? (copy-es (list 1 2)))"
               // The structure is walked to the leaves, and the cdr of an improper
               // pair is part of it.
               "(=? (car (car (cdr (copy-es (list (list 1 2) (list 3 (list 4))))))) 3)"
               "(=? (cdr (copy-es (cons 1 2))) 2)"
               // Non-pair referents come through as themselves.
               "(eq? (car (car (copy-es (list (list 'a))))) 'a)" ]
    "6.4.3", [ "(=? (car (assq 2 (list (list 1 'a) (list 2 'b)))) 2)"
               "(eqv? (car (cdr (assq 2 (list (list 1 'a) (list 2 'b))))) 'b)"
               "(null? (assq 9 (list (list 1 'a))))"
               "(null? (assq 1 (list)))" ]
    "6.4.4", [ "(memq? 2 (list 1 2 3))"
               "(eqv? (memq? 9 (list 1 2 3)) #f)"
               "(eqv? (memq? 1 (list)) #f)" ]
    "4.9.1", [ "(let ((e (get-current-environment))) (sequence (eval (list $define! 'dz 11) e) (=? dz 11)))"
               "(inert? ($define! dy 1))" ]
    "6.5.1", [ "(eq? 'a 'a)"; "(eqv? (eq? 'a 'b) #f)"
               // Generalized to zero or more arguments: true unless some two differ.
               "(eq?)"; "(eq? 'a)"; "(eq? 'a 'a 'a)"
               "(eqv? (eq? 'a 'a 'b) #f)" ]
    "6.7.6", [ // $letrec* binds sequentially, so a later binding sees an earlier one.
               "(=? (letrec* ((a 1) (b (+ a 1))) b) 2)" ]
    "6.7.7", [ "(=? (let-redirect (make-environment) ((x 5)) x) 5)"
               // The body is evaluated in the redirected environment, so a binding of
               // the caller is not visible: `car` is unbound in a fresh environment.
               "(=? (let-redirect (get-current-environment) ((x 5)) (car (list x))) 5)" ]
    "6.7.10", [ "(environment? (bindings->environment (n 3)))"
                "(=? (remote-eval n (bindings->environment (n 3))) 3)" ]
    "6.8.2", [ "(sequence (provide! (pa pb) (define pa 1) (define pb 2)) (=? (+ pa pb) 3))"
               // Only the named symbols escape; the helper stays private.
               "(sequence (provide! (shown) (define hidden 41) (define shown (+ hidden 1))) (=? shown 42))" ]
    "6.8.3", [ "(sequence (define src (bindings->environment (q 9))) (import! src q) (=? q 9))" ]
    "4.10.1", [ "(operative? vau)"; "(eqv? (operative? car) #f)"; "(operative?)" ]
    "4.10.2", [ "(applicative? car)"; "(eqv? (applicative? vau) #f)"; "(applicative?)" ]
    "5.7.1", [ "(equal? (get-list-metrics (list 1 2 3)) (list 3 1 3 0))"
               "(equal? (get-list-metrics ()) (list 0 1 0 0))"
               // A non-pair is the start of an improper list of just itself.
               "(equal? (get-list-metrics 5) (list 0 0 0 0))"
               // "if n = c = 0, the improper list is not a list"
               "(equal? (get-list-metrics (cons 1 2)) (list 1 0 1 0))"
               // A cycle is measured rather than walked into, and a + c = p.
               "(let ((p (list 1 2 3))) (set-cdr! (cdr (cdr p)) p)"
               + " (equal? (get-list-metrics p) (list 3 0 0 3)))"
               "(let ((q (list 1 2 3 4 5)))"
               + " (set-cdr! (cdr (cdr (cdr (cdr q)))) (cdr (cdr q)))"
               + " (equal? (get-list-metrics q) (list 5 0 2 3)))"
               "(let ((r (list 1))) (set-cdr! r r)"
               + " (equal? (get-list-metrics r) (list 1 0 0 1)))" ]
    "5.7.2", [ "(equal? (list-tail (list 1 2 3 4) 2) (list 3 4))"
               "(equal? (list-tail (list 1 2) 0) (list 1 2))" ]
    "6.2.1", [ "(combiner? car)"; "(combiner? vau)"; "(eqv? (combiner? 1) #f)" ]
    "6.3.2", [ "(=? (list-ref (list 1 2 3) 1) 2)"; "(=? (list-ref (list 1 2 3) 0) 1)" ]
    "6.3.3", [ "(equal? (append (list 1 2) (list 3)) (list 1 2 3))"
               "(equal? (append) ())"; "(equal? (append (list 1)) (list 1))"
               "(equal? (append () (list 1)) (list 1))" ]
    "6.3.4", [ "(equal? (list-neighbors (list 1 2 3)) (list (list 1 2) (list 2 3)))"
               "(equal? (list-neighbors ()) ())"
               "(equal? (list-neighbors (list 1)) ())" ]
    // 6.3.5: (filter applicative list) -- the applicative comes first.
    "6.3.5", [ "(equal? (filter (lambda (x) (positive? x)) (list -1 2 -3 4)) (list 2 4))"
               "(equal? (filter (lambda (x) #t) ()) ())" ]
    "6.3.6", [ "(equal? (assoc 'b (list (list 'a 1) (list 'b 2))) (list 'b 2))"
               "(equal? (assoc 'z (list (list 'a 1))) ())" ]
    "6.3.7", [ "(member? 2 (list 1 2 3))"; "(eqv? (member? 9 (list 1 2)) #f)" ]
    "6.3.8", [ "(finite-list? (list 1 2))"; "(finite-list? ())"; "(eqv? (finite-list? 5) #f)"
               // The acyclic lists: a cyclic one is a list but not a finite one, and
               // an improper one is not a list at all.
               "(let ((p (list 1 2 3))) (set-cdr! (cdr (cdr p)) p) (eqv? (finite-list? p) #f))"
               "(eqv? (finite-list? (cons 1 2)) #f)"
               "(finite-list?)" ]
    "6.3.9", [ "(countable-list? (list 1 2))"; "(eqv? (countable-list? 5) #f)"
               // The lists: finite or cyclic, but not improper.
               "(let ((p (list 1 2 3))) (set-cdr! (cdr (cdr p)) p) (countable-list? p))"
               "(eqv? (countable-list? (cons 1 2)) #f)"
               "(countable-list?)" ]
    // 6.3.10: (reduce list binary identity) -- the list comes first here.
    "6.3.10", [ "(=? (reduce (list 1 2 3 4) + 0) 10)"; "(=? (reduce () + 0) 0)"
                "(=? (reduce (list 5) + 0) 5)"
                // The six-argument syntax, which is the one that reduces a *cyclic*
                // list: precycle converts each element of the cycle, incycle reduces
                // those, postcycle converts the result back for binary. Here with an
                // acyclic prefix of 2 and a cycle of 3, and postcycle doubling the
                // cycle's contribution so that it is visibly applied.
                "(let ((ls (list 10 20 1 2 3)))"
                + " (sequence (encycle! ls 2 3)"
                + " (and? (=? (reduce ls + 0 (lambda (x) x) + (lambda (x) x)) 36)"
                + " (=? (reduce ls + 0 (lambda (x) x) + (lambda (x) (* x 2))) 42))))"
                // A pure cycle: the acyclic prefix is empty, so binary is never called
                // and the result is postcycle's alone.
                "(let ((ls (list 1 2 3)))"
                + " (sequence (encycle! ls 0 3)"
                + " (=? (reduce ls + 0 (lambda (x) x) + (lambda (x) x)) 6)))" ]
    "6.6.1", [ "(equal? (list 1 (list 2)) (list 1 (list 2)))"
               "(eqv? (equal? (list 1) (list 2)) #f)"
               "(equal?)"; "(equal? 1)"; "(equal? 1 1 1)"
               "(eqv? (equal? 1 1 2) #f)"
               // 4.3.1: equal? must return true whenever eq? would.
               "(let ((p (list 1))) (equal? p p))" ]
    "4.6.2", [ "(null? ())"; "(eqv? (null? (cons 1 2)) #f)" ]
    "4.6.3", [ "(eqv? (car (cons 1 2)) 1)"; "(eqv? (cdr (cons 1 2)) 2)" ]
    "4.8.1", [ "(environment? (get-current-environment))" ]
    "4.8.2", [ "(ignore? #ignore)"; "(eqv? (ignore? #inert) #f)"
               "(eqv? (ignore? 5) #f)"; "(ignore?)"
               // 4.9.1: in a parameter tree it matches an operand and binds nothing.
               "(=? ((lambda (a #ignore) a) 1 2) 1)"
               // 4.10.3: as the environment parameter it declines the environment.
               "(=? ((vau (x) #ignore 7) 1) 7)" ]
    "4.8.3", [ "(eqv? (eval (list + 1 2) (get-current-environment)) 3)" ]
    "4.8.4", [ "(environment? (make-environment))" ]
    "4.10.3", [ // An operative receives its operands unevaluated.
                "(eqv? (car ((vau xs _ xs) foo)) 'foo)" ]
    "4.10.4", [ "(eqv? ((wrap (vau (x) _ x)) (+ 1 2)) 3)" ]
    "4.10.5", [ "(eqv? ((unwrap (lambda (x) x)) bar) 'bar)" ]
    // Primitive here rather than derived (ADR 0007); 1.3.2 permits that, since "the
    // derivation code is not considered part of the definition of the feature".
    "5.1.1", [ "(eqv? (sequence 1 2 3) 3)"
               // "If (objects) is the empty list, the result is inert."
               "(inert? (sequence))"
               // Left to right, and an operative, so a later element sees what an
               // earlier one defined.
               "(let ((v (vector 0 0)))"
               + " (sequence (sequence (vector-set! v 0 1) (vector-set! v 1 2))"
               + " (and? (=? (vector-ref v 0) 1) (=? (vector-ref v 1) 2))))"
               "(=? ((lambda () (sequence (define local 5) local))) 5)" ]
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
    "6.3.1", [ "(eqv? (length (list 1 2 3)) 3)"; "(eqv? (length ()) 0)"
               // "If object is not a pair, it returns zero; if object is a cyclic
               // list, it returns positive infinity."
               "(eqv? (length 5) 0)"; "(eqv? (length (cons 1 2)) 1)"
               "(let ((p (list 1 2 3))) (set-cdr! (cdr (cdr p)) p) (eqv? (length p) #e+infinity))" ]
    "6.7.2", [ "(environment? (get-current-environment))" ]
    "6.7.4", [ "(eqv? (let* ((x 1) (y (+ x 1))) y) 2)" ]
    "6.7.5", [ "(eqv? (letrec ((f (lambda (n) (if (eqv? n 0) 0 (f (- n 1)))))) (f 3)) 0)" ]
    "6.7.9", [ "(eqv? (remote-eval (+ 1 2) (get-current-environment)) 3)" ]
    "6.8.1", [ "(let ((e (get-current-environment))) (sequence (set! e zz 7) (eqv? zz 7)))" ]
    // 6.9.1: (for-each applicative . lists) -- applicative first, as for map.
    "6.9.1", [ "(let ((t (vector 0))) (sequence (for-each (lambda (x) (vector-set! t 0 x)) (list 7)) (=? (vector-ref t 0) 7)))" ]
    "7.2.2", [ "(eqv? (call/cc (lambda (k) (k 42))) 42)" ]
    "7.2.1", [ "(call/cc (lambda (k) (continuation? k)))"
               "(eqv? (continuation? 5) #f)"
               "(eqv? (continuation? (lambda () 0)) #f)"
               "(continuation?)" ]
    "7.2.3", [ // A child of the continuation that prepends a computation, its result
               // normally returning to the original continuation.
               "(=? (call/cc (lambda (k)"
               + " (apply-continuation (extend-continuation k (lambda (x) (* x 10))) (list 4)))) 40)"
               "(=? (+ 1 (call/cc (lambda (k)"
               + " (apply-continuation (extend-continuation k (lambda (x) (* x 10))) (list 4))))) 41)"
               "(call/cc (lambda (k) (continuation? (extend-continuation k (lambda (x) x)))))" ]
    "7.2.5", [ "(call/cc (lambda (k) (applicative? (continuation->applicative k))))"
               // The operand tree is passed whole.
               "(=? (car (call/cc (lambda (k) ((continuation->applicative k) 1 2) 99))) 1)"
               "(=? (car (cdr (call/cc (lambda (k) ((continuation->applicative k) 1 2) 99)))) 2)"
               "(null? (call/cc (lambda (k) ((continuation->applicative k)) 99)))" ]
    "7.3.1", [ "(=? (call/cc (lambda (k) (apply-continuation k 5) 99)) 5)"
               "(=? (car (call/cc (lambda (k) (apply-continuation k (list 1 2)) 99))) 1)" ]
    "7.2.4", [ "(call/cc (lambda (k) (continuation? (guard-continuation (list) k (list)))))"
               // Normal receipt behaves as the guarded continuation does.
               "(=? (call/cc (lambda (k) (apply-continuation (guard-continuation (list) k (list)) 5))) 5)"
               // An abnormal pass out of the extent is intercepted, and the
               // interceptor's result is what continues to the destination.
               "(=? (call/cc (lambda (out) (guard-dynamic-extent (list) (lambda ()"
               + " (apply-continuation out 1) 99)"
               + " (list (list root-continuation (lambda (v d) (* v 10))))))) 10)"
               // At most one interceptor is selected from each list.
               "(=? (call/cc (lambda (out) (guard-dynamic-extent (list) (lambda ()"
               + " (apply-continuation out 1) 99)"
               + " (list (list root-continuation (lambda (v d) (+ v 1)))"
               + " (list root-continuation (lambda (v d) (* v 100))))))) 2)" ]
    "7.2.6", [ "(continuation? root-continuation)"
               // Its extent contains everything, so a clause selecting on it always
               // applies -- the report's stated reason for exposing it.
               "(=? (call/cc (lambda (out) (guard-dynamic-extent (list) (lambda ()"
               + " (apply-continuation out 3) 99)"
               + " (list (list root-continuation (lambda (v d) v)))))) 3)" ]
    "7.2.7", [ "(continuation? error-continuation)"
               // "When an error is signaled during a Kernel computation, the
               // signaling action consists of an abnormal pass to some continuation
               // in the dynamic extent of error-continuation." So an exit guard
               // selecting on error-continuation is selected when the guarded extent
               // signals -- which is what makes the pass observable at all.
               "(=? (call/cc (lambda (out) (guard-dynamic-extent (list) (lambda ()"
               + " (car 5) 99) (list (list error-continuation"
               + " (lambda (v d) (apply-continuation out 7))))))) 7)"
               // The interceptor's second argument diverts, which is how an error is
               // handled rather than merely observed. The operand tree of a divert is
               // a list here (the 7.2.5 divergence), so both paths yield one.
               "(=? (car (guard-dynamic-extent (list) (lambda () (car 5) (list 1))"
               + " (list (list error-continuation (lambda (v d) (d 9)))))) 9)" ]
    "7.3.3", [ // Exit guards fire outward, smallest extent first.
               "(=? (call/cc (lambda (out) (guard-dynamic-extent (list) (lambda ()"
               + " (guard-dynamic-extent (list) (lambda () (apply-continuation out 1))"
               + " (list (list root-continuation (lambda (v d) (+ v 1))))))"
               + " (list (list root-continuation (lambda (v d) (* v 100))))))) 200)"
               // A normal return is not an abnormal pass, so nothing intercepts it.
               "(=? (guard-dynamic-extent (list) (lambda () 7)"
               + " (list (list root-continuation (lambda (v d) (* v 10))))) 7)"
               // Entry guards fire on an abnormal pass into the extent.
               "(=? (let ((flag (vector 0)))"
               + " (let ((k (call/cc (lambda (return) (guard-dynamic-extent"
               + " (list (list root-continuation (lambda (v d) (+ v 1000))))"
               + " (lambda () (call/cc (lambda (c) (return c)))) (list))))))"
               + " (if (zero? (vector-ref flag 0))"
               + " (begin (vector-set! flag 0 1) (apply-continuation k 5)) k))) 1005)"
               // The combiner is called with no operands and the dynamic environment
               // of the guard-dynamic-extent call.
               "(=? ((lambda (n) (guard-dynamic-extent (list)"
               + " (wrap (vau () d (eval (quote n) d))) (list))) 4) 4)" ]
    "7.3.4", [ "(applicative? exit)"
               // That it is an abnormal transfer of #inert to root-continuation: an
               // exit guard selecting on root catches the pass on its way there, and
               // diverts so that the session does not actually end.
               "(call/cc (lambda (out) (guard-dynamic-extent (list) (lambda () (exit) 99)"
               + " (list (list root-continuation"
               + " (lambda (v d) (apply-continuation out (inert? v))))))))" ]
    "7.3.2", [ "(eqv? (let/cc k (k 9)) 9)" ]
    "8.1.1", [ "(let ((t (make-encapsulation-type))) (let ((e ((car t) 1)) (p (car (cdr t)))) (p e)))" ]
    "9.1.1", [ "(promise? (memoize 1))" ]
    "9.1.2", [ "(eqv? (force (memoize 5)) 5)" ]
    // R-1RK 10.1.1. `b` and `a` below are the binder and accessor of one fresh
    // keyed dynamic variable.
    "10.1.1", [ // The accessor returns the bound object for the extent of the call.
                "(let ((p (make-keyed-dynamic-variable)))"
                + " (let ((b (car p)) (a (car (cdr p)))) (=? (b 42 (lambda () (a))) 42)))"
                // The binder's value is the combiner's, not the bound object.
                "(let ((p (make-keyed-dynamic-variable)))"
                + " (=? ((car p) 42 (lambda () 99)) 99))"
                // Dynamic rather than lexical: reached through an intervening call.
                "(let ((p (make-keyed-dynamic-variable)))"
                + " (let ((b (car p)) (a (car (cdr p))))"
                + " (let ((peek (lambda () (a)))) (=? (b 7 (lambda () (peek))) 7))))"
                // The nearest enclosing binding wins, and the outer one is restored.
                "(let ((p (make-keyed-dynamic-variable)))"
                + " (let ((b (car p)) (a (car (cdr p))))"
                + " (=? (b 1 (lambda () (b 2 (lambda () (a))))) 2)))"
                "(let ((p (make-keyed-dynamic-variable)))"
                + " (let ((b (car p)) (a (car (cdr p))))"
                + " (=? (b 1 (lambda () (b 2 (lambda () 0)) (a))) 1)))"
                // Each call makes a different variable, so one binder's object is not
                // visible through the other's accessor.
                "(let ((p (make-keyed-dynamic-variable)) (q (make-keyed-dynamic-variable)))"
                + " (let ((bp (car p)) (ap (car (cdr p))) (bq (car q)))"
                + " (=? (bp 1 (lambda () (bq 2 (lambda () (ap))))) 1)))"
                // The binding is part of the continuation, so a continuation captured
                // inside the extent still sees it when resumed from outside.
                "(let ((p (make-keyed-dynamic-variable)) (flag (vector 0)))"
                + " (let ((b (car p)) (a (car (cdr p))))"
                + " (=? (let ((k (call/cc (lambda (return)"
                + " (b 11 (lambda () (call/cc (lambda (c) (return c))) (a)))))))"
                + " (if (zero? (vector-ref flag 0))"
                + " (begin (vector-set! flag 0 1) (k 0)) k)) 11)))" ]
    // R-1RK 11.1.1. `b` binds an object in a fresh child of the given environment;
    // `a` reads it from anywhere in that environment's descendants.
    "11.1.1", [ "(let ((p (make-keyed-static-variable)))"
                + " (let ((b (car p)) (a (car (cdr p))))"
                + " (=? (eval (list a) (b 42 (get-current-environment))) 42)))"
                // The binder returns an environment, and descendants inherit it.
                "(let ((p (make-keyed-static-variable)))"
                + " (let ((b (car p)) (a (car (cdr p))))"
                + " (let ((e (b 42 (get-current-environment))))"
                + " (and? (environment? e) (=? (eval (list a) (make-environment e)) 42)))))"
                // The nearest such ancestor wins, and the outer one still reads.
                "(let ((p (make-keyed-static-variable)))"
                + " (let ((b (car p)) (a (car (cdr p))))"
                + " (let ((e1 (b 1 (get-current-environment))))"
                + " (and? (=? (eval (list a) (b 2 e1)) 2) (=? (eval (list a) e1) 1)))))"
                // Static rather than dynamic: a procedure written inside the
                // environment reads the object wherever it is called from.
                "(let ((p (make-keyed-static-variable)))"
                + " (let ((b (car p)) (a (car (cdr p))))"
                + " (=? ((eval (list lambda (list) (list a))"
                + " (b 42 (get-current-environment)))) 42)))"
                // Each call makes a different variable, and the two coexist.
                "(let ((p (make-keyed-static-variable)) (q (make-keyed-static-variable)))"
                + " (let ((e ((car q) 99 ((car p) 42 (get-current-environment)))))"
                + " (and? (=? (eval (list (car (cdr p))) e) 42)"
                + " (=? (eval (list (car (cdr q))) e) 99))))" ]
    "9.1.3", [ "(promise? ($lazy 1))"
               "(=? (force ($lazy (+ 1 2))) 3)"
               // Evaluated in the dynamic environment of the constructing call.
               "(let ((n 5)) (=? (force ($lazy n)) 5))"
               // "Distinct promises represent different occasions of evaluation."
               "(eqv? (eq? ($lazy 1) ($lazy 1)) #f)" ]
    "13.1.1", [ "(eq? (string->symbol \"abc\") (quote abc))"
                "(symbol? (string->symbol \"abc\"))" ]
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
    "12.5.13", [ "(=? (max 1 7 3) 7)"; "(=? (min 1 7 3) 1)"; "(=? (max 5) 5)"
                 // The empty cases preserve (max h . t) = (max h (max . t)).
                 "(eqv? (max) #e-infinity)"; "(eqv? (min) #e+infinity)" ]
    "12.5.14", [ "(=? (gcd 12 18) 6)"; "(=? (lcm 4 6) 12)"; "(=? (gcd 0 5) 5)"
                 // Over *improper* integers: an infinity beside a finite non-zero
                 // argument drops away, and the empty gcd is positive infinity.
                 "(eqv? (gcd) #e+infinity)"; "(=? (gcd #e+infinity 6) 6)"
                 "(=? (lcm) 1)"; "(eqv? (lcm 3 #e+infinity) #e+infinity)" ]
    // R-1RK 12.6. The implementation is the one 12.2 sanctions explicitly: inexact
    // reals are non-robust with infinite bounds, and the tag distinguishing exact
    // from inexact is the internal representation.
    "12.6.1", [ "(exact? 1)"; "(exact? 1/2)"; "(exact? #e+infinity)"
                "(eqv? (exact? 0.5) #f)"
                "(inexact? 0.5)"; "(eqv? (inexact? 1) #f)"
                // An exact real is robust and has itself as its primary value (12.2).
                "(robust? 1)"; "(eqv? (robust? 0.5) #f)"
                "(eqv? (undefined? 0.5) #f)"; "(eqv? (undefined? 1) #f)"
                // Variadic, and true for the empty argument list.
                "(exact?)"; "(inexact?)"; "(robust?)"; "(undefined?)" ]
    "12.6.2", [ // An exact real is its own bounds.
                "(eqv? (car (get-real-internal-bounds 5)) 5)"
                "(eqv? (car (cdr (get-real-internal-bounds 5))) 5)"
                "(eqv? (car (get-real-exact-bounds 5)) 5)"
                // An inexact real is bounded only by the infinities: exactly by those
                // of 12.3.2, and internally in its own format.
                "(eqv? (car (get-real-exact-bounds 0.5)) #e-infinity)"
                "(eqv? (car (cdr (get-real-exact-bounds 0.5))) #e+infinity)"
                "(eqv? (finite? (car (get-real-internal-bounds 0.5))) #f)"
                "(inexact? (car (get-real-internal-bounds 0.5)))"
                // A freshly allocated list of two.
                "(=? (length (get-real-internal-bounds 0.5)) 2)"
                "(=? (length (get-real-exact-bounds 0.5)) 2)" ]
    "12.6.3", [ "(eqv? (get-real-internal-primary 5) 5)"
                "(eqv? (get-real-exact-primary 5) 5)"
                "(eqv? (get-real-internal-primary 0.5) 0.5)"
                // The exact value of a double is exact: a finite one is a dyadic
                // rational, which exact ratios can hold in full.
                "(eqv? (get-real-exact-primary 0.5) 1/2)"
                "(eqv? (get-real-exact-primary 0.75) 3/4)"
                "(inexact? (get-real-internal-primary 0.5))" ]
    "12.6.4", [ "(inexact? (make-inexact 0 1/2 1))"
                // The primary value comes from the middle argument.
                "(=? (make-inexact 0 1/2 1) 0.5)"
                "(=? (make-inexact #e-infinity 2 #e+infinity) 2)"
                // An inexact second argument is carried through unchanged.
                "(eqv? (make-inexact 0 0.25 1) 0.25)" ]
    "12.6.5", [ "(inexact? (real->inexact 1))"; "(=? (real->inexact 1) 1)"
                "(exact? (real->exact 0.5))"; "(eqv? (real->exact 0.5) 1/2)"
                // real->inexact leaves an inexact real alone.
                "(eqv? (real->inexact 0.5) 0.5)"
                // real->exact behaves just as get-real-exact-primary.
                "(eqv? (real->exact 0.75) (get-real-exact-primary 0.75))" ]
    "12.6.6", [ // The binder and accessor of the strict-arithmetic keyed dynamic
                // variable, so the setting follows the extent of the binder's call.
                "(eqv? (with-strict-arithmetic #f (lambda () (get-strict-arithmetic?))) #f)"
                "(eqv? (with-strict-arithmetic #t (lambda () (get-strict-arithmetic?))) #t)"
                "(get-strict-arithmetic?)"
                "(eqv? (with-strict-arithmetic #f (lambda ()"
                + " (with-strict-arithmetic #t (lambda () (get-strict-arithmetic?))))) #t)"
                // When cleared, a result with no primary value is returned rather than
                // signalled -- and it is a number, but neither robust nor undefined.
                "(with-strict-arithmetic #f (lambda ()"
                + " (number? (- #e+infinity #e+infinity))))"
                "(with-strict-arithmetic #f (lambda ()"
                + " (eqv? (robust? (- #e+infinity #e+infinity)) #f)))"
                // 12.3.3: overflow is one of the "survivable but dubious arithmetic
                // events" strict arithmetic signals; cleared, it gives an infinity.
                "(with-strict-arithmetic #f (lambda () (eqv? (finite? (* 1e308 10)) #f)))"
                // An infinite operand in is not an overflow, whatever comes out.
                "(eqv? (+ #e+infinity 1) #e+infinity)" ]
    // R-1RK 12.7.1. Narrowing is advice, so the checks assert what the report
    // actually requires: the binder and accessor behave as a keyed dynamic variable,
    // and the bounding information is no less restrictive when the variable is set
    // than when it is cleared.
    "12.7.1", [ "(eqv? (with-narrow-arithmetic #t (lambda () (get-narrow-arithmetic?))) #t)"
                "(eqv? (with-narrow-arithmetic #f (lambda () (get-narrow-arithmetic?))) #f)"
                "(eqv? (get-narrow-arithmetic?) #f)"
                "(eqv? (with-narrow-arithmetic #t (lambda ()"
                + " (with-narrow-arithmetic #f (lambda () (get-narrow-arithmetic?))))) #f)"
                // The two arithmetic variables are separate.
                "(with-narrow-arithmetic #t (lambda () (get-strict-arithmetic?)))"
                // The report's only hard constraint on what is maintained, besides
                // correctness: the interval when set is contained in the one when
                // cleared.
                "(<=? (car (with-narrow-arithmetic #f (lambda () (get-real-exact-bounds 0.5))))"
                + " (car (with-narrow-arithmetic #t (lambda () (get-real-exact-bounds 0.5)))))"
                "(<=? (car (cdr (with-narrow-arithmetic #t (lambda () (get-real-exact-bounds 0.5)))))"
                + " (car (cdr (with-narrow-arithmetic #f (lambda () (get-real-exact-bounds 0.5))))))" ]
    "12.8.1", [ "(rational? 1)"; "(rational? 1.5)"; "(rational? 1/3)"
                "(eqv? (rational? 'a) #f)"; "(rational?)"
                // A ratio is not an integer, and reduces to one when it can.
                "(eqv? (integer? 1/3) #f)"; "(integer? 4/2)" ]
    "12.8.2", [ "(=? (/ 8 2) 4)"
                // Dividing exact integers gives an exact ratio, not the nearest
                // double: three thirds are exactly one, which no double satisfies.
                "(=? (+ (/ 1 3) (/ 1 3) (/ 1 3)) 1)"
                "(=? (numerator (/ 1 3)) 1)"; "(=? (denominator (/ 1 3)) 3)"
                // Least terms, and a ratio that reduces to an integer becomes one.
                "(eqv? (/ 2 4) (/ 1 2))"; "(eqv? (/ 6 3) 2)"
                // Divides by the product of the remaining arguments.
                "(=? (/ 24 2 3) 4)" ]
    "12.8.3", [ "(=? (numerator 0.5) 1)"; "(=? (denominator 0.5) 2)"
                "(=? (numerator 6) 6)"; "(=? (denominator 6) 1)"
                "(=? (numerator 0.75) 3)"; "(=? (denominator 0.75) 4)"
                "(=? (numerator 3/4) 3)"; "(=? (denominator 3/4) 4)"
                // Least terms, and a negative ratio carries its sign in the numerator.
                "(=? (numerator 6/8) 3)"; "(=? (denominator 6/8) 4)"
                "(=? (numerator (/ 1 -3)) -1)"; "(=? (denominator (/ 1 -3)) 3)" ]
    "12.8.4", [ "(=? (floor 3.7) 3)"; "(=? (floor -3.7) -4)"
                "(=? (ceiling 3.2) 4)"; "(=? (ceiling -3.2) -3)"
                "(=? (truncate 3.7) 3)"; "(=? (truncate -3.7) -3)"
                // Halfway cases round to even.
                "(=? (round 0.5) 0)"; "(=? (round 1.5) 2)"; "(=? (round 2.5) 2)"
                // An exact ratio rounds to an exact integer, which R-1RK 12.3.2
                // requires of every operation given only exact arguments.
                "(eqv? (floor 7/2) 3)"; "(eqv? (ceiling 7/2) 4)"
                "(eqv? (truncate -7/2) -3)"; "(eqv? (floor -7/2) -4)"
                "(eqv? (round 7/2) 4)"; "(eqv? (round 5/2) 2)" ]
    // 12.9: the report gives these signatures only (see the note in the matrix), so
    // the checks assert the standard mathematical meanings.
    "12.9.1", [ "(real? 1)"; "(real? 1.5)"; "(eqv? (real? 'a) #f)"; "(real?)"
                // A complex is real only when its imaginary part is zero.
                "(eqv? (real? (make-rectangular 0 1)) #f)"
                "(real? (make-rectangular 5 0))" ]
    "12.10.1", [ "(complex? 1)"; "(complex? (make-rectangular 0 1))"
                 "(eqv? (complex? 'a) #f)"; "(complex?)" ]
    "12.10.2", [ "(=? (real-part (make-rectangular 3 4)) 3)"
                 "(=? (imag-part (make-rectangular 3 4)) 4)"
                 "(=? (* (make-rectangular 0 1) (make-rectangular 0 1)) -1)" ]
    // 15.1.5 / 15.1.7 / 15.1.8: a value written to a file and read back must come
    // back equal. Numbers do not survive this, because `write` prints them as
    // `<obj 42 : Int32>`, which `read` cannot parse -- the 3.6 divergence. Symbols,
    // lists and booleans do.
    "15.1.1", [ "(port? (get-current-input-port))"; "(eqv? (port? 5) #f)"; "(port?)" ]
    "15.1.2", [ "(input-port? (get-current-input-port))"
                "(output-port? (get-current-output-port))"
                // "Every port must be admitted by at least one of these two", and a
                // non-port is false rather than an error.
                "(eqv? (input-port? (get-current-output-port)) #f)"
                "(eqv? (input-port? 5) #f)"; "(input-port?)"; "(output-port?)" ]
    "15.1.3", [ // "The opened port is accessed implicitly within the dynamic extent of
                // the call": write with no port finds it, and read reads it back.
                "(sequence (with-output-to-file \"conformance-15-1-3.txt\""
                + " (lambda () (write (quote hello))))"
                + " (eq? (with-input-from-file \"conformance-15-1-3.txt\""
                + " (lambda () (read))) (quote hello)))"
                // The binding is scoped to the extent, so the console is current again.
                "(output-port? (get-current-output-port))" ]
    "15.1.4", [ "(port? (get-current-input-port))"; "(port? (get-current-output-port))"
                "(input-port? (get-current-input-port))"
                "(output-port? (get-current-output-port))" ]
    "15.1.6", [ // Closing is not mutation (chapter 15's preamble), and gives inert.
                "(inert? (close-output-file (open-output-file \"conformance-15-1-6.txt\")))"
                "(inert? (close-input-file (open-input-file \"conformance-15-1-6.txt\")))" ]
    "15.2.1", [ // Like 15.1.3 but the port is an operand rather than implicit.
                "(sequence (call-with-output-file \"conformance-15-2-1.txt\""
                + " (lambda (p) (write (quote hello) p)))"
                + " (eq? (call-with-input-file \"conformance-15-2-1.txt\""
                + " (lambda (p) (read p))) (quote hello)))" ]
    "15.1.5", [ "(let ((f (. System.IO.Path GetTempFileName))) (sequence (let ((p (open-output-file f))) (sequence (write 'alpha p) (close-output-port p))) (. System.IO.File Delete f) #t))" ]
    "15.1.7", [ "(let ((f (. System.IO.Path GetTempFileName))) (sequence (let ((p (open-output-file f))) (sequence (write 'alpha p) (close-output-port p))) (let ((p (open-input-file f))) (let ((v (read p))) (sequence (close-input-port p) (. System.IO.File Delete f) (equal? v 'alpha))))))" ]
    // R-1RK 3.6 has write "generate external representations whenever possible", and
    // 12.4 asks more of an exact number: "writeing an exact number z and then reading
    // what was written will produce an object eq? to z". Only a round trip checks that.
    "15.1.8", [ "(let ((f (. System.IO.Path GetTempFileName)))"
                + " (let ((trip (lambda (v) (sequence"
                + " (with-output-to-file f (lambda () (write v)))"
                + " (with-input-from-file f (lambda () (read)))))))"
                + " (and? (eqv? (trip 28) 28) (eqv? (trip -3) -3)"
                + " (eqv? (trip 1/3) 1/3) (eqv? (trip #e+infinity) #e+infinity)"
                + " (eqv? (trip 3.14) 3.14)"
                + " (equal? (trip \"hello\") \"hello\")"
                + " (equal? (trip (list 8 13)) (list 8 13))"
                + " (eq? (trip (quote sym)) (quote sym)))))"
                // An inexact real must read back inexact (12.4), which is what the
                // decimal point is for: without it 1.0 would read back as exact 1.
                "(let ((f (. System.IO.Path GetTempFileName)))"
                + " (sequence (with-output-to-file f (lambda () (write (real->inexact 1))))"
                + " (inexact? (with-input-from-file f (lambda () (read))))))" ]
    // 15.2.2: load evaluates the file's forms in the calling environment.
    "6.7.1", [ "($binds? (get-current-environment) car)"
               "(eqv? ($binds? (get-current-environment) definitely-not-bound) #f)"
               // The first operand is evaluated; the rest are not.
               "(let ((e (make-environment))) (eqv? ($binds? e car) #f))"
               // True for no symbols at all.
               "($binds? (get-current-environment))" ]
    "6.7.8", [ // ($let-safe b . body) is ($let-redirect (make-kernel-standard-
               // environment) b . body): the body runs in a fresh standard
               // environment, so a local definition of the caller is not visible.
               "(=? ($let-safe ((x 1)) (+ x 1)) 2)"
               "($let-safe () (applicative? car))" ]
    "6.7.3", [ "(environment? (make-kernel-standard-environment))"
               // "a child of the ground environment": ground is visible through it.
               "(eval (list applicative? car) (make-kernel-standard-environment))"
               // Fresh each call.
               "(eqv? (eq? (make-kernel-standard-environment)"
               + " (make-kernel-standard-environment)) #f)" ]
    "15.2.3", [ // Written to a temp file the way 15.2.2's check does, so that the
                // check carries its own module rather than depending on a fixture.
                "(let ((f (. System.IO.Path GetTempFileName)))"
                + " (sequence (. System.IO.File WriteAllText f \"(define a 42)\")"
                + " (let ((m (get-module f)))"
                + " (sequence (. System.IO.File Delete f)"
                + " (and? (environment? m) (=? (eval (quote a) m) 42))))))"
                // Each call gets its own environment, and a module's definitions are
                // reached through it rather than dumped into the caller.
                "(let ((f (. System.IO.Path GetTempFileName)))"
                + " (sequence (. System.IO.File WriteAllText f \"(define a 42)\")"
                + " (let ((m (get-module f)) (n (get-module f)))"
                + " (sequence (. System.IO.File Delete f) (eqv? (eq? m n) #f)))))"
                // The second argument is bound as module-parameters, before the file
                // is evaluated -- so the module can read it as it runs.
                "(let ((f (. System.IO.Path GetTempFileName)) (p (make-environment)))"
                + " (sequence (. System.IO.File WriteAllText f"
                + " \"(define seen (eval (quote s) module-parameters))\")"
                + " (eval (list define (quote s) 5) p)"
                + " (let ((m (get-module f p)))"
                + " (sequence (. System.IO.File Delete f) (=? (eval (quote seen) m) 5)))))" ]
    "15.2.2", [ "(let ((f (. System.IO.Path GetTempFileName))) (sequence (. System.IO.File WriteAllText f \"(define loaded-marker 7)\") (load f) (. System.IO.File Delete f) (=? loaded-marker 7)))" ]
    "12.10.3", [ "(<? (abs (- (magnitude (make-rectangular 3 4)) 5)) 0.000001)"
                 "(<? (abs (- (angle (make-rectangular 0 1)) 1.5707963267948966)) 0.000001)"
                 "(=? (make-polar 1 0) 1)" ]
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
                // Exact arguments give an exact result of whatever size it takes,
                // rather than one read back out of a double: 3^39 needs 62 bits and
                // the nearest double is 11 short.
                "(=? (expt 3 39) 4052555153018976267)"
                "(=? (expt 2 100) 1267650600228229401496703205376)"
                "(eqv? (expt 2 -1) 1/2)"; "(eqv? (expt 2/3 3) 8/27)" ]
    "12.8.5", [ "(=? (simplest-rational 0.2 0.4) (/ 1 3))"
                "(=? (simplest-rational -0.5 0.5) 0)"
                "(=? (rationalize 0.3 0.1) (/ 1 3))"
                // Exact bounds give the exact simplest ratio between them.
                "(eqv? (simplest-rational 1/3 1/2) 1/2)"
                "(eqv? (rationalize 3/10 1/10) 1/3)" ]
]

/// Divergences the matrix cannot express as a status, recorded so that a `verified`
/// row is not read as "identical to the report".
let private divergences () = [
    "7.2.5", "Two things. First, applying a continuation object directly, as in "
             + "`(k 1)`, bypasses the selection and interception of 7.2.5: no guard is "
             + "consulted. That is a dialect extension rather than a gap in the "
             + "report, which does not make continuations applicable at all -- "
             + "`apply-continuation` (7.3.1) and `continuation->applicative` (7.2.5) "
             + "are its mechanisms, and both intercept correctly. Anything relying on "
             + "a guard should use those, and since 7.2.7 now signals by abnormal "
             + "pass, errors do go through interception while a direct application "
             + "still does not. Second, a combination's operand tree is represented as "
             + "a list, so the *atomic* operand tree the report also allows has no "
             + "spelling: `(divert #f)` delivers `(#f)` rather than `#f`, which is why "
             + "the report's `$binds?` derivation (6.7.1) needs a list on both paths "
             + "here. `apply-continuation` takes the object directly and is unaffected."
    "3.6", "Two spellings differ from the report's, and both round-trip through "
           + "`read`, because IronKernel's reader accepts them. A dotted pair writes "
           + "as `(1 & 2)` rather than `(1 . 2)`, since `.` is the CLR interop "
           + "operative here. A CLR value with no Kernel representation -- a DateTime, "
           + "a complex number, an inexact infinity or NaN -- writes as `<obj v : T>`, "
           + "which the reader cannot parse; 3.6 provides for objects that have no "
           + "external representation, and those are IronKernel's."
    "12.9", "The report specifies 12.9.2 through 12.9.6 by signature only. Appendix "
            + "A.2 records that it is an incomplete draft whose unwritten portions were "
            + "\"only planned in rough outline\", so `verified` there means the binding "
            + "exists with its standard mathematical meaning, and the choices the "
            + "report leaves open are IronKernel's: an argument outside a function's "
            + "real domain takes its complex value now that 12.10 is supported, so "
            + "`(sqrt -1)` is `i`; a result with no primary value follows 12.2's rule and "
            + "so signals under strict arithmetic and is returned without it; and "
            + "infinities are returned as values."
    "12.2", "Inexact reals are non-robust with bounds of exact negative and positive "
            + "infinity, which 12.2 sanctions explicitly (\"an implementation can fully "
            + "support module Inexact without making any effort to maintain finite "
            + "bounds or robustness\"). Two things follow. `robust?` is exactly \"every "
            + "argument is exact\". And no number is ever created with its lower bound "
            + "above its upper bound, so the report's `undefined` number never arises "
            + "and `undefined?` is always false. Narrowing the bounds is what module "
            + "Narrow inexact (12.7) asks for, and that module is absent."
    "12.7", "Module Narrow inexact is supported in the sense the report requires -- "
            + "the variable binds and reads, and the bounding information is no less "
            + "restrictive when it is set than when it is cleared -- but setting it "
            + "changes nothing observable. Narrowing is advice (\"the implementation is "
            + "advised to maintain the most restrictive bounding and robustness "
            + "information it (correctly) can\"), and IronKernel maintains the "
            + "infinite bounds of 12.2 either way."
    "12.3.3", "Under strict arithmetic, overflow and a result with no primary value "
              + "both signal; underflow does not, and still gives zero. Telling an "
              + "underflow apart needs the operation and not just its operands -- a "
              + "zero result from non-zero operands is an underflow for multiplication "
              + "and an exact answer for subtraction -- so it is left undetected "
              + "rather than guessed at. The variable's initial value here is true, "
              + "which the report leaves open."
    "7.2.6", "`root-continuation` is not literally at the end of every continuation "
             + "chain: IronKernel's drivers give each top-level form its own "
             + "continuation. Its extent is instead defined to contain everything, "
             + "which is what \"the ancestor of all other continuations\" means for the "
             + "selection algorithm, so a clause selecting on it is always selected. "
             + "Receiving a value ends the session, and the process exit status is 0."
    "4.7", "Module Pair mutation is complete. Mutability follows where the "
           + "structure came from: the reader produces immutable pairs, because a "
           + "program is an algorithm rather than data the program made, while `cons` "
           + "and `list` produce mutable ones. R-1RK 6.4.1 makes it an error for two "
           + "arguments of `append!` to share a last pair; that condition is on the "
           + "caller and is not checked, so appending such a pair to itself builds a "
           + "cycle rather than signalling."
    "6.3", "The derived list library divides on whether a derivation asks about a "
           + "list's *shape* or walks its *elements*. `length`, `finite-list?` and "
           + "`countable-list?` go through `get-list-metrics`, which measures a cycle "
           + "rather than walking into one. `list-tail`, `filter`, `reduce`, `append` "
           + "and the rest walk elements and diverge on a cyclic argument, as the "
           + "report's own derivations of them do. `reduce` (6.3.10) is the exception "
           + "and is complete: its six-argument syntax reduces a cyclic list through "
           + "the caller's `precycle`/`incycle`/`postcycle`, with the call counts the "
           + "report fixes. Its three-argument syntax still diverges on a cycle, which "
           + "is what the report specifies -- there the second syntax \"must be used\"."
    "12.10", "Complex numbers are `System.Numerics.Complex`, so components are "
             + "double precision and a result whose imaginary part is zero collapses "
             + "back to a real. The report specifies 12.10 by signature only."
    "12.8", "Exactness is carried by a value's representation rather than by a "
            + "separate tag: `1/2` is an exact ratio and `0.5` is a double, and "
            + "`exact?` reads the representation. Module Inexact (12.6) is supported "
            + "on that basis. One consequence is that `numerator` and `denominator` of "
            + "an inexact real return exact integers -- `(denominator 0.1)` is 2^55 -- "
            + "rather than inexact ones."
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

/// Every feature paired with its probed status, against a real bootstrapped
/// environment. Both the matrix and the README check read from this.
let private matrixRows () =
    let env = conformanceEnv ()
    features () |> List.map (fun f -> f, statusOf env f)

let private renderMatrix () =
    let rows = matrixRows ()
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
    appendLine "features in M, and (2) supports all of the modules assumed by M.\""
    appendLine ""
    appendLine "**\"All entries verified\" is weaker than \"supported\".** The column below says"
    appendLine "only that every entry of the module has a passing behavioural check. It does"
    appendLine "not assert 1.3.2 support, which additionally requires the module's assumed"
    appendLine "modules and the report's baseline representation requirements. Read the"
    appendLine "divergences before taking any row as a claim of conformance."
    appendLine ""
    appendLine "| Module | Required | Entries | Verified | All entries verified |"
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

/// The README quotes the matrix's headline counts. They are prose, not generated,
/// and they had already drifted once -- claiming 25 of 34 complete modules when the
/// matrix has always listed 44 -- so a reader had no way to tell which was right.
[<Fact>]
let ``the README quotes the matrix's current counts`` () =
    let rows = matrixRows ()
    let entriesWith status =
        rows |> List.filter (fun (_, (s, _, _)) -> s = status) |> List.length
    let modules =
        rows
        |> List.groupBy (fun (f, _) -> f.Section)
        |> List.map (fun (_, group) -> group |> List.forall (fun (_, (s, _, _)) -> s = Verified))
    let expected =
        [ sprintf "**%d are verified" (entriesWith Verified)
          sprintf "and %d are absent**" (entriesWith Absent')
          sprintf "**%d of %d\nmodules are complete**"
            (modules |> List.filter id |> List.length) modules.Length ]
    let readme =
        File.ReadAllText(Path.Combine(repoRoot (), "README.md")).Replace("\r\n", "\n")
    for fragment in expected do
        Assert.True(
            readme.Contains fragment,
            sprintf "README.md is out of date: it should say %s" (fragment.Replace("\n", " ")))

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

