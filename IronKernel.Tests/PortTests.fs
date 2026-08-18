module IronKernel.Tests.PortTests

open System.IO
open Xunit
open IronKernel.Ast
open IronKernel.Tests.TestHelpers

/// Each test writes into its own file under the temp directory and removes it after,
/// so that a failure cannot leave one test's output where another expects to read it.
let private withTempFiles count (body: string list -> unit) =
    let paths =
        [ for index in 1 .. count ->
            Path.Combine(Path.GetTempPath(), sprintf "ironkernel-port-%s-%d.txt" (string (System.Guid.NewGuid())) index) ]
    try body paths
    finally for path in paths do (try File.Delete path with _ -> ())

let private quoted (path: string) = "\"" + path.Replace("\\", "\\\\") + "\""

[<Fact>]
let ``port? and the direction predicates`` () =
    // R-1RK 15.1.1 is the primitive type predicate; 15.1.2's two "return true unless
    // one or more of its arguments is not an input/output port", so a non-port is
    // false rather than an error. "Every port must be admitted by at least one."
    [
        "(port? (get-current-input-port))", Bool true
        "(port? (get-current-output-port))", Bool true
        "(eqv? (port? 5) #f)", Bool true
        "(eqv? (port? (list 1)) #f)", Bool true
        "(port?)", Bool true
        "(input-port? (get-current-input-port))", Bool true
        "(output-port? (get-current-output-port))", Bool true
        // The standard ports go one way each.
        "(eqv? (input-port? (get-current-output-port)) #f)", Bool true
        "(eqv? (output-port? (get-current-input-port)) #f)", Bool true
        "(eqv? (input-port? 5) #f)", Bool true
        "(input-port?)", Bool true
        "(output-port?)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``with-output-to-file makes its port the implicit current one`` () =
    // R-1RK 15.1.3, and chapter 15's preamble: "the opened port is accessed implicitly
    // within the dynamic extent of the call, and is automatically closed on normal
    // return". `write` with no port is what "implicitly" means.
    withTempFiles 1 (fun paths ->
        let file = quoted paths.[0]
        [
            // The report gives 15.1.3 by signature only; returning the combiner's
            // result is the natural reading, and write's result is what that is.
            "(with-output-to-file " + file + " (lambda () (write (quote hello))))", Bool true
            // Read it back through the matching form.
            "(eq? (with-input-from-file " + file + " (lambda () (read))) (quote hello))", Bool true
            // The binding is scoped to the extent, so the console is current again.
            "(output-port? (get-current-output-port))", Bool true
            "(input-port? (get-current-input-port))", Bool true
        ] |> evalSessionKernel)

[<Fact>]
let ``the current port binding nests and unwinds`` () =
    withTempFiles 2 (fun paths ->
        let outer, inner = quoted paths.[0], quoted paths.[1]
        [
            "(with-output-to-file " + outer + " (lambda ()"
            + " (with-output-to-file " + inner + " (lambda () (write (quote inside))))"
            + " (write (quote outside))))", Bool true
            "(eq? (with-input-from-file " + outer + " (lambda () (read))) (quote outside))", Bool true
            "(eq? (with-input-from-file " + inner + " (lambda () (read))) (quote inside))", Bool true
        ] |> evalSessionKernel)

[<Fact>]
let ``call-with-*-file hands the port over instead of binding it`` () =
    // R-1RK 15.2.1. The preamble's second idiom: an explicit reference, still closed
    // on return.
    withTempFiles 1 (fun paths ->
        let file = quoted paths.[0]
        [
            "(call-with-output-file " + file + " (lambda (p) (write (quote hello) p)))", Bool true
            "(eq? (call-with-input-file " + file + " (lambda (p) (read p))) (quote hello))", Bool true
            // The port really is the operand, and it is an output port inside.
            "(call-with-output-file " + file + " (lambda (p) (output-port? p)))", Bool true
            // It does not disturb the current port.
            "(output-port? (get-current-output-port))", Bool true
        ] |> evalSessionKernel)

[<Fact>]
let ``open and close are the third idiom`` () =
    // The preamble's third: the programmer takes on the whole lifetime. 15.1.6's
    // closing is not mutation (a port's state is administrative) and gives inert.
    withTempFiles 1 (fun paths ->
        let file = quoted paths.[0]
        [
            "(define p (open-output-file " + file + "))", Inert
            "(port? p)", Bool true
            "(output-port? p)", Bool true
            "(inert? (close-output-file p))", Bool true
            "(define q (open-input-file " + file + "))", Inert
            "(input-port? q)", Bool true
            "(inert? (close-input-file q))", Bool true
        ] |> evalSessionKernel)

[<Fact>]
let ``the closing applicatives check the direction and the type`` () =
    withTempFiles 1 (fun paths ->
        let file = quoted paths.[0]
        withKernel (fun env ->
            match evalIn env ("(define p (open-output-file " + file + "))") with
            | Status message -> failwithf "setup failed: %s" message
            | _ -> ()
            // An output port is not an input port, so close-input-file refuses it.
            match evalIn env "(close-input-file p)" with
            | Status message -> Assert.Contains("input", message)
            | value -> failwithf "closing an output port as input gave %s" (showVal value)
            for expression in [ "(close-output-file 5)"; "(close-output-file)"; "(port? )" ] do
                match evalIn env expression with
                | Status _ | Bool _ -> ()
                | value -> failwithf "%s gave %s" expression (showVal value)
            ignore (evalIn env "(close-output-file p)")))

[<Fact>]
let ``reading past the end of a port signals rather than faulting`` () =
    // ReadLine returns null at end of input, and the parser dereferences what it is
    // given, so a read past the end reached it as a null string and aborted the
    // process. IronKernel has no end-of-file object to return instead, so this
    // signals. A test host that runs this at all is part of the check.
    withTempFiles 1 (fun paths ->
        // The file has to exist and be empty: opening a missing one for input is now
        // an error in its own right, which is a different thing to test.
        File.WriteAllText(paths.[0], "")
        let file = quoted paths.[0]
        withKernel (fun env ->
            match evalIn env ("(call-with-input-file " + file + " (lambda (p) (read p)))") with
            | Status message -> Assert.Contains("end of input", message)
            | value -> failwithf "reading an empty port gave %s" (showVal value)
            // The environment is still usable: this is an ordinary Kernel error.
            match evalIn env "(port? (get-current-input-port))" with
            | Bool true -> ()
            | value -> failwithf "the environment did not survive: %s" (showVal value)))

[<Fact>]
let ``a port survives more than one write`` () =
    // Both directions now leave the stream open when the reader or writer is disposed,
    // so a port is usable until 15.1.6 closes it. Disposing the writer used to be
    // avoided instead, which left its finalizer to flush to a closed stream later.
    withTempFiles 1 (fun paths ->
        let file = quoted paths.[0]
        [
            "(define p (open-output-file " + file + "))", Inert
            "(write (quote one) p)", Bool true
            "(write (quote two) p)", Bool true
            "(inert? (close-output-file p))", Bool true
        ] |> evalSessionKernel)

[<Fact>]
let ``make-kernel-standard-environment is a fresh child of ground`` () =
    // R-1RK 6.7.3: "a child of the ground environment with no local bindings". The
    // report's own derivation is ($lambda () (get-current-environment)), which works
    // because library derivations are evaluated in the ground environment.
    [
        "(environment? (make-kernel-standard-environment))", Bool true
        // Fresh each call, which 4.2.1 requires of environments anyway.
        "(eqv? (eq? (make-kernel-standard-environment) (make-kernel-standard-environment)) #f)",
            Bool true
        // Ground is visible through it.
        "(eval (list applicative? car) (make-kernel-standard-environment))", Bool true
        "(eval (list (quote =?) 1 1) (make-kernel-standard-environment))", Bool true
        // Defining in one does not disturb another, nor the caller.
        "(define a (make-kernel-standard-environment))", Inert
        "(eval (list define (quote x) 1) a)", Inert
        "(=? (eval (quote x) a) 1)", Bool true
        "(eqv? (eq? a (make-kernel-standard-environment)) #f)", Bool true
    ] |> evalSessionKernel

[<Fact>]
let ``get-module evaluates a file into a fresh standard environment`` () =
    // R-1RK 15.2.3: creates a fresh standard environment, evaluates the file's
    // expressions in it consecutively, and returns it.
    withTempFiles 1 (fun paths ->
        let modulePath = Path.ChangeExtension(paths.[0], ".ikr")
        File.WriteAllText(modulePath, "(define answer 42)\n(define twice (lambda (x) (* 2 x)))\n")
        try
            [
                "(define m (get-module " + quoted modulePath + "))", Inert
                "(environment? m)", Bool true
                "(=? (eval (quote answer) m) 42)", Bool true
                "(=? (eval (list (quote twice) 21) m) 42)", Bool true
                // Each call gets its own environment, so modules cannot see each other.
                "(eqv? (eq? m (get-module " + quoted modulePath + ")) #f)", Bool true
            ] |> evalSessionKernel
        finally (try File.Delete modulePath with _ -> ()))

[<Fact>]
let ``a module's definitions do not reach the caller`` () =
    // The point of get-module over load: "starting each module in a fresh standard
    // environment", so that a file's definitions are reached through the returned
    // environment rather than dumped into whoever loaded it.
    withTempFiles 1 (fun paths ->
        let modulePath = Path.ChangeExtension(paths.[0], ".ikr")
        File.WriteAllText(modulePath, "(define module-only 7)\n")
        try
            withKernel (fun env ->
                match evalIn env ("(define m (get-module " + quoted modulePath + "))") with
                | Status message -> failwithf "get-module failed: %s" message
                | _ -> ()
                match evalIn env "(eval (quote module-only) m)" with
                | Obj (:? int as value) -> Assert.Equal(7, value)
                | value -> failwithf "the module binding was not reachable: %s" (showVal value)
                match evalIn env "module-only" with
                | Status message -> Assert.Contains("unbound", message)
                | value -> failwithf "the module leaked into the caller: %s" (showVal value))
        finally (try File.Delete modulePath with _ -> ()))

[<Fact>]
let ``the second argument is bound as module-parameters`` () =
    // 15.2.3: the fresh environment "is augmented, prior to evaluating read
    // expressions, by binding symbol module-parameters to the optional argument".
    // Prior matters: the module can read it while it is being evaluated.
    withTempFiles 1 (fun paths ->
        let modulePath = Path.ChangeExtension(paths.[0], ".ikr")
        File.WriteAllText(modulePath, "(define seen (eval (quote setting) module-parameters))\n")
        try
            [
                "(define params (make-environment))", Inert
                "(eval (list define (quote setting) 5) params)", Inert
                "(define m (get-module " + quoted modulePath + " params))", Inert
                // The module read it while being evaluated.
                "(=? (eval (quote seen) m) 5)", Bool true
                "(eq? (eval (quote module-parameters) m) params)", Bool true
            ] |> evalSessionKernel
        finally (try File.Delete modulePath with _ -> ()))

[<Fact>]
let ``opening a missing file for input is an error rather than a creation`` () =
    // OpenOrCreate for input meant a missing file was silently created empty and then
    // read as nothing, which also left the file behind -- the CLR fault sweep noticed
    // by leaving one in the repository.
    withTempFiles 1 (fun paths ->
        let file = quoted paths.[0]
        withKernel (fun env ->
            match evalIn env ("(open-input-file " + file + ")") with
            | Status _ -> ()
            | value -> failwithf "opening a missing file gave %s" (showVal value)
            Assert.False(File.Exists paths.[0], "opening for input created the file")
            // Opening for output does create it, which is what output is for.
            match evalIn env ("(close-output-file (open-output-file " + file + "))") with
            | Inert -> ()
            | value -> failwithf "opening for output gave %s" (showVal value)
            Assert.True(File.Exists paths.[0], "opening for output did not create the file")))
