module IronKernel.Tests.ErrorTests

open Xunit
open IronKernel.Ast
open IronKernel.Errors
open IronKernel.Tests.TestHelpers

[<Fact>]
let ``extractValue renders structured errors`` () =
    let result = extractValue (throwError (UnboundVar("Missing binding", "value")))
    match result with
    | Status message -> Assert.Equal("Missing binding: 'value' ", message)
    | value -> failwithf "expected error status, got %A" value
[<Fact>]
let ``operations that fail in the CLR signal Kernel errors`` () =
    // A CLR exception escaping a primitive aborts the process, taking the REPL or
    // script host with it. Division by zero, arithmetic overflow and file I/O each
    // did this before being guarded; these are the remaining cases found by sweeping
    // the primitive surface. A test host that runs this at all is part of the check:
    // before the fix these expressions terminated the process rather than failing.
    let env = freshEnv ()
    let cases =
        [ "(vector-ref (vector 1 2) 5)", "outside a vector"
          "(vector-ref (vector 1 2) -1)", "outside a vector"
          "(vector-ref (vector) 0)", "outside a vector"
          "(vector-set! (vector 1 2) 9 0)", "outside a vector"
          "(printf \"{0} {1}\" 1)", "printf" ]
    for expression, fragment in cases do
        match evalIn env expression with
        | Status message -> Assert.Contains(fragment, message)
        | value -> failwithf "%s should signal an error, got %s" expression (showVal value)
    // The environment stays usable afterwards: these are ordinary Kernel errors.
    assertEval env "(vector-ref (vector 7) 0)" (Obj 7)
