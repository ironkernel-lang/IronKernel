# ADR 0004: Compiling procedure bodies

Status: Proposed

## Decision

Compiled code will return `Step` rather than a collapsed `ThrowsError<LispVal>`,
and operative bodies will be compiled lazily and carried in the continuation
representation as a list of compiled forms. Until compiled functions participate
in the caller's trampoline, procedure bodies must stay interpreted, and further
analyzer specialization must not be added.

## Problem

Only top-level forms are compiled today, through `evalCompiled` and
`compileFormsGuarded`. Operative application binds a fresh frame and evaluates
the body as `KernelCode`, a list of raw `LispVal` forms driven form by form by
`evalStep`. The `CompiledCombiner` case in `Ast.fs` is matched in three places
but is never constructed anywhere. Because `define` evaluates its right-hand side
through `bounceEval`, `(define f (vau ...))` never reaches the analyzer's
specializations either. Effectively all real work runs interpreted.

The measured gap is large. On an identical form, `CompilerBenchmarks` reports
interpreted evaluation at 369.9 ns and 1832 B, generic compiled evaluation at
160.2 ns and 712 B, and constant-folded compiled evaluation at 93.5 ns and 240 B
— 2.3x to 4.0x faster with 2.6x to 7.6x less allocation. Compiling a form costs
86.2 ns, less than a single interpreted evaluation, so compilation pays for
itself within roughly one call.

## Why bodies cannot be compiled today

`KernelFunc` is `Func<LispVal, LispVal, ThrowsError<LispVal>>`. It returns a
finished value, not a trampoline step. Every compiled leaf bottoms out in `eval`,
`continueEval`, `operate`, or `bind`, and each of those calls `run`. Each
compiled form is therefore a nested trampoline. For one-shot top-level forms this
is harmless. For procedure bodies it breaks three guarantees:

- **Proper tail calls.** A tail-recursive procedure one million calls deep runs in
  constant stack today. Each nested `run` is a loop entered from inside another
  loop's thunk, so compiling bodies against collapsing functions would turn each
  Kernel tail call into CLR stack growth. Note this is specific to *nested
  trampolines*. Once compiled code returns `Step` there is a second, independent
  tail-call obligation that costs heap rather than stack; see phase 2.
- **First-class continuations.** `run` collapses `Step` into a value, so a
  continuation captured inside a compiled body cannot escape past that boundary
  or be resumed back into the middle of the body.
- **Asynchrony.** `run` ends in `GetAwaiter().GetResult()`. An `Await` raised
  inside a compiled body would block a thread instead of suspending.

## Plan

**Phase 1 — return `Step` from compiled code.** Change `KernelFunc` and
`GeneratedFunc` to `Func<LispVal, LispVal, Step>` and replace collapsing calls
with the `bounceEval`, `bounceContinue`, `bounceOperate`, and `bounceBind`
variants that already exist for exactly this purpose. A single `run` remains at
the top-level entry points. This touches roughly twenty call sites in
`Compiler.fs` and `RuntimeDispatch.fs`, the seven emitted helpers used by
generated artifacts, and the `StaticEmit` source strings. The change is wide but
mechanical, and the type checker locates every site. It alters no observable
behaviour and is validated by the existing suite plus deep tail recursion.

**Phase 2 — represent compiled bodies in continuations.** Add
`CompiledCode` beside `KernelCode` in `DeferredCode`, holding the body as a list
of compiled forms. It is typed as a plain function rather than the compiler's
`KernelFunc` so `IronKernel.Runtime` stays free of a compiler dependency. Mirror
the existing stepping in `continueEvalValidStep`: evaluate the head form, retain
the remaining forms in `currentCont`, and let the final form inherit `nextCont`.
Keeping the body a list rather than one opaque delegate is what preserves proper
tail calls structurally, exactly as the interpreter does. `appendContinuationRecord`
and `findPrompt` manipulate only the `nextCont` chain and never inspect the payload
of `currentCont`, so continuation splicing, `call/cc`, `shift`/`reset`, and
`prompt`/`perform`/`resume` require no changes.

Operative application detects a tail call by observing that the caller's body is
exhausted, and matches `KernelCode []` to do it. A compiled caller reports an
exhausted body as `CompiledCode []`, so that case must be added or a frame is
retained on every tail call out of compiled code.

This second tail-call obligation costs heap, not stack, and the distinction
matters for how it is tested. Once compiled code returns `Step`, the trampoline
keeps the CLR stack flat whether or not the tail call is recognised, and the
program still computes the right answer; what grows is the retained continuation
chain. A test that merely runs many iterations and checks the result therefore
passes either way. The property is only visible structurally: capture a
continuation at the deepest point of a self-recursive compiled body and measure
its `nextCont` depth, which stays bounded when the tail call is recognised and
grows with the iteration count when it is not.

**Phase 3 — compile bodies lazily.** Give `OperativeRecord` a mutable memo and
compile on first application with `analyzeFormsGuarded` against the closure
environment. Because compilation costs less than one interpreted evaluation, no
tiering or hotness heuristic is warranted. Invalidation already works: binding
guards key on cell version, and the named call-site cache validates frame binding
counts, so a body that defines locally invalidates correctly.

`IronKernel.Runtime` cannot reference the compiler, since ADR 0002 requires
managed artifacts to exclude the compiler and FParsec. The body compiler is
therefore injected the way `RuntimeSourceServices` already injects the parser.
Artifacts that do not install it fall back to interpretation.

**Phase 3 outcome.** Bodies are compiled and memoised as designed, but the gain
is about 1.3% on a body-heavy workload, not the 2.3x-4.0x projected above. The
projection came from `CompilerBenchmarks` measuring a single flat form, which is
not representative of a procedure body.

The reason is structural: the compiler never descends into operand position. Every
combination case in `compileToFunc` converts its operands back to raw `LispVal`
and hands them to the runtime, because `COperate` deliberately retains operand
syntax so combiner dispatch can tell operatives from applicatives. Compiling a
body therefore compiles only the shell of each form; all nested evaluation stays
interpreted, and nested evaluation is where the time goes.

Across `ControlFlowBenchmarks`, repeated named procedure calls are 15-16% faster
with 17% less allocation, and continuation-heavy paths are 4-6% slower. That does
not repay phase 1's cost, so the premise that phase 3 pays for phase 1 does not
hold as stated.

**Phase 4 — compile operand trees.** The remaining lever is teaching the compiler
to descend into operands while preserving Kernel's operative/applicative
distinction: operands may only be pre-compiled once the combiner in operator
position is known to be applicative, which the binding guards and call-site cache
already establish. This is a larger change than phases 1-3 and should be measured
against the same body-heavy workload before being adopted.

**Phase 5 — revisit analyzer specialization.** Re-measure with
`GuardSpecializationBenchmarks`. Fresh-frame invocation becomes the common case
once bodies are compiled, and guards measured 12% faster there, so extending
`PrimitiveIdentity` should be reconsidered then, with evidence.

## Consequences

Phases 1 and 2 change no observable behaviour and land independently; the
performance benefit arrives only with Phase 3. Phase 1 is a measured cost until
then: threading continuations where nested trampolines previously ran tight inner
loops costs about 7% on `CompiledGeneric` and 15% on `CompiledFolded`, at 10-27%
more allocation. If phases 2 and 3 do not land, phase 1 should be reverted rather
than left in place.

Phase 1 also constrains how a located span may be applied. Errors short-circuit
the trampoline as `Done` and bypass continuations, so `runLocated` has to inspect
the step chain. Under CPS that chain also covers everything that runs after the
form, so a span applied naively reaches past its own form and an operator's span
swallows errors raised by the operands evaluated after it. Interpreting bounded
each sub-evaluation with a fresh continuation; the compiled path has to restore
that boundary explicitly by recording when control passes out of the form. Until then, adding
`PrimitiveIdentity` cases is a measured pessimization rather than an
optimization: guards re-resolve the binding by name on every invocation, whereas
the `COperate` fallback's call-site cache validates by environment reference
equality and always hits when the environment is stable, which is the only
situation compiled code encounters today.

Continuation-heavy behaviour is the primary regression risk, and it is exercised
by examples rather than by unit tests. `Examples/coroutines.ikr` is now executed
in CI rather than merely packaged; the remaining continuation examples should
gain equivalent coverage before Phase 2 begins.

Compiled bodies are immutable lists of compiled forms, so re-entry through a
multi-shot continuation stays safe. Debuggability changes: body frames will
report through compiled delegates, and located spans must be preserved through
`CLocated` for diagnostics to survive.
