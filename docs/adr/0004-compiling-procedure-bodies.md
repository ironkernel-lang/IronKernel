# ADR 0004: Compiling procedure bodies

Status: Implemented

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

**Phase 4 — compile operand trees. Attempted and rejected.** Operands were
compiled and dispatched once the call site resolved to an applicative, preserving
the operative distinction. It was correct but 2.4x *slower* on the body-heavy
workload, 55s against 23s, and the cost scaled with iteration count rather than
being one-time compilation.

Instrumenting the call-site cache during that run explains why, and invalidates
the premise of phases 3 and 4 together: **0 hits against 150,393 misses**.
`NamedCallSite.cacheValid` requires `obj.ReferenceEquals(env, resolved.Env)`, and
every procedure call binds its parameters in a fresh frame, so a call site
evaluated inside a procedure body never sees the same environment twice. Each
compiled operand therefore pays full `resolveBindingCellWithPath`, a
`ResolvedCallSite` allocation, and a volatile publish, where the interpreter pays
one `getVar'`. Compiling more of the body simply buys more cache misses.

This is the same effect measured earlier by `GuardSpecializationBenchmarks`, where
guards only paid off against a fresh frame per call, and it is why phase 3 returned
1.3% rather than the projected multiple.

One further trap found here: operands must not be partially evaluated. Constant
folding an operand raises errors from expressions that may never be evaluated, and
`(and? #f (/ 1 0))` must short-circuit.

**Phase 4 (revised) — implemented.** Three changes, each measured separately.

*Call-site validation across fresh frames.* `NamedCallSite` now validates that
resolving the name from the invoking environment still reaches the same frame --
every nearer frame still lacks the name, and the owning frame is the same object --
rather than requiring the environment to be the same instance. Hit rate inside a
procedure body went from 0% to 67%. Chains that are not a simple single-parent walk
are dispatched without caching rather than cached and never revalidated.

*Lowering guarded `if` and `define` into Core.* `analyzeGuarded` produced
`CIntrinsicOperate`, which hands the runtime primitive raw syntax that it then
evaluates through the interpreter. Every conditional and every definition inside a
compiled body was therefore interpreted. The located analyzer had always lowered
them to `CIf` and `CDefine`; the ordinary path now agrees.

*Plain closures instead of expression trees.* `Expression.Lambda(...).Compile()`
costs tens of microseconds per node. That was affordable when only top-level forms
were compiled once, but phase 3 compiles a body per operative, and a combiner built
and applied once -- every `let` expands to one -- has nothing to amortise it
against. Lowering `if` while still emitting expression trees made
`LambdaLiteralCall` 4.5x slower; replacing them with closures removed that and left
every benchmark at or better than master.

Compiling operand trees stays rejected. Retried on top of the fixed cache it was
still 2.4x slower, so the cost is in the dispatch path rather than in cache misses,
and it needs profiling rather than another attempt.

## Results

Against master as it stood when phases 1-4 landed, with 237 tests passing at that
time and diagnostics byte-identical:

| Measurement | master | now |
|---|---|---|
| Body-heavy workload | 23.0 s | 20.5 s (-11%) |
| `NamedLambdaCall` | 905 ns | 695 ns (-23%) |
| `NamedVauCall` | 902 ns | 680 ns (-25%) |
| `DirectEffectHandler` | 1040 ns | 799 ns (-23%) |
| `EffectHandlerAbort` | 2021 ns | 1774 ns (-12%) |
| `LambdaLiteralCall` | 29.7 us | 28.9 us (-3%) |

Allocation on a named call falls 22%. Continuation-heavy paths are within 1-2% of
master. Phase 1's cost on `CompiledGeneric` and `CompiledFolded` remains: those
measure a single top-level form, where the extra continuation threading is not
offset by anything a body would gain.

**Phase 5 — revisit analyzer specialization.** *Measured. The answer is no: do not
extend `PrimitiveIdentity`.*

The premise held. `GuardSpecializationBenchmarks`, on an idle machine, has the
guarded path ahead in both cases -- and the 12% figure that motivated this phase
reproduces exactly:

| | Mean | vs its unguarded pair | Allocated |
|---|---:|---:|---:|
| `Unguarded` | 190.9 ns | | 984 B |
| `Guarded` | 159.0 ns | -16.7% | 800 B (-19%) |
| `UnguardedFreshEnv` | 219.1 ns | | 1232 B |
| `GuardedFreshEnv` | 193.4 ns | -11.7% | 1048 B (-15%) |

So the earlier claim that guards were a pessimization is doubly dead: the reasoning
behind it was void once phase 4 replaced the reference-equality cache, and the
measurement now disagrees with it too.

What kills the extension is not the mechanism's speed but its reach. A census of the
Core nodes the analyzer produces *inside compiled bodies* -- what phase 3 compiles
per operative -- over two corpora:

| | kernel.ikr (409 nodes) | examples (232 nodes) |
|---|---:|---:|
| `COperate` (generic dispatch) | 51.1% | 62.1% |
| `CGuarded` (the specialized path) | 16.4% | 12.5% |

Half to two-thirds of a compiled body is generic dispatch, and the operators
reaching it divide into two groups, neither of which `PrimitiveIdentity` can help:

- **Ordinary applicative calls** -- `null?` (32 sites in kernel.ikr), `car`, `cons`,
  `zero?`, `<`, `vector-set!`, and user procedures. There is nothing to lower. `CIf`
  wins because it compiles its branches instead of leaving them as raw operands; an
  applicative call has no branches, and `COperate` already reaches the call-site
  cache.
- **Derived control operatives** -- `letrec` (20), `let` (11), `begin` (11), `cond`,
  `sequence`. These are the ones with structure worth lowering, and they are defined
  in `kernel.ikr` as vaus. `PrimitiveIdentity` is a field on
  `PrimitiveOperativeRecord`, so it cannot tag them at all. That is structural, not a
  matter of which cases someone bothered to add.

The only primitive candidate with a Core node already waiting for it is `eval` ->
`CEval` (19 sites in kernel.ikr, 5 in the examples). Worth noting while here:
`CEval`, `CSeq`, `CVau` and `CReset` exist in the IR but the analyzer never emits any
of them -- they are produced only by the package decoder and the partial evaluator.
The specialization machinery is narrower in practice than the node set suggests.

*Limitation.* The census counts static occurrences, not execution frequency, so it
says what a body is made of rather than where its time goes. The structural
conclusion does not depend on the weighting: a derived combiner is unreachable by
this mechanism however hot it is. Execution frequency would only change how much is
on the table for a *different* mechanism.

*If the lever is wanted*, it is identity for derived combiners -- a way to guard on
"this binding is still the standard library's `let`" -- which is a different design
from `PrimitiveIdentity` and should get its own ADR rather than being grown into
this one.

## Baseline

Taken on an idle machine alongside phase 5's measurement, as the reference for any
later work. `ControlFlowBenchmarks`: `NamedLambdaCall` 744.7 ns / 3.6 KB,
`NamedVauCall` 736.9 ns / 3.6 KB, `CallCcEscape` 795.1 ns, `ShiftResetResume`
1220.0 ns, `DirectEffectHandler` 856.5 ns, `EffectHandlerAbort` 1970.7 ns,
`EffectHandlerResume` 2695.4 ns, `LambdaLiteralCall` 32.9 us.
`CompilerBenchmarks`: ColdCompile 147.3 ns / 808 B, Interpreted 432.4 ns / 2048 B,
CompiledGeneric 185.0 ns / 808 B, CompiledFolded 54.1 ns / 304 B.

Worth stating because it cost time twice: these numbers move by half again if
anything else on the machine is busy, and stray processes left by an earlier run are
the likeliest cause. Ratios and allocation stay put when that happens, which is how
to tell it from a real regression -- a uniform slowdown with byte-identical
allocation is the machine, not the code.

## Consequences

Phases 1 and 2 change no observable behaviour and land independently; the
performance benefit arrives only with Phase 3. Phase 1 is a measured cost until
then: threading continuations where nested trampolines previously ran tight inner
loops costs about 7% on `CompiledGeneric` and 15% on `CompiledFolded`, at 10-27%
more allocation. If phases 2 and 3 do not land, phase 1 should be reverted rather
than left in place.

Phase 1 also constrains how a located span may be applied. An unintercepted error
reaches the driver as `Done` without passing through the continuations between, so
`runLocated` has to inspect the step chain. Under CPS that chain also covers
everything that runs after the form, so a span applied naively reaches past its own
form and an operator's span swallows errors raised by the operands evaluated after
it. Interpreting bounded each sub-evaluation with a fresh continuation; the compiled
path has to restore that boundary explicitly by recording when control passes out of
the form.

> ADR 0006 has since made signalling an abnormal pass, so an error now runs the
> guard machinery on its way out. That does not change this: with no guard
> installed the pass reaches a destination that returns `Done`, which is what
> `runLocated` sees.

The paragraph that used to close this section argued that adding `PrimitiveIdentity`
cases was a pessimization because the call-site cache "validates by environment
reference equality and always hits when the environment is stable, which is the only
situation compiled code encounters today". Phase 4 measured the opposite -- 0 hits
against 150,393 misses, because every call binds a fresh frame -- and replaced that
validation with the path check. The argument is void, and what replaces it is phase
5: re-measure rather than reason from the old cache's behaviour.

Continuation-heavy behaviour is the primary regression risk, and it is exercised
by examples rather than by unit tests. `Examples/coroutines.ikr` is now executed
in CI rather than merely packaged; the remaining continuation examples should
gain equivalent coverage before Phase 2 begins.

Compiled bodies are immutable lists of compiled forms, so re-entry through a
multi-shot continuation stays safe. Debuggability changes: body frames will
report through compiled delegates, and located spans must be preserved through
`CLocated` for diagnostics to survive.
