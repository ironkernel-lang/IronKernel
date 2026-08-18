# ADR 0006: Errors as abnormal passes

Status: Accepted — phases 1-3 done, phase 4 outstanding

## Decision

Signalling an error will become an abnormal pass to a continuation in the dynamic
extent of `error-continuation`, as R-1RK 7.2.7 specifies, rather than a value on a
separate channel that unwinds the computation directly. `fail` will take the
continuation it is signalling from, and the pass will run the guard selection and
interception of 7.2.5 on its way out. Reaching `error-continuation` with nothing
intercepting will do what signalling does today, so a program that installs no
guards will behave exactly as it does now.

## Problem

R-1RK 7.2.7 is explicit:

> When an error is signaled during a Kernel computation, the signaling action
> consists of an abnormal pass to some continuation in the dynamic extent of
> error-continuation.

IronKernel signals on a separate channel. `Step` is `Done of ThrowsError<LispVal>
| More | Await`, and `fail e` is `Done (throwError e)`: the trampoline stops and
the error travels out past every continuation between the signalling point and the
driver, consulting none of them. `error-continuation` exists and can be passed to
explicitly, but nothing arrives there by itself.

Three things follow, and all three are recorded as divergences today.

- **Exit guards do not fire on errors.** `guard-dynamic-extent` cannot clean up
  after a failure, which is most of what one wants it for. A `dynamic-wind` built
  on it runs its `after` on a normal return and on an abnormal pass, but not when
  the body signals.
- **The report's `$binds?` derivation does not work here** (6.7.1). It installs an
  exit guard selecting on `error-continuation` and asks whether looking a symbol up
  signals. IronKernel implements `$binds?` by asking the environment directly,
  which is fine, but the report's own derivation is not expressible.
- **`error-continuation` is a continuation nothing passes to.** Its rationale
  (7.2.7) gives two purposes: duplicating the built-in error-signalling action, and
  allowing "an exit-guard that will be selected whenever an error is signaled
  within the guarded dynamic extent". Neither is available.

The last is the real cost. Kernel has no separate exception hierarchy — the
continuation hierarchy *is* the exception mechanism, and 7.1's rationale says so
directly. An implementation whose errors bypass that hierarchy has the machinery
without the mechanism.

## What the continuation machinery already provides

Everything the pass needs exists and is tested, from the work in chapter 7:

- `selectInterceptors` walks the source and destination chains and picks the
  interceptors, exit guards outward and entry guards inward, at most one per list.
- `passAbnormally` schedules the whole interception chain as normal passes, so
  handing the value from one interceptor to the next is not itself intercepted.
- `errorContinuation ()` is a distinguished continuation whose extent is disjoint
  from ordinary computation, because it has no ancestors and is nobody's ancestor.

So this is not new machinery. It is routing an existing signal through it.

## The continuation is in scope where signalling happens

The obstacle looks worse than it is. `fail` has no continuation today, but almost
every caller does.

| | Count |
|---|---:|
| `fail` sites (produce a `Step`) | 199 |
| of those, in `Runtime.fs` | 143 |
| `Runtime.fs` sites with `cont` already in scope | 143 — all of them |
| `throwError` sites in modules that return `ThrowsError`, not `Step` | 44 |
| points where a `ThrowsError` is converted to a `Step` | 23 |

The layering already separates the two. `Arithmetic`, `Interop` and `ClrBindings`
return `ThrowsError<LispVal>` and never see a continuation; their 44 `throwError`
sites do not change. The conversion happens in the primitives, which do have one —
`| Choice1Of2 error -> fail error`, 23 of those — and that is where the pass
begins.

So the migration is: give `fail` a continuation parameter, and let the type
checker find the 199 sites. Most already have `cont` named in the enclosing
function.

## What `fail` becomes

```
let signal cont error = (* abnormal pass of `error` from `cont` to the
                           error continuation, running guards on the way *)
```

Three details decide whether this is right.

**What value is passed.** 7.2.7 says the diagnostic "is not made available to any
Kernel computation", so the error object an interceptor sees need not be the
diagnostic string. The simplest faithful choice is to pass the `LispError` wrapped
as an opaque Kernel value, so an interceptor can pass it on or divert but not read
it. Whether to expose it later is a separate decision, and 7.2.7's "modulo the
format of the value used to describe the error, which this preliminary report does
not specify" leaves it open.

**Where it lands.** "Some continuation in the dynamic extent of
`error-continuation`" — a fresh child of it, so that each signal has its own
destination and the extent test is exact.

**What happens with no guards.** The pass selects nothing, reaches
`error-continuation`, and its native frame returns `Done (Choice1Of2 error)` —
which is what `fail` does today. That is what keeps the change invisible to
programs that do not use guards, and it is the property the migration should be
built around.

## Risks

**Regress.** An error signalled inside an interceptor that is handling an error
would start another pass, from a source inside the first pass's interception chain.
The report does not discuss it. A depth guard that falls back to the direct unwind
is the conservative answer, and the alternative — letting it recurse — should be
rejected explicitly rather than by omission.

**The 7.2.5 divergence interacts.** Applying a continuation directly, `(k 1)`,
bypasses interception; only `apply-continuation` and `continuation->applicative`
go through it. Error passes will go through it, so an error and a direct
continuation application will behave differently in the presence of guards. That is
already true and already recorded, but this change makes the asymmetry easier to
meet.

**Diagnostics could get worse.** Today an error carries its `LocatedError` wrapper
out to the driver, which reports the span. If the pass rewrites the value on the
way, that location has to survive. Nothing about the design requires losing it, but
it is the sort of thing that gets lost.

**Errors during driver setup.** Signalling before there is a meaningful
continuation — during bootstrap, or from a host entry point — has no chain to walk.
Those paths keep the direct unwind.

## Cost

Nothing on the non-error path: `signal` runs only when signalling. On the error
path, one walk of the source and destination chains, which is what every other
abnormal pass already pays.

`CompilerBenchmarks` should therefore be unchanged, and if it is not, the reason
will be that something was added to the ordinary path by accident. That makes it a
good check on the migration rather than a formality.

## Plan

**Phase 1 — a signalling seam.** *Done.* `signal cont error` sits beside `fail` and
ignores its continuation, so nothing changes yet. 200 sites now signal; 8 still
`fail`, and those are exactly the ones with no continuation to signal from -- six
where the continuation *argument* is itself malformed, and the internal error for a
metacontinuation in the wrong position.

> **Corrected in phase 3.** The second sentence was wrong. 47 sites were still
> unmigrated, not 8, and they were not the ones without a continuation: 39 `fail`
> sites in the runtime and 8 `Done(throwError ...)` sites in the compiled and dispatch
> paths, almost all with a continuation in scope. The count of 8 is right only for
> what remains *after* phase 3. See phase 3 below.

The migration was not quite as mechanical as this plan assumed, and the part that
was not is the part phase 2 depends on. `signal` takes the continuation the failing
operation would have returned to, which is the *innermost* one in scope, and eleven
sites sit inside a CPS callback that binds its own -- the guard interceptor, the
port-closing callbacks, the encapsulation and keyed-variable constructors. At those,
the enclosing primitive's `cont` is also in scope, so a blanket rewrite compiles and
is silently wrong. They were found by scanning for callback binders rather than by
the compiler, and are the reason this phase is worth doing before the behaviour
changes rather than during.

Two other things the sweep turned up: four sites had no continuation in scope at all
and one of them, `realArgument`, needed one threaded in from its callers; and a
handful spelled the call `fail(` without a space, so a pattern requiring one missed
them.

**Phase 2 — route through the machinery.** *Done.* `signal` performs the abnormal
pass. The 382 tests passed unchanged, which was the specification for "invisible to
programs that do not use guards"; five new tests in `ErrorPassTests.fs` check the
other half, because a signalling action that quietly went back to unwinding directly
would also leave those 382 passing.

The pass is installed from `Runtime` through a mutable hook, the idiom already used
for `configureSourceServices` and `configureBodyCompiler`, rather than moving the
guard machinery above `Eval`. Less churn for the same result, and the fallback when
unconfigured is the old direct unwind.

Two details the design settled:

- **Regress** was answered by the extent test rather than a depth counter. An error
  signalled from inside `error-continuation`'s extent — which is where an interceptor
  handling an error runs — unwinds directly instead of starting a second pass. That
  is not just a cutoff: once inside the error extent, unwinding is what signalling
  means. A guard whose interceptor always signals now terminates, reporting the
  interceptor's error.
- **Diagnostics** were checked rather than assumed. The destination carries the
  original `LispError` instead of rebuilding one from the value that arrives, and the
  message an unintercepted error reports was compared against master on the same
  inputs: byte-identical. Source spans turn out not to be carried by the error at all
  — the dispatch layer attaches them on the unwind — so they were never at risk.

**What the benchmark caught.** The ADR predicted `CompilerBenchmarks` would be
unchanged and said a change would mean something had been added to the ordinary path.
Something did change: `Interpreted` allocates 2048 B against master's 2024 B. The
prediction's reasoning was wrong rather than its measurement. Instrumenting `signal`
shows it is never called while evaluating `(+ value 1)`, so no work was added to the
ordinary path; the 24 bytes are codegen around the indirection, which appears only
once the hook is actually dispatched through. Three shapes were measured — a curried
function behind an option, an inline delegate, and a non-inline delegate — and all
three allocate the same 24 bytes, so it is the indirection itself and not the calling
convention. The non-inline delegate is the fastest of the three and the one shipped:
411 ns against master's 421 ns, with the compiled paths unchanged. Time improved and
allocation rose 1.2%, on the interpreted path only.

**Phase 3 — the payoffs.** *Done.* `dynamic-wind` cleans up after a failure, and
the report's `$binds?` derivation works. Both are tests; the direct `$binds?`
implementation stays.

Neither worked when the phase began, and the reason is the part of this ADR worth
keeping. **Phases 1 and 2 had missed 47 signalling sites**, so whether an error could
be intercepted depended on which primitive raised it: a guard caught `(car 5)` and
missed an unbound variable.

- **39 `fail` sites in `Eval`, `Runtime` and `Interop`.** Phase 1's note claimed 8
  remained and that they were "exactly the ones with no continuation to signal from".
  That was a miscount. Almost all 39 are the `| Choice1Of2 error -> fail error`
  conversions this ADR had already identified as "where the pass begins" — the
  inventory named them and the migration then skipped them. 8 sites genuinely do stay
  `fail`, and those are the malformed-continuation and internal-error cases.
- **8 sites in the compiled and dispatch paths** — `Compiler.fs`,
  `RuntimeDispatch.fs`, and the source text `StaticCompiler.fs` emits — which called
  `Done(throwError ...)` and so never went through `signal` at all. The site inventory
  in this ADR counted `fail` and `throwError` in the runtime and never considered
  compiled code, which is what a lambda body becomes. This is why the gap showed up as
  "the guard catches an error from `(car 5)` but not from evaluating a symbol": the
  first is a primitive, the second is compiled.

Two of the 47 sit inside CPS callbacks binding their own continuation, and take that
one rather than the enclosing primitive's — the same trap phase 1 documented, which
the compiler cannot catch because both names are in scope.

**On the `$binds?` transcription.** The report's derivation diverts with
`(apply divert #f)`, which passes `#f` as an *atomic* operand tree. IronKernel's
`apply` is the report's derivation verbatim, so that is not where the difference is:
a combination's operand tree is represented as a list, so a non-list tree has no
spelling, and `(divert #f)` delivers `(#f)`. That is the 7.2.5 divergence already on
record. The test has the body return `(list #t)` and takes the car of either path,
which is a transcription difference and not a semantic one — what decides the
predicate is still whether looking the symbol up signals.

**Phase 4 — record.** Retire the 7.2.7 divergence, narrow 15.1.3's successor if
ports can now close on error too, and re-validate. Note that the 7.2.5 divergence
does *not* retire: an atomic operand tree still has no representation, and errors
now go through interception while a direct continuation application still does not.

## Baseline to hold

`CompilerBenchmarks` on master at the time of writing: ColdCompile 149.7 ns /
808 B, Interpreted 419.9 ns / 2024 B, CompiledGeneric 179.4 ns / 808 B,
CompiledFolded 51.0 ns / 304 B. 382 tests pass; the matrix records 135 of 135
entries verified and 44 of 44 modules complete, with twelve divergences.

## Consequences

The change retires a divergence and makes the report's exception mechanism
available: guards that clean up after failures, and error handling written in
Kernel rather than only in the host.

It also makes every error a control-flow event that user code can intercept, which
is a larger claim than "errors are reported". A guard that swallows errors silently
becomes writable, and the diagnostic path becomes something a program can affect.
That is what R-1RK asks for, and it is worth naming as a consequence rather than
discovering it.

The migration is wide but shallow — one signature, 199 mechanical call sites, and
one function that changes behaviour. The risk is concentrated almost entirely in
phase 2, which is the argument for landing phase 1 separately and keeping phase 2
small enough to read in one sitting.
