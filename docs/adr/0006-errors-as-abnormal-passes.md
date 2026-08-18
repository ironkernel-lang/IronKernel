# ADR 0006: Errors as abnormal passes

Status: Accepted — phase 1 done, phases 2-4 outstanding

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

**Phase 2 — route through the machinery.** Make `signal` perform the abnormal pass.
With no guards installed, every existing test must still pass unchanged; that suite
is the specification for "invisible to programs that do not use guards".

**Phase 3 — the payoffs.** An exit guard selecting on `error-continuation` fires
when the guarded extent signals. `dynamic-wind` cleans up after a failure. The
report's `$binds?` derivation becomes expressible, and should be added as a test
even though the direct implementation stays.

**Phase 4 — record.** Retire the 7.2.7 divergence, narrow 15.1.3's successor if
ports can now close on error too, and re-validate.

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
