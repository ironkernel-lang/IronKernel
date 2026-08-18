# ADR 0008: Caching compiled bodies

Status: Proposed — not to be built yet

## Decision

Do not add the cache now. Measured, it is worth 0.6% to 2.2% of wall clock, and
taking it would first require making body compilation closure-independent, which is
the larger and more interesting half. Record the measurement so the question is not
re-derived from the compilation counts, which overstate it badly.

## Problem

ADR 0004 phase 3 compiles an operative's body on first application and memoises it on
the `OperativeRecord`. A combiner built and applied once therefore compiles a body it
will use once. ADR 0007 removed the two largest sources of those by making
`$sequence` and `let` primitive, and closed by naming this as the general fix.

The counts make it look compelling. One run of `constant-width-amb`:

| | compilations | distinct bodies | time in compilation |
|---|---:|---:|---:|
| before ADR 0007's `let` change | 339,599 | 21,055 | 415 ms |
| now | 47,260 | **136** | **57 ms** |

47,260 compilations of 136 distinct bodies is 347x redundant. A cache keyed on the
body would collapse it to 136.

## Why the counts overstate it

57 ms against a 4.53 s run is **1.2%**. Across three programs the compile share is
0.6% (`zipper`), 1.2% (`constant-width-amb`) and 2.2% (`constant-width`).

This also corrects the account given when `let` was made primitive. That change was
explained by the recompilation it removed, and the recompilation is real -- 339,599
compilations down to 47,260 -- but compilation time only fell from 415 ms to 57 ms.
That is 358 ms of a 6,680 ms improvement, about **5%**. The other 95% was the
operative construction, the `map`/`car`/`cadr`/`cons` traffic and the `eval` that the
derivation performed per call. The compilation count was the visible symptom, not the
cost.

## What is actually shared

A cache needs a key. Repeated evaluation of the same source form gives:

| | shared across evaluations? |
|---|---|
| `OperativeRecord` | no -- fresh per evaluation, which is why the memo misses |
| the body as an F# list object | **no** -- rebuilt per evaluation |
| the first body form, and its `PairCell` | **yes** |
| the closure environment | no, inside a procedure |

So the key is the body's cell, not the list that holds it. `acquireImmutableForms`
returns its argument unchanged when the forms are already immutable, and the reader
produces immutable pairs, so a body that came from source is the same object every
time.

That last qualification is the important one, and it is why this cache would not have
substituted for ADR 0007's work. The old `let` *synthesised* its body at run time with
`list*` and `cons`, so those bodies were fresh cells: 21,055 distinct bodies behind
339,599 compilations. A body-identity cache would have missed on most of them.
Bodies from source cache well; bodies a derivation builds do not cache at all.

## Why it is not just a dictionary

`compileLispValGuarded closure form` consults the closure while analysing, in two
ways.

**Guard creation.** `tryCreateBindingGuard env name identity` emits a guarded
specialization only if the name currently resolves to the expected primitive. Reusing
a compilation made against a different closure is *safe* here -- but only because of
what the guard checks at run time, and the two compiled paths do not agree on that:

- `RuntimeDispatch.runGuard` re-resolves the name in the invoking environment and
  compares identity. Closure-independent.
- `Compiler.fs`'s `CGuarded` uses `bindingGuardMatches`, which additionally requires
  `cell.id` and `state.version` to equal what was seen at compile time. Closure-
  *dependent*.

A shared body would fail the second check in every closure except the one it was
compiled against, fall back to the interpreted path, and so keep the compilation while
losing the specialization -- much of the point. The stricter check also appears to be
stricter than necessary: the identity comparison already establishes that the binding
holds the expected primitive, which is what the specialization needs.

**CLR sugar.** The analyzer asks `getVar' env name` and, when the name is unbound,
tries a CLR rewrite instead. Two closures can disagree about that, and this one is
unsound to reuse rather than merely slow, because the compiled form calls something
different. It is narrow -- it needs a name that is both rewritable as CLR sugar and
bound in some other closure -- but it is the one difference in kind.

**Shared mutable call-site caches.** A compiled body carries `NamedCallSite` objects
with a one-entry inline cache. Sharing a body shares those across environments, so
alternating closures would invalidate and refill rather than hit. The effect is
unmeasured, and it works against the gain rather than with it.

## What would have to happen first

Make compilation closure-independent, then the key is just the body cell:

1. Align the compiled `CGuarded` with `runGuard`'s name-and-identity check, removing
   the `cellId`/`version` pinning. This is worth doing on its own terms -- it is the
   same conceptual guard implemented two ways, and the strict version also fails after
   a rebind-and-restore that the permissive one survives.
2. Decide the CLR-sugar question at run time rather than at analysis time, or record
   the dependency in the key.
3. Only then add the cache, keyed on the first body form's `PairCell`, with the
   call-site sharing measured rather than assumed.

Step 1 is a small change with its own justification. Step 2 is the real work.

## Alternatives

**Cache on the source form instead of the body.** Same problem: the decision is not
where the key lives but whether the compiled result depends on the closure.

**Memoise per closure.** Sound without any of the above, and useless: the closure is
fresh per call, which is the whole reason the existing memo misses.

**Do nothing.** What this ADR recommends. The remaining 47,260 compilations are 1.2%
of a run, and the two derivations that generated most of them are already gone.

## Consequences

The question stays open with a number attached, so it can be re-opened by evidence
rather than by the compilation counter, which is the thing that made it look large.
If a workload appears where compilation is a materially larger share -- short runs
with many distinct source bodies would be the shape -- the plan above is the route.

Step 1 should probably happen regardless of whether the cache is ever built.
