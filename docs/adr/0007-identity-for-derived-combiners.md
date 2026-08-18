# ADR 0007: Identity for derived combiners

Status: Accepted — sequencing and `let` implemented

## Decision

Do not build it. ADR 0004 phase 5 ended by naming identity for derived combiners as
the lever its own mechanism could not reach; measuring that lever shows it is worth
about 1% of dispatches beyond what a much smaller change already gets. Instead,
promote the hot standard-library operatives to primitives and lower them through the
`PrimitiveIdentity` guard that already exists, starting with `$sequence`.

## Problem

`PrimitiveIdentity` is a field on `PrimitiveOperativeRecord`. A compound operative --
anything `kernel.ikr` builds with `vau` -- cannot carry one, so `analyzeGuarded`
cannot recognise it and every call goes through generic `COperate` dispatch. Phase 5
measured that guards are 11.7% faster on a fresh frame where they apply, and found
that the operators with structure worth lowering are all derived and therefore out of
reach.

The obvious repair is to give derived combiners an identity too: stamp the standard
library's combiners at bootstrap, generalise `BindingGuard.expectedIdentity` to cover
them, and lower `(let ...)`, `(sequence ...)` and friends the way `if` is lowered
today.

Before building that, it is worth asking what it would buy.

## What the dispatches actually are

Phase 5's census counted *static* occurrences in compiled bodies and ranked `letrec`
first among derived operatives. That ranking is an artifact of counting source sites.
Instrumenting the compiled dispatch path (`NamedCallSite.Invoke`) and running eight
example programs -- 9.0M dispatches in total, from 2.5k to 8.2M per program -- gives
the frequency instead:

| Combiner kind | Share of dispatches |
|---|---:|
| primitive applicative | 78.4% |
| derived applicative | 12.3% |
| **derived operative** | **7.2%** |
| other applicative | 2.0% |
| primitive operative | 0.0% |

The derived-operative share is the ceiling on what this ADR's mechanism could ever
address, and it is remarkably stable: 6.8% to 7.6% across all eight programs.

Inside that 7.2% slice:

| | Share of slice | Share of all dispatches |
|---|---:|---:|
| `seq2` | 46.3% | 3.4% |
| `sequence` | 37.9% | 2.7% |
| `let` | 14.1% | 1.0% |
| `letrec` | 1.3% | 0.09% |
| `cond`, `let*`, rest | 0.4% | 0.03% |

So 84% of the target is one feature, sequencing. `letrec`, which the static census
ranked first, is 0.09% of dispatches -- three orders of magnitude below where
counting source sites placed it. Anyone sizing this work from the static census would
have built the general mechanism to speed up the wrong thing.

## Sequencing costs more than its own dispatches

`$sequence` is the report's derivation (5.1.1): `seq2` plus an `aux` operative that
evaluates the head and recurses on `(eval (cons aux tail) env)`. Each element
therefore costs roughly a `null?`, two `eval`s and a `cons` on top of the dispatch
itself -- and those are the top of the overall table:

| Site | Share of all dispatches |
|---|---:|
| `null?` | 26.0% |
| `eval` | 18.7% |
| `cons` | 9.4% |
| `zero?` | 8.9% |
| `car` | 7.9% |

This is an inference, not an attribution: the census keys on the dispatched name and
does not record the caller, so it cannot say how much of that `eval` traffic is
sequencing. Two things make the inference worth acting on anyway. The arithmetic is
the right order -- 549k sequencing dispatches against 1.68M `eval` and 845k `cons` --
and the census *undercounts* sequencing, because `aux` recurses through
`(cons aux tail)`, a computed operator that never reaches the name-keyed call site at
all. Lowering `$sequence` removes the generated traffic, not just the 6.1%.

## Why the general mechanism is the wrong shape

The case for identity on derived combiners is that it generalises. It does not.

A guard only pays if the compiler knows what to lower the combiner *into*. `CIf`
wins by compiling the branches; `CSeq` would win by compiling the elements. That
knowledge is hardcoded per feature, so the mechanism can only ever recognise
combiners the compiler already understands -- which is the standard library, and
nothing else. It does not extend to user-defined combiners: speeding those up means
inlining an arbitrary vau body, with the hygiene and dynamic-environment questions
that entails, and that is a different technique that would not use this machinery.

So the general mechanism's reach is exactly the set of combiners we could instead
make primitive. Both routes end at the same lowered `CSeq`; one adds an identity
scheme for compound operatives, a bootstrap stamping pass and a wider
`BindingGuard`, and the other adds a primitive and one `PrimitiveIdentity` case.

The report settles whether making them primitive is allowed. R-1RK 1.3.2:

> The derivation code is not considered part of the definition of the feature, so
> implementations are not expected to duplicate the exact behavior of the code.

Library features may be implemented primitively. Conformance is unaffected, and the
matrix records module completeness rather than how a feature was built.

## What to do instead

**Promote `$sequence` to a primitive operative** with a `PrimitiveSequence` identity,
and lower `(sequence . forms)` to `CSeq` in `analyzeGuarded` under the existing
binding guard, with the current `COperate` path as the fallback.

`CSeq` already exists in `Ir.fs` and `compileToFunc` already compiles it -- it is
produced today only by the package decoder and the partial evaluator, never by the
analyzer. So the compiler side is a lowering rule, not a new node.

`let` is the only other candidate above 1%, and it is a further decision to take on
its own evidence once sequencing is done, because removing the sequencing traffic
changes the profile everything else is measured against.

## Outcome

Implemented for `$sequence`. The gain is much larger than the 6.1% dispatch share,
which is what the inference above predicted: the derivation's cost was mostly the
`eval`/`cons`/`null?` traffic it generated per element, not its own dispatches.

| | master | primitive |
|---|---:|---:|
| `constant-width-amb.ikr`, median of 3 | 16.19 s | **11.56 s (-28.6%)** |
| `LambdaLiteralCall` | 32,881 ns / 135.1 KB | **20,804 ns / 87.2 KB (-37% / -35%)** |
| `NamedLambdaCall` | 744.7 ns | 739.2 ns |
| `EffectHandlerResume` | 2695.4 ns | 2659.7 ns |

`LambdaLiteralCall` builds and applies a combiner once, which is what every `let`
expands to, so it is the most sequence-dense benchmark in the set; the rest are flat
to 2% better. `CompilerBenchmarks` is unchanged (146.9 / 426.7 / 183.1 / 52.2 ns),
which is the check that nothing was added to the ordinary path.

The three risks named above were all real work rather than formalities. The tail
context needed the structural test, and that test was checked against a negative
control: moving the recursion out of tail position takes the captured continuation's
depth from 23 to 2003, so it discriminates. The derivation is kept in
`StdlibTests` and checked against the primitive, so it cannot rot silently. And
`sequence` being load-bearing is why the suite and the twelve examples are the real
evidence here -- 398 tests, and every example unchanged.

The `let` question is now open on its own terms, and the profile it should be
measured against is this one, not the one in this ADR.

## Outcome, `let`

Re-censused against the post-sequencing profile first, as that paragraph asked.
Total dispatches over the same eight programs fell from 9.0M to 5.69M, `eval` fell
70% -- confirming sequencing generated most of it -- and derived operatives fell from
7.2% to 1.8% of a smaller total, with `let` now 89.8% of that slice.

One prediction in this ADR was wrong and is worth recording. It attributed `cons`
traffic to sequencing along with `eval`; `cons` is 844,535 both before and after,
unchanged. The `eval` half of the inference held, the `cons` half did not.

`let` at 1.62% of dispatches did not look worth much. The dispatch count was the
wrong measure, and the reason is specific: the derivation builds
`((lambda (formals) . body) . expressions)`, so every `let` constructs a fresh
operative -- and a fresh operative's `compiledBody` is `None`, so ADR 0004 phase 3's
memo never hits and the body is compiled again for the single application it will
ever receive. Counting those directly:

| | before | after |
|---|---:|---:|
| body compilations, `constant-width-amb` | 339,599 | **47,260 (-86%)** |
| wall clock, median of 3 | 11.56 s | **4.88 s (-58%)** |

Against master before either change, that example is 16.19 s to 4.88 s, a 70%
reduction. `ControlFlowBenchmarks` and `CompilerBenchmarks` are unchanged, which is
expected -- neither exercises `let` in a hot path, so the gain shows up in programs
rather than microbenchmarks.

`let` binds through `bindArgsStep`, the same code an operative's formals use, so a
definiend tree destructures identically; the body runs through `sequenceForms`, which
keeps the tail context it used to inherit from the lambda. Both have tests, and the
tail-context test was validated against a negative control the same way sequencing's
was: 23 against 2003.

**The residual is larger than either change.** 47,260 body compilations remain in one
run, and `let` accounted for only 90,583 of the original 339,599 dispatches' worth.
The rest come from other operatives built and applied once -- a `lambda` literal
inside a loop is the obvious case. The general fix is to memoise compilation across
operatives sharing a body, since the body `LispVal` is the same object every time the
same source form is evaluated. That is not free: `compileLispValGuarded` takes the
closure environment, and analysis-time decisions such as CLR-call sugar depend on what
is bound there, so a cache keyed on body identity alone is unsound. It needs its own
ADR.

## Risks

**Sequencing is load-bearing.** Every operative body is a sequence, so a wrong
primitive breaks everything at once. That is also the mitigation: the 394-test suite
and the twelve examples exercise it on every path, and a mistake cannot hide.

**Tail position.** 5.1.1 requires the last element to be evaluated as a tail context.
The derivation gets this from `aux`'s structure; a primitive and a `CSeq` lowering
each have to preserve it deliberately. ADR 0004 phase 2 already found that the
equivalent property is invisible to a test that only checks results, and has to be
measured structurally -- capture a continuation at the deepest point and assert its
`nextCont` depth stays bounded. The same test shape applies here.

**The derivation stops being exercised.** `kernel.ikr`'s version is presently
executed by everything; as a fallback it would be executed by almost nothing, so it
can rot unnoticed. It should keep a test that drives it directly.

**The profile is one corpus.** Eight example programs are not a workload survey, and
they lean on the standard library more than user code would. The 7.2% ceiling is the
number to distrust first if the result disappoints.

## Cost

One primitive, one `PrimitiveIdentity` case, one lowering rule, and the tests above.
No new mechanism. Against that, the rejected design needs identity on
`OperativeRecord`, a bootstrap pass to stamp the standard library, a generalised
`BindingGuard`, and a decision about what happens when a program redefines a stamped
name -- for at most one point of additional reach.

## Consequences

`$sequence` moves from derived to primitive. The report permits it, but it is a real
change in character: IronKernel has preferred to derive what the report derives, and
this is the first place where measurement argues the other way. It is worth being
explicit that the reason is evidence rather than convenience, and that the derivation
stays in the tree as the fallback and as documentation of the semantics.

If sequencing is lowered and the gain does not appear, the conclusion is not "now
build the general mechanism". It is that dispatch is not where the time goes, and the
remaining 78.4% -- primitive applicative calls in hot loops -- is the thing to profile
next.
