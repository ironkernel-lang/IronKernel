# ADR 0005: Mutable pairs

Status: Accepted — phases 0-2 done, phases 3-6 outstanding

## Decision

Pairs will become mutable cons cells, replacing `List of LispVal list` and
`DottedList of (LispVal list * LispVal)` with a single `Pair` case over a cell
holding a mutable car, a mutable cdr, and an immutability flag. The change will
land in phases, and the phase that introduces the cell will keep `List` and
`DottedList` as active patterns so that the match sites compile unchanged, while
construction moves to differently named helpers. `eq?` will become object
identity, and `equal?`, `showVal` and `get-list-metrics` will become cycle-safe.

Until that happens, module Pair mutation stays half implemented: `copy-es`,
`copy-es-immutable`, `assq` and `memq?` are supported; `set-car!`, `set-cdr!`,
`encycle!` and `append!` are absent. That is the state recorded in the matrix
under the 4.7 divergence.

## Problem

R-1RK 4.7.1 requires `set-car!` and `set-cdr!` to write into a pair that other
references can observe. IronKernel has no such pair. A list is an F# immutable
list, so two references to "the same" list share structure only by accident of
implementation, and there is no cell to assign to. Every remaining entry of module
Pair mutation follows from that one gap: `encycle!` (5.8.1) and `append!` (6.4.1)
mutate, and `copy-es`'s guarantee that its result is *not* `eq?` to its argument
(6.4.2) is meaningless while `eq?` compares structurally.

The gap is not confined to those entries. Two required entries are implemented on
the assumption it holds:

- `equal?` (4.3.1, 6.6.1) is an explicit work-stack walk in `eqvValue`
  (`Runtime.fs`). It terminates because structure is finite. Once `encycle!` can
  build a cycle it must terminate anyway, which the report requires.
- `get-list-metrics` (5.7.1) reports `(pairs nils pairs 0)` computed with
  `List.length`, i.e. it answers "acyclic, of this length" unconditionally. It is
  the primitive the whole list library in `kernel.ikr` is derived from, and those
  derivations carry comments saying cycles cannot arise.

## Scale

`List` and `DottedList` are matched or constructed 121 times across 19 of the
project's source files, and most of that is concentrated:

| File | Sites |
|---|---:|
| `IronKernel.Runtime/Runtime.fs` | 45 |
| `IronKernel.Runtime/Eval.fs` | 22 |
| `IronKernel/Analyze.fs` | 20 |
| remaining 16 files | 34 |

Three files hold 87 of the 121. That is better than it first appears: a naive
count of the two names reaches 315, but 194 of those are `List.map`,
`List.length` and the rest of the F# `List` module, which have nothing to do with
the union case. The distinction matters for more than sizing — see below.

This is still the core data type of the language, so a change to it is not local
to a feature, and the traversals that depend on structure being finite are spread
more widely than the constructors are.

## Why one representation, not two

The obvious way to contain the blast radius is to keep `List`/`DottedList` for
immutable structure and add a mutable `Pair` beside it, converting where needed.
That does not work. `(set-car! (list 1 2) 0)` has to mutate what `list` returned,
so `list` must produce mutable pairs; and `cons` likewise; and once the ordinary
constructors produce cells, every list in the system is a cell chain and the
second representation is dead weight that `car`, `cdr`, `pair?`, `eq?`, `equal?`
and every traversal still have to handle. The two-representation design pays the
full conversion cost and adds a permanent case split.

Representing a list as a mutable array is worse: it cannot express cdr sharing,
which is the point of cons cells, and cannot represent a cycle at all.

So: one representation, cons cells.

## What the cell has to carry

```
and PairCell = {
    mutable car : LispVal
    mutable cdr : LispVal
    /// R-1RK distinguishes mutable from immutable pairs. copy-es-immutable
    /// (4.7.2) produces immutable ones, and $vau (4.10.3) and load (15.2.2)
    /// acquire immutable copies of the structures they capture.
    immutable : bool
}
```

The immutability flag is not optional. The report has `set-car!` signal an error
on an immutable pair, and more importantly IronKernel already *depends* on
algorithm structure being immutable: `OperativeRecord.compiledBody` memoises the
compiled form of a body (`Eval.fs`, where `compiledBody` is read and assigned).
That memo is sound today only because a body cannot change after `$vau` captured
it. With mutable pairs it stays sound only if `$vau` copies its operands
immutably, which is exactly what 4.7.2's rationale says `$vau` is for. `$vau`
currently stores `body` directly (`Runtime.fs`, the `Operative` construction).

This is the part most likely to be missed, so it is phase 0 below rather than an
afterthought: it is a correctness prerequisite for the memo, not a feature.

## Containing the churn

Converting the sites by hand is where a change like this goes wrong. Most of them
do not care that a list is an F# list; they care about shape — `| List [a; b] ->`
for arity dispatch, `List [x; y]` to build a result.

The pattern side survives intact. An active pattern named `List` coexists with the
F# `List` module, so sites like

```
| List [] -> ...
| List (x :: rest) -> ...
```

compile unchanged over cells:

```
let (|List|_|) (value: LispVal) : LispVal list option = (* walk a proper chain *)
```

The construction side does not. Defining `let List (values: LispVal list)` to
build a chain **shadows the `List` module**, and the 194 `List.map` /
`List.length` / `List.foldBack` usages elsewhere stop resolving. This was checked
rather than assumed: with the function defined, the compiler rejects
`List.length` as "The field, constructor or member 'length' is not defined".

So the constructor takes a different name — `ofList`, `ofDotted` — and the ~32
construction sites are edited, while the ~28 pattern sites are not. That is the
right split anyway: construction is where the immutability flag has to be chosen,
so those sites deserve to be looked at individually.

Two further caveats, both real:

- The active pattern materialises an F# list on every match, allocating on paths
  that currently allocate nothing. The evaluator's argument dispatch and the
  primitives' arity matching are the hot ones, and they should move to direct cell
  access rather than keep the convenience pattern. Which sites those are is a
  measurement question, not a guess — `CompilerBenchmarks` is the instrument.
- The active pattern must not loop on a cyclic argument. Bounding the walk and
  returning `None` past the bound is the right answer for "is this a proper list
  of the shape I expect", and keeps cycle-handling in the places that should have
  it. A prototype confirms a self-referential cell falls through to the
  not-a-proper-list branch rather than hanging.

## Plan

**Phase 0 — capture goes through an immutable-acquisition seam.** *Done.* Both
operative construction sites — the `vau` primitive and the compiler's `CVau` —
route the parameter tree and body through `acquireImmutable` /
`acquireImmutableForms`, which are the identity today because every pair is
already immutable. It lands with no observable change and no risk, and it is what
makes the `compiledBody` memo sound later; doing it first means the later phases
cannot silently invalidate it.

`load` needed no seam, contrary to the first draft of this plan. R-1RK 15.2.2 has
it acquire immutable copies of what it captures, and IronKernel's `load` captures
nothing: each parsed form is evaluated and discarded, and an operative created
along the way acquires its own structure through `vau`. That is recorded as a
comment there rather than as a call that would do nothing.

**Phase 1 prerequisite — one spelling of the empty list.** *Done.* `LispVal`
carries both `Nil` and `List []`, and only the second was recognised: applying
`#inert` produced the bare case, which was neither `null?` nor `eqv?` to itself.
A value that is not equal to itself breaks the reflexivity 4.3.1 requires of an
equivalence predicate, and the package decoder produced the same case for tag 5,
so a value read back from a `.ikc` was not `eqv?` to the equal value built at
runtime. The producers now normalise and the predicates accept both spellings.
Collapsing the two cases on top of that inconsistency would have buried the bug
rather than fixed it, so it is fixed first and phase 1 removes the duplicate case
outright.

**Phase 1 — introduce the cell.** *Done.* `LispVal` has `Pair of PairCell` with a
mutable car, a mutable cdr and an immutability flag, and `Nil` is the only empty
list. `List` and `DottedList` survive as active patterns, so the match sites
compiled untouched and only construction moved, to `ofList` / `ofDotted`.
Everything is still built immutable and nothing mutates a cell, so no behaviour
changes.

The active-pattern cost was worse than this plan guessed, and the guess about
*where* was wrong. It is not confined to argument dispatch and arity matching: any
site that asks a question about **one cell** through a list pattern became linear,
and the damage was concentrated in a handful of places that are called constantly.

- `car` walked a whole chain to read its first cell. `cdr` and `cons` walked it
  *and rebuilt it*, so every `(cdr rest)` in a library loop copied the rest of the
  list and every traversal was quadratic.
- `bind` destructured and rebuilt both the parameter chain and the argument chain
  on every iteration, making operative application quadratic in its arity.
- The evaluator matched `List (Atom name :: args)` and then `List (op :: args)`,
  materialising the operands twice per combination.
- The analyzer matched up to seven list patterns against the same form, walking
  and rebuilding it each time — most of what compiling a form does.
- `null?`, `pair?`, the `ListShape` contract check and the equivalence walk each
  walked a chain to answer a question about one cell.

The rule that falls out, and the one to apply in later phases: **anything asking
about a cell matches `Pair` or `Nil` directly; only code that genuinely wants the
elements uses the list pattern, and then only once.** Where a function needs the
elements repeatedly it materialises them once at the top and matches on the F#
list from there.

Against the baseline below, after those changes:

| Method | before | after | |
|---|---:|---:|---|
| ColdCompile | 105.4 ns / 592 B | 145.8 ns / 808 B | +38% |
| Interpreted | 371.1 ns / 1872 B | 401.0 ns / 2024 B | +8% |
| CompiledGeneric | 173.6 ns / 808 B | 175.1 ns / 808 B | +1%, allocation identical |
| CompiledFolded | 51.9 ns / 304 B | 52.6 ns / 304 B | +1%, allocation identical |

The steady-state compiled paths are at parity, which is what this plan named as
the number to hold. What remains is paid where a cons chain has to be turned into
an F# list for code that wants the elements: compiling a form, and evaluating one
interpreted. That is inherent to keeping the list patterns rather than rewriting
the analyzer and evaluator against cells directly, and it is the obvious place to
look if the interpreted path ever needs to be faster.

The full suite is 114s against 107s on master, all 342 tests passing.

**Phase 2 — `eq?` becomes identity.** *Done.* `eq?` and `equal?` were both bound
to the same structural walk; they now share one traversal that differs in a single
respect — `eq?` compares pairs by cell identity, `equal?` compares them
structurally. That is exactly what 4.2.1 asks for: "two pairs returned by
different calls to cons are not eq?, even if they have the same car and cdr and
the implementation doesn't support pair mutation". Environments were already
distinguished the same way. The 4.2.1 divergence is retired.

Two further bugs surfaced while splitting them, both in required entries and both
of the same shape as the `Nil` one that preceded phase 1. The structural walk
covered only the types with a structural comparison and let everything else fall
through to *not equal*, so an environment, a vector, a primitive combiner and a
continuation were **not equal to themselves** — reflexivity is rule 1 of both
4.2.1 and 4.3.1. A reference-equality case ahead of the type-specific ones fixes
all of them at once. And neither predicate was variadic, though 6.5.1 and 6.6.1
generalize both to zero or more arguments.

`copy-es`'s promise that its result is not `eq?` to a pair argument (6.4.2) became
observable at this point, so the 4.7 divergence no longer has to record it as
unobservable.

The expected fallout did not materialise: `assq` and `memq?` are `assoc` and
`member?` over `eq?`, and this plan expected their tests to need revisiting. They
did not, because they are exercised with symbols and numbers, which remain `eq?`
when equal. That is worth knowing rather than assuming — a program that used
`memq?` over freshly built lists would now get a different answer.

**Phase 3 — mutation.** `set-car!` and `set-cdr!` (4.7.1), signalling on an
immutable pair. `copy-es` (6.4.2) becomes a real copy with an observably fresh
result, and `copy-es-immutable` (4.7.2) stops being the identity. These are the
entries the module is named for, and the first point at which anything can
actually change under a reference.

**Phase 4 — cycle safety.** Now that `encycle!` is buildable, before it is built:
`equal?` gets a termination-safe algorithm; `showVal` — already an explicit work
stack — gets cycle detection; `get-list-metrics` computes the four metrics for
real. Then the `kernel.ikr` list library derivations that carry "no list can be
cyclic" comments are revisited one at a time against the report's cyclic cases.
`equal?` is a required entry, so this phase is not optional.

**Phase 5 — the mutating library entries.** `encycle!` (5.8.1) and `append!`
(6.4.1), which is where a cycle first enters the system from Kernel code.

**Phase 6 — re-validate and record.** Benchmarks against the baseline, the CLR
fault sweep extended with cyclic and mutation cases, the conformance matrix
regenerated, and the 4.7 and 4.2.1 divergences removed.

## Baseline to hold

`CompilerBenchmarks` on master at the time of writing:

| Method | Mean | Allocated |
|---|---:|---:|
| ColdCompile | 105.4 ns | 592 B |
| Interpreted | 371.1 ns | 1872 B |
| CompiledGeneric | 173.6 ns | 808 B |
| CompiledFolded | 51.9 ns | 304 B |

340 tests pass; the conformance matrix records 119 of 135 entries verified and 35
of 44 modules complete.

A cons cell and an F# list cell are both one heap object per element, so the
allocation totals should be close. The risk is not allocation volume but the
arity-dispatch paths described above, and `CompiledGeneric` is the number that
will show it first.

## Consequences

The change retires two divergences (4.7 and 4.2.1), completes an optional module,
and makes two required entries — `equal?` and `get-list-metrics` — honest about
cycles rather than correct only because cycles cannot occur.

It also removes a simplifying assumption the codebase currently benefits from
everywhere: that a value's structure is finite and cannot change while being
walked. Every traversal added after this lands has to be written with that in
mind, and the analyzer and compiler are protected only by phase 0's copying, not
by the type system.

The phases are ordered so that each is independently reviewable and the suite
stays green throughout. Phases 0 and 1 change no behaviour at all; phase 2 changes
behaviour that is currently a recorded divergence; phases 3 to 5 add the module.
If the work stops after any phase, the result is a consistent system rather than a
half-migration — which is the main reason for doing it in this order rather than
starting with the entries the module is named for.
