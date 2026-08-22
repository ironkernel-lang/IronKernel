# IronKernel.Amb

Nondeterministic search for IronKernel. Choice points are ordinary
expressions, the search strategy is a value, and the code doing the searching
never mentions a continuation.

```scheme
(collect
  (let ((a (amb (list 1 2))))
    (let ((b (amb (list 10 20))))
      (emit (cons a b)))))
; => ((1 . 10) (1 . 20) (2 . 10) (2 . 20))
```

Built on IronKernel's `shift`/`reset`, which are multi-shot and re-delimit when
resumed — so a choice point can invoke its captured continuation once per
alternative.

## Use

```bash
ik add IronKernel.Amb 0.1.0
```

Or, from a checkout of this repository:

```bash
cd lib/IronKernel.Test && ik pack     # seed the local feed for the test DSL
cd ../IronKernel.Amb
ik test
ik pack
```

## API

### Choice points

| Form | Meaning |
|---|---|
| `(amb xs)` | Yield each element of `xs`. An empty list fails. |
| `(amb-range lo hi)` | Yield each integer in `[lo, hi)` without building a list. |
| `(require test)` | Continue only if `test` holds, otherwise fail. |
| `(fail)` | Abandon the current branch. |
| `(amb-bracket xs ok? enter! leave!)` | Yield each `x` satisfying `ok?`, with `enter!` applied before the continuation runs and `leave!` after it finishes. |
| `(amb-bracket-range lo hi ok? enter! leave!)` | The same over `[lo, hi)`. |

### Reporting

| Form | Meaning |
|---|---|
| `(emit s)` | Report a solution. A no-op outside any strategy. |

### Strategies

Operatives. Each installs a delimiter, runs the body, and restores the
previous handler.

| Form | Returns |
|---|---|
| `(collect body …)` | List of every solution, in the order found. |
| `(first-of body …)` | The first solution, or `()`. Escapes through `call/cc`, so the rest of the tree is never explored. |
| `(count-of body …)` | How many solutions, retaining none of them. |
| `(search handler body …)` | `#inert`; applies `handler` to each solution. Use for strategies of your own. |

## Mutable state and backtracking

A search that mutates a board or a set of used lines has to undo that mutation
when a branch is abandoned, and doing it at the call site does not work: by the
time a choice expression returns, the rest of the search has already run inside
the continuation. The undo belongs to the choice point, which is what
`amb-bracket` is for.

```scheme
(let ((y (amb-bracket-range 0 n
           (lambda (c) (free? x c))        ; guard
           (lambda (c) (mark! x c 1))      ; before the continuation runs
           (lambda (c) (mark! x c -1)))))  ; after it has been exhausted
  (place-queen (+ x 1)))
```

State stays consistent with the caller's view of it, and the caller still never
sees a continuation. `test/amb_test.ikr` builds n-queens this way in about
twenty lines.

## Notes

- Strategies nest: an inner search runs to completion inside one branch of an
  outer one.
- The library performs no host I/O.
- `amb` and friends must run inside a strategy — that is what installs the
  `reset` their `shift` needs.

## Origin

Extracted from [`Examples/constant-width-amb.ikr`](../../Examples/constant-width-amb.ikr),
which enumerates figures of constant width on a chessboard and, as the width-1
case, solves the n-queens problem.
