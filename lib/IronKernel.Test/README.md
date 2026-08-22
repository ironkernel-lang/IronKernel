# IronKernel.Test

A small testing DSL for IronKernel. Checks are operatives, so a failing check
reports the *source form* it evaluated — and every check runs inside an error
guard, so a check that signals an error is recorded as a failure and the run
continues to the next check.

```scheme
(suite "arithmetic"
  (check "addition commutes" (=? (+ 1 2) (+ 2 1)))
  (check-equal "cons builds a pair" (cons 1 2) (cons 1 (+ 1 1)))
  (check-error "car of a number signals" (car 5)))
(report-checks)
```

```
arithmetic
  ok    addition commutes
  ok    cons builds a pair
  ok    car of a number signals

3 check(s), 0 failure(s)
```

`report-checks` signals an error when any check failed, which is exactly what
`ik test` treats as a failing test file.

## Use

```bash
ik add IronKernel.Test 0.1.0
```

Or, from a checkout of this repository:

```bash
cd lib/IronKernel.Test
ik test
ik pack
```

## API

### Checks

| Form | Meaning |
|---|---|
| `(check name expr)` | Pass only when `expr` evaluates to `#t`. `#f`, a non-boolean result, and a signalled error are three distinct failures, each reported with the source form. |
| `(check-equal name expected actual)` | Pass when the two values are `equal?` — structural, so lists, vectors, and strings compare by content. Failure prints both values. |
| `(check-error name expr)` | Pass when `expr` signals an error; a normal return is the failure, reported with the value. |

`name` is evaluated (normally a string literal); the remaining operands are
evaluated in the caller's environment when the check runs.

### Grouping and reporting

| Form | Meaning |
|---|---|
| `(suite name check …)` | Print `name` as a heading, then run the body. |
| `(report-checks)` | Print the tally, list the failed names, and signal an error if anything failed. End every test file with this. |
| `(checks-summary)` | `(passes (failed-name …))`, for tools building on the DSL. |
| `(reset-checks!)` | Clear the tally. |

## Failure output

Each kind of failure explains itself:

```
  FAIL  a false check fails
        expression: (eq? 1 2)
  FAIL  a non-boolean check fails
        expression: (+ 1 2)
        non-boolean: 3
  FAIL  unequal values fail
        expected: 1
        actual:   2
```

## Notes

- Errors are intercepted with an exit guard on `error-continuation`
  (R⁻¹RK 7.2.5); the guard is per-check, so state outside the check is
  untouched.
- A check passes only on `#t` — the same discipline `filter` applies to its
  predicate, so `(check "..." (length xs))` is caught rather than silently
  truthy.
- The package performs no host I/O beyond writing to the current output port.
