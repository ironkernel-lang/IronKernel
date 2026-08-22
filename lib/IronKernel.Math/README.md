# IronKernel.Math

Statistics, combinatorics, and number theory for IronKernel. The runtime's
numeric tower is already strong — integers promote to big integers, division
of exacts gives exact ratios in least terms — so this package adds what the
tower does not: the procedures that combine numbers, exact wherever the
mathematics allows.

```scheme
(mean (list 1 2))          ; => 3/2, exactly
(isqrt (expt 10 100))      ; => 10^50, exactly — sqrt would round
(binomial 52 5)            ; => 2598960
(prime-factors 360)        ; => (2 2 2 3 3 5)
```

Only `stdev` is inherently inexact — it takes a square root — and says so by
returning one.

## Use

```bash
ik add IronKernel.Math 0.1.0
```

Or, from a checkout of this repository:

```bash
cd lib/IronKernel.Test && ik pack        # seed the local feed
cd ../IronKernel.Collections && ik pack
cd ../IronKernel.Math
ik test
ik pack
```

## API

### Constants

`pi`, `tau`, `euler`, `golden-ratio` — each the double nearest the
mathematical value.

### Basics

| Form | Meaning |
|---|---|
| `(sign x)` | −1, 0, or 1, always exact, for any real. |
| `(clamp x lo hi)` | Signals if `lo > hi`. |
| `(lerp a b t)` | `a` at `t=0`, `b` at `t=1`; exact on exact inputs. |
| `(isqrt n)` | Largest integer whose square does not exceed `n`. Newton's method on exact integers — correct at sizes where `sqrt`'s double rounds. |

### Statistics

All take a non-empty list of reals and preserve exactness.

| Form | Meaning |
|---|---|
| `(sum xs)` / `(product xs)` | 0 and 1 on the empty list. |
| `(mean xs)` | An exact ratio on exact inputs. |
| `(median xs)` | Sorts internally; even count gives the mean of the two middles. |
| `(variance xs)` | Population variance, exact. |
| `(sample-variance xs)` | Bessel's n−1 correction; wants at least two elements. |
| `(stdev xs)` / `(sample-stdev xs)` | Inexact, by nature. |

### Combinatorics

| Form | Meaning |
|---|---|
| `(factorial n)` | Exact at any size. |
| `(binomial n k)` | n choose k by the rising product — k steps, never a full factorial. Out-of-range k gives 0. |
| `(permutations n k)` | Ordered selections: the falling factorial. |

### Number theory

| Form | Meaning |
|---|---|
| `(prime? n)` | Trial division stepping 6k±1 — exact at any size, suited to 64-bit-scale numbers, not cryptographic ones. |
| `(next-prime n)` | Smallest prime strictly greater than `n`. |
| `(primes-upto n)` | Sieve of Eratosthenes, bound included. |
| `(prime-factors n)` | With multiplicity, ascending; `(prime-factors 1)` is `()`. |
| `(divisors n)` | Every positive divisor, ascending, in O(√n). |
| `(totient n)` | Euler's φ, from the distinct prime factors, exactly. |
| `(coprime? a b)` | `gcd` is 1. |

## Notes

- Pure Kernel: no CLR interop, no host I/O. List work (folds, `sort`,
  `distinct`) comes from [`IronKernel.Collections`](../IronKernel.Collections/),
  a runtime dependency.
- Domain errors signal rather than answer: `(isqrt -1)`, `(factorial -1)`,
  `(prime? 7.0)`, `(sample-variance (list 1))` are all errors.
