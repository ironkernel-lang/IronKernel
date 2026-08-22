# IronKernel.Collections

List, alist, set, and vector utilities for IronKernel — the combinators the
standard library stops short of.

```scheme
(sort (list 3 1 2) <?)                     ; => (1 2 3)
(take (list 1 2 3 4) 2)                    ; => (1 2)
(group-by odd? (list 1 2 3 4 5))           ; => ((#t 1 3 5) (#f 2 4))
(vector->list (list->vector (list 1 2)))   ; => (1 2)
```

Conventions match the standard library's own: procedure arguments first and
the collection last (as in `filter` and `any?`); nothing mutates its argument
except the two `!`-marked vector operations; set and alist operations compare
with `equal?` (structural), like `assoc` and `member?`.

## Use

```bash
ik add IronKernel.Collections 0.1.0
```

Or, from a checkout of this repository:

```bash
cd lib/IronKernel.Test && ik pack     # seed the local feed for the test DSL
cd ../IronKernel.Collections
ik test
ik pack
```

## API

### Folds and basics

| Form | Meaning |
|---|---|
| `(reverse xs)` | |
| `(fold-left f init xs)` | `(f (… (f init x1) …) xn)` |
| `(fold-right f init xs)` | `(f x1 (… (f xn init) …))` |

### Slicing

`(take xs n)`, `(drop xs n)` — fewer/none if the list runs out;
`(take-while keep? xs)`, `(drop-while keep? xs)`.

### Mapping and searching

| Form | Meaning |
|---|---|
| `(append-map f xs)` | Map and append the resulting lists. |
| `(flatten xs)` | Every non-pair leaf, in order. |
| `(partition keep? xs)` | `((kept …) (rest …))`, each in original order. |
| `(remove reject? xs)` | The complement of `filter`. |
| `(find accept? xs)` | First match, or `#f`. |
| `(count accept? xs)` | |
| `(every? accept? xs)` | Applicative companion to `any?`; `#t` on the empty list. |

### Generation

`(iota n [start [step]])`, `(range lo hi)` (half-open),
`(zip-with f xs ys)` (stops with the shorter list).

### Sorting

| Form | Meaning |
|---|---|
| `(sort xs less?)` | Stable merge sort; `less?` orders strictly, as `<?` does. |
| `(sort-by key less? xs)` | `(sort-by length <? xss)` |

### Sets over `equal?`

`(distinct xs)` (keeps first occurrences), `(union a b)`,
`(intersection a b)`, `(difference a b)`.

### Association lists

| Form | Meaning |
|---|---|
| `(assoc-set alist key value)` | Fresh alist; replaces in place or appends. |
| `(assoc-remove alist key)` | |
| `(assoc-keys alist)` / `(assoc-values alist)` | |
| `(group-by key xs)` | Alist from key values to their elements, keys in first-appearance order. |

### Vectors

`(vector->list v)`, `(list->vector xs)`, `(vector-map f v)` (fresh),
`(vector-for-each f v)`, `(vector-fill! v value)`.

## Notes

- Pure Kernel: no CLR interop, no host I/O.
- Deep recursion is safe — the evaluator is a CPS trampoline — so `sort` and
  `fold-right` handle long lists without stack concerns.
