# IronKernel.Strings

String and format utilities for IronKernel. Strings in IronKernel are CLR
strings and the runtime keeps its primitive surface small; this package wraps
the CLR interop in the vocabulary a Kernel program expects.

```scheme
(string-split "a,b,c" ",")            ; => ("a" "b" "c")
(string-join (list "a" "b" "c") "-")  ; => "a-b-c"
(substring "hello" 1 4)               ; => "ell"
(format "{0} of {1:F1}" 2 3.0)        ; => "2 of 3.0"
```

Three commitments, chosen once so no caller has to think about them:

- **Comparisons are ordinal.** Search, prefix, suffix, and ordering compare
  UTF-16 units, never the current culture.
- **Formatting is culture-invariant.** `format`, `number->string`, and
  `string->number` read and write the invariant culture, so `3.5` renders as
  `"3.5"` on every machine.
- **Half-open intervals.** `substring` takes `[start, end)` like the rest of
  the language's ranges, not .NET's `(start, length)`.

## Use

```bash
ik add IronKernel.Strings 0.1.0
```

Or, from a checkout of this repository:

```bash
cd lib/IronKernel.Test && ik pack     # seed the local feed for the test DSL
cd ../IronKernel.Strings
ik test
ik pack
```

## API

### Classification

| Form | Meaning |
|---|---|
| `(string? x)` / `(char? x)` | By CLR runtime type; every Kernel value answers `#f`. |

### Basics

| Form | Meaning |
|---|---|
| `(string-length s)` | UTF-16 length. |
| `(string-empty? s)` | Length zero. |
| `(string-ref s i)` | Character at `i`, from zero. |
| `(substring s start end)` | The characters in `[start, end)`. |
| `(string-append s …)` | Concatenation; no arguments give `""`. |
| `(string->list s)` / `(list->string chars)` | To and from a list of characters. |

### Search

| Form | Meaning |
|---|---|
| `(string-index-of s sub)` | First index, or `#f`. |
| `(string-contains? s sub)` | |
| `(string-starts-with? s prefix)` / `(string-ends-with? s suffix)` | |

### Split and join

| Form | Meaning |
|---|---|
| `(string-split s sep)` | Every field, empties included; `sep` is a non-empty string. |
| `(string-join strings sep)` | |
| `(string-lines s)` | Lines, treating `\r\n` and `\n` alike; one trailing newline yields no final empty line. |

### Case, trimming, editing

`string-upcase`, `string-downcase` (invariant), `string-trim`,
`string-trim-start`, `string-trim-end`, `(string-replace s old new)` (every
occurrence, ordinal), `(string-repeat s n)`, `(string-reverse s)`,
`(string-pad-left s width [pad])`, `(string-pad-right s width [pad])`.

### Numbers

| Form | Meaning |
|---|---|
| `(string->number s)` | The number in invariant notation, or `#f`. Integers stay exact (narrowed to 32-bit when they fit); a point or exponent gives an inexact. Group separators are rejected. |
| `(number->string n [spec])` | Invariant rendering; `spec` is a .NET format spec (`"F2"`, `"X"`, …). |

### Ordering

`(string-compare a b)` gives -1/0/1 ordinally; `string=?`, `string<?`,
`string>?`, `string<=?`, `string>=?` derive from it.

### Characters

`char->integer`, `integer->char`, `char-digit?`, `char-letter?`,
`char-whitespace?`, `char-upper?`, `char-lower?`, `char-upcase`,
`char-downcase`.

### format

`(format fmt arg …)` — .NET-style holes `{n}` and `{n:spec}`, any number of
arguments, `{{`/`}}` for literal braces, always the invariant culture.
Implemented here rather than delegated to `String.Format` so the argument list
is unbounded; a hole past the arguments, an empty hole, or an unbalanced brace
signals an error.

## Notes

- Values in `format` holes must be CLR-convertible (numbers, strings,
  booleans, CLR objects); to render Kernel structure, use `show`.
- The package performs no host I/O.
