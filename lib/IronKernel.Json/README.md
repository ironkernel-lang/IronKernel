# IronKernel.Json

JSON reading and writing for IronKernel, in the mapping the Scheme world has
settled on:

| JSON | Kernel |
|---|---|
| object | association list with string keys; `()` for `{}` |
| array | vector — so the empty array and the empty object differ |
| string | string |
| number | exact integer when the text is integral, inexact otherwise |
| `true` / `false` | `#t` / `#f` |
| `null` | `json-null` (test with `json-null?`) |

```scheme
(json-parse "{\"a\": [1, 2]}")          ; => (("a" . #(1 2)))
(json->string (list (cons "a" (vector 1 2))))
                                        ; => "{\"a\":[1,2]}"
(json-get doc "users" 0 "name")         ; strings index objects, integers arrays
```

The reader is a recursive-descent parser over the string — not a wrapper
around `System.Text.Json` — so errors carry the offset and the grammar is
enforced: leading zeros, bare `+`, trailing commas, unescaped control
characters, and trailing text all signal. The writer refuses values JSON
cannot carry (NaN, infinities, non-string keys, arbitrary Kernel or CLR
objects) rather than guessing.

## Use

```bash
ik add IronKernel.Json 0.1.0
```

Or, from a checkout of this repository:

```bash
cd lib/IronKernel.Test && ik pack        # seed the local feed
cd ../IronKernel.Strings && ik pack
cd ../IronKernel.Json
ik test
ik pack
```

## API

| Form | Meaning |
|---|---|
| `(json-parse text)` | The one JSON value the whole string denotes, or an error with the offset. |
| `(json->string value)` | Compact JSON. |
| `(json->string value #t)` | Pretty-printed with two-space indentation; empty `{}`/`[]` stay inline. |
| `(json-get value step …)` | Follow a path: a string step indexes an object, an integer step indexes an array. Signals when a step does not apply. |
| `json-null` | The null sentinel — a symbol, so it survives `equal?` and printing. |
| `(json-null? x)` | |

## Notes

- Member order is preserved in both directions; `json-parse` inverts
  `json->string` for JSON-representable data, and vice versa.
- Numbers read and write the invariant culture. An integral text becomes an
  exact integer (64-bit when needed); a fraction or exponent becomes an
  inexact.
- Escapes: `\" \\ \/ \b \f \n \r \t \uXXXX` are decoded; on the way out,
  control characters below U+0020 are `\u`-escaped.
- Depends on [`IronKernel.Strings`](../IronKernel.Strings/) at runtime.
  Nothing here performs host I/O.
