# IronKernel examples

Run an example from the repository root:

```bash
dotnet run --project IronKernel -- Examples/hello.ikr
```

The CLI loads `kernel.ikr` and `promises.ikr` before each script. Compile any
finite example to an `.ikc` package with:

```bash
dotnet run --project IronKernel -- compile Examples/hello.ikr -o hello.ikc
dotnet run --project IronKernel -- run hello.ikc
```

| Example | Demonstrates | Notes |
|---|---|---|
| [`lantern/`](lantern/) | **Multi-file `.ikproj`**, HttpListener, `clr-open`, `vau` HTML DSL, tagged 404 | See [`lantern/README.md`](lantern/README.md); `ik run` entry point |
| `hello.ikr` | Environments, `lambda`, and CLR output | Prints `Hello,world!` |
| `safe-clr.ikr` | Generated, allowlisted CLR bindings | Run with `--profile safe` |
| `vau-dotnet.ikr` | User-defined control forms and .NET interop | Guided feature tour |
| `samples.ikr` | Recursion and the `let` family | Prints intermediate values |
| `continuations.ikr` | Full continuations | Defines local output helpers |
| `effects-async.ikr` | Tagged deep handlers and CLR Task suspension | Requires `unrestricted` profile |
| `contracts.ikr` | Operative/applicative contracts and guarded folding | Prints validated results |
| `coroutines.ikr` | Cooperative scheduling experiment | Historical example; not yet covered by the compatibility suite |
| `zipper.ikr` | Delimited continuations | Functional zipper traversal |
| `constant-width.ikr` | Mutable vectors, CPS backtracking, `args` | Enumerates constant-width chessboard figures; takes `n k w` |
| `constant-width-amb.ikr` | `shift`/`reset` as an `amb` layer, `vau` search strategies, encapsulation types | Same problem, direct style; also solves n-queens and builds width 3/4/8 figures |
| `sqrt.ikr` | Operative-based numeric procedure | Defines `sqrt`; intentionally produces no output |
| `yingyang.ikr` | Classic yin-yang continuation loop | Intentionally non-terminating; do not use it to test packaging |

Errors identify the source file and failing range:

```text
Examples/demo.ikr:2:1: Getting an unbound variable: 'missing'
(missing 42)
^^^^^^^^^^^^
```
