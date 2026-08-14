# AGENTS.md

## Cursor Cloud specific instructions

IronKernel is a single product: an F#/.NET 10 hybrid CLR compiler + REPL for the
Kernel language (`IronKernel.sln`, projects `IronKernel`, `IronKernel.Runtime`,
`IronKernel.Tests`, `Mono.Terminal`). The `website/` directory is only a static
promo site (`python3 -m http.server -d website 8080`) and is not part of the app.

### Source layout
- `IronKernel.Runtime/` owns the shared core: `Monads.fs`, `Ast.fs`,
  `Capabilities.fs`, `Errors.fs`, `SymbolTable.fs`, `Contracts.fs`, `ClrSugar.fs`,
  `Eval.fs`, `RuntimeDispatch.fs`, `ClrBindings.fs`, `Arithmetic.fs`, `Interop.fs`,
  `Generated/Bindings.Safe.fs`, `Runtime.fs`.
- `IronKernel/` owns the parser, analyzer, compiler, REPL, and CLI (`ik`) and
  consumes the core through a `ProjectReference` to `IronKernel.Runtime`.

### Environment
- The .NET 10 SDK lives at `~/.dotnet` and is added to `PATH`/`DOTNET_ROOT` via
  `~/.bashrc`. New login shells already have `dotnet` available. Non-login shells
  may need the full path `~/.dotnet/dotnet`.

### Build / test / lint / run
- Standard commands are in `README.md`. Debug (dev) is the default for
  `dotnet build`/`dotnet test`; CI (`.github/workflows/ci.yml`) uses `-c Release`.
- There is no separate linter; the F# compiler warnings emitted during
  `dotnet build` are the lint signal. `IronKernel`, `IronKernel.Runtime`, and
  `IronKernel.Tests` all set `<TreatWarningsAsErrors>true</TreatWarningsAsErrors>`,
  so the build is warning-clean by construction — a new warning fails the build.
  Keep it that way rather than adding `NoWarn` entries.

### Compilation reach (non-obvious, affects optimization work)
- Only **top-level** forms are compiled (`evalCompiled` / `compileFormsGuarded`).
  Procedure bodies are stored as raw `KernelCode` and interpreted form by form by
  `evalStep`; the `CompiledCombiner` case exists in `Ast.fs` but is **never
  constructed**. `define` also evaluates its right-hand side through `bounceEval`,
  so `(define f (vau ...))` never reaches the analyzer's specializations.
- Consequence for `Analyze.analyzeGuarded`: adding `PrimitiveIdentity` cases is
  currently a **pessimization, not a win**. Guards re-resolve the binding by name on
  every invocation, whereas the `COperate` fallback's `NamedCallSite` cache
  validates by environment reference equality and always hits when the environment
  is stable — which is the only situation compiled code sees today. Measured with
  `GuardSpecializationBenchmarks`: guarded is ~10% slower with a shared environment
  and ~12% faster only with a fresh frame per call, a case the runtime never
  produces. Compile procedure bodies first; then extending guards pays off.

### REPL gotchas (non-obvious)
- `dotnet run --project IronKernel` loads `kernel.ikr` and `promises.ikr` from
  the current directory when present, then falls back to the application output
  directory. Running from the repository root is supported.
- The REPL uses the `Mono.Terminal` line editor, which needs a **real TTY**.
  When stdin or stdout is redirected the REPL now detects it and falls back to
  plain `Console.ReadLine`, so piping works:
  `printf '(+ 1 2)\nquit\n' | dotnet run --project IronKernel`. End of input exits
  cleanly, so the trailing `quit` is optional. Use a pty (e.g. `tmux send-keys`)
  only when testing line-editing behaviour itself (history, completion, arrows).
- IronKernel is **Kernel, not Scheme**. Use `define`/`defn`, `lambda`, `if`,
  `letrec`. `+` and `*` are **binary** (exactly 2 args). `display`, `=?`, and
  `$let` are not bound; print via .NET interop, e.g.
  `(define write (lambda (x) (. System.Console WriteLine x)))`.

### Running scripts / compiling
- Run a script file: `dotnet run --project IronKernel -- path/to/file.ikr`
  (script and package modes auto-load the standard library).
- Compile to an IKC package:
  `dotnet run --project IronKernel -- compile file.ikr -o out.ikc`.
- Run a package: `dotnet run --project IronKernel -- run out.ikc`.
