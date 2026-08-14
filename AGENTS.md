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
  `dotnet build` are the lint signal (the build currently has warnings, 0 errors).

### REPL gotchas (non-obvious)
- `dotnet run --project IronKernel` loads `kernel.ikr` and `promises.ikr` from
  the current directory when present, then falls back to the application output
  directory. Running from the repository root is supported.
- The REPL uses the `Mono.Terminal` line editor, which needs a **real TTY**.
  Piping stdin (`printf ... | dotnet run`) crashes with a `System.Console`
  `SetCursorPosition` exception. For scripted/interactive REPL testing, drive it
  through a pty (e.g. a `tmux` session with `send-keys`).
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
