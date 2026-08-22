# IronKernel

An implementation of the Kernel programming language (R⁻¹RK, WPI TR 05-07) on .NET,
plus a compiler, a project/package tool (`ik`), and a CLR interop surface.

The report is the specification. When behaviour is in question, quote the report
section rather than reasoning from what the code does.

## Build and test

```
dotnet build IronKernel.sln -c Release --nologo
dotnet test  IronKernel.sln -c Release --nologo
```

The suite is currently 409 tests and takes roughly two minutes.

## Verification ritual

Run all of this before opening a PR. Each step has caught something the others did
not.

1. **Clean rebuild, zero warnings.** `dotnet build IronKernel.sln -c Release --no-incremental --nologo`
2. **Full suite.**
3. **Every example.** `Examples/*.ikr`, skipping `yingyang.ikr` — it is non-terminating
   by design. Run the built binary directly (`IronKernel/bin/Release/net10.0/IronKernel`);
   `dotnet run` in a loop has hung here.
4. **CLR fault sweep.** `python3 tools/scan-clr-faults.py IronKernel/bin/Release/net10.0/IronKernel tools/clr-fault-cases.txt`
   Expect `faulted (process aborted): 0`. A non-zero count means a CLR exception
   escaped as a process abort instead of a Kernel error.
5. **Benchmarks**, when the change could touch evaluation:
   `dotnet run -c Release --project IronKernel.Benchmarks -- --filter '*CompilerBenchmarks*'`
   Classes: `CompilerBenchmarks`, `ControlFlowBenchmarks`, `GuardSpecializationBenchmarks`,
   `EqualityBenchmarks`, `SymbolLookupBenchmarks`, `ApplicationArityBenchmarks`,
   `ClrResolutionBenchmarks`.

## Conformance matrix

`docs/kernel-conformance.md` is **generated**, by probing a real bootstrapped
environment in `IronKernel.Tests/KernelConformanceTests.fs`. A test fails if the
committed copy is stale, so it cannot drift from the implementation.

```
IRONKERNEL_UPDATE_CONFORMANCE=1 dotnet test IronKernel.sln -c Release --nologo --filter "conformance matrix"
```

The README quotes the matrix's headline counts and a separate test checks that too.
Current state: 135/135 entries verified, 44/44 modules, 11 divergences.

R⁻¹RK §1.3.2 makes the **module** the unit of conformance. `verified` means a
behavioural check exercises the entry — not that every requirement in it is proven.
Divergences are recorded in the same file and are worth reading before treating any
row as a conformance claim.

## Layout

| | |
|---|---|
| `IronKernel.Runtime/` | AST, evaluator (CPS trampoline), symbol table, primitives, CLR interop |
| `IronKernel/` | analyzer, compiler, package format, REPL, project tool (`ik`) |
| `IronKernel/kernel.ikr` | the standard library, in Kernel |
| `IronKernel.Tests/` | xunit; conformance matrix generator lives here |
| `docs/adr/` | architecture decision records |
| `Examples/` | runnable examples, including the `lantern` multi-file project |

## ADRs

0001 source/project/package conventions · 0002 AOT artifacts · 0003 portable core
package format · 0004 compiling procedure bodies · 0005 mutable pairs · 0006 errors
as abnormal passes · 0007 identity for derived combiners · 0008 caching compiled
bodies (proposed, deliberately not built) · 0009 editor tooling from the runtime
outward (`ik check --json`, environment enumeration, the `ik lsp` language
server, and reader recovery are its phases 1–4).

They record measurements and rejected options, not just decisions. When a prediction
in one turns out wrong, correct it in place rather than leaving it — several carry
inline corrections for exactly that reason.

## Conventions that earned their place

**A test must be able to fail for the right reason.** Check it. Two real examples:
"the file could be deleted" cannot detect an unclosed port, because deleting an open
file succeeds on Unix; and a tail-context test only means something if moving the
recursion out of tail position breaks it (it takes the captured continuation's depth
from 23 to 2003). Negative controls are cheap and have repeatedly shown a test was
vacuous.

**Counts and profiles have not predicted cost here.** Three hypotheses — caching
compiled bodies, pre-sizing the frame dictionary, the equality path — looked
compelling by dispatch counts or a sampled profile and produced nothing on the clock.
The two changes that worked (`$sequence` and `let` as primitives, together 16.2s →
4.9s on the heaviest example) both removed work a *derivation* generated per call.
Verify by timing a real program before believing a profile. `dotnet-trace` on this
platform puts GC-poll frames at ~89%, so it is biased toward allocation sites.

**Benchmark noise vs regression.** A uniform slowdown across every case with
byte-identical allocation is the machine, not the code — usually a stray process from
an earlier run holding a core. Check `ps` for leftover `IronKernel` processes before
diagnosing. Killing a shell pipeline does not kill the `dotnet` child.

**Editing large F# files.** Prefer line-indexed edits over slicing between two text
anchors. Slicing has twice removed a function that happened to sit between the
anchors; the compiler caught it both times, but it is avoidable.

**Git.** Stage explicit paths. `git add -A` has swept unrelated untracked files into
a commit.

**The global `ik` tool can be stale.** It is installed separately from the repo
(`dotnet tool`, packaged from `IronKernel/IronKernel.fsproj` as `IronKernel.Tool`).
Check `ik --version` against `version` before investigating a reported bug — a
lantern crash reported against 0.4.2 did not exist on the current tree.
