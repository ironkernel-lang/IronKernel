# First-party packages

Each directory here is an ordinary `.ikproj` IronKernel package: `ik test`
runs its tests, `ik pack` builds the `.nupkg`. They are the batteries the
language ships with, grown deliberately — small surfaces, report-consistent
conventions, tests that can fail for the right reason.

| Package | Provides |
|---|---|
| [`IronKernel.Test`](IronKernel.Test/) | Testing DSL: checks as operatives that report the failing source form, error assertions, suites, a tally that fails `ik test` when a check does |
| [`IronKernel.Collections`](IronKernel.Collections/) | Folds, slicing, stable sort, sets over `equal?`, alist editing, the vector/list bridge — pure Kernel |
| [`IronKernel.Strings`](IronKernel.Strings/) | Search, split/join, case, trimming, padding, characters, invariant number conversion, variadic `format` — ordinal semantics throughout |
| [`IronKernel.Json`](IronKernel.Json/) | Grammar-enforcing JSON reader with offsets in its errors, a writer that refuses what JSON cannot carry, pretty-printing, path traversal |
| [`IronKernel.Math`](IronKernel.Math/) | Statistics, combinatorics, number theory — exact wherever the mathematics allows: means as ratios, `isqrt` and `factorial` at any size, primes, factorizations, totients |
| [`IronKernel.Amb`](IronKernel.Amb/) | Nondeterministic search: `amb`, `require`, bracketed choice, pluggable search strategies over multi-shot delimited continuations |

## Working in this directory

Packages test with `IronKernel.Test` through a **test-scoped reference**
(`IronKernelScope="test"`, written by `ik add <id> <ver> --test`): it loads
for `ik test` only and never appears in a published package's dependencies.
`IronKernel.Json` additionally depends on `IronKernel.Strings` at runtime,
and `IronKernel.Math` on `IronKernel.Collections`.

Until these are published to NuGet.org, siblings resolve through the local
folder feeds in [`NuGet.config`](NuGet.config). Seed them once per checkout:

```bash
cd IronKernel.Test && ik pack
cd ../IronKernel.Strings && ik pack
cd ../IronKernel.Collections && ik pack
```

Packages that consume a locally packed sibling do not commit
`packages.lock.json` — a local `.nupkg` has no stable content hash, so a
committed lock would fail locked restore everywhere else. Once a dependency
is on NuGet.org the lock can return.

NuGet caches by id and version: after changing a dependency without bumping
its version, delete `~/.nuget/packages/<id>/<version>` (and the consumer's
`obj/`) so the repacked copy is picked up.

## Candidates for what comes next

- **Time** — dates, durations, and formatting over `System.DateTime`, with
  the same invariant-culture discipline as `IronKernel.Strings`.
- **Ports/IO** — structured file and path helpers over the capability-gated
  port primitives.
- A **conformance-style docs page** per package, generated from its tests,
  the way `docs/kernel-conformance.md` is generated from the suite.
