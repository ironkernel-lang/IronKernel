# IronKernel packages

IronKernel packages are ordinary NuGet dependency packages tagged
`ironkernel`. A package may contain both IronKernel source and CLR assemblies.

## Layout

```text
package.nupkg
├── ironkernel/package.json
├── ironkernel/src/**/*.ikr
├── ironkernel/lib/**/*.ikc
├── ironkernel/bindings/*.json
├── lib/net10.0/*.dll
└── buildTransitive/*.targets
```

The project loader reads restored `project.assets.json`, loads declared CLR
runtime assemblies, then evaluates `ironkernel/src/**/*.ikr` in deterministic
path order before project sources.

Files under `ironkernel/lib/**/*.ikc` use the versioned IKC2 portable Core IR
format. They contain typed syntax and diagnostic metadata rather than an embedded
source payload or platform-specific CLR code.

`ironkernel/package.json` may declare entry modules, exports, required runtime
version, capability requirements, and generated CLR binding manifests. The
initial `ik pack` command packages project sources and NuGet dependencies; a
schema-backed package manifest is the next format revision.

## Dependency scopes

A `PackageReference` may carry `IronKernelScope="test"`; `ik add <id> <ver>
--test` writes one. A test-scoped reference restores normally and its sources
load for `ik test` only — after runtime dependency sources, before project
sources. `ik run` and `ik build` ignore it, and `ik pack` leaves it out of the
published package's dependency group, so consumers never inherit a test
harness. Anything reachable from a runtime-scoped reference stays runtime,
whatever else also references it. The scope attribute accepts `runtime` (the
default) and `test`; anything else fails the project load.

## Repositories and repeatability

- Public packages are published to NuGet.org.
- Private packages use standard NuGet feeds and `NuGet.config`.
- Projects enable `RestorePackagesWithLockFile`.
- Commit `packages.lock.json`.
- CI uses `ik restore --locked`.
- Use NuGet package-source mapping to prevent dependency confusion.

Custom NuGet package types are intentionally avoided because ordinary
Visual Studio and NuGet installation paths do not support them consistently.
