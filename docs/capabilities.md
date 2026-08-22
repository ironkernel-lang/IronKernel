# Capability environments

IronKernel environments carry a host-authority set in addition to bindings and
parents. Authority is not a Kernel value and cannot be introduced with
`define`, `set!`, `import!`, or `eval`.

## Profiles

- `minimal`: no source loading, host I/O, raw CLR reflection, or generated CLR bindings
- `safe`: generated bindings from the reviewed `safe` manifest
- `unrestricted`: all current host integration, including CLR Task adapters; the compatibility default

Child environments receive the intersection of their own creator's authority
and every parent environment's authority. This prevents an empty or mixed-parent
environment from manufacturing additional access.

`(environment-capabilities env)` reports an environment's authority set as a
list — for example `(host-io (generated-clr "safe"))` — under every profile.
It reveals information, not authority: reading the set grants nothing, and its
companions `environment-symbols` / `environment-local-symbols` likewise return
symbol names, never parent environments as values (ADR 0009).

## Defense in depth

Restricted profiles omit dangerous names from their primitive environments.
The values behind raw interop, I/O, source loading, and generated wrappers also
check the invoking environment. Consequently, copying a primitive from an
unrestricted environment into a safe environment does not transfer authority.

First-class environments and compound operatives are themselves capability
references: an operative retains its lexical environment, and an environment
can be passed to `eval`. Deliberately handing either value from an unrestricted
root to restricted code delegates that root's authority. Embedders must expose
only environments and closures whose authority they intend to grant.

## Generated CLR surface

`manifests/safe-clr-bindings.json` names one exact public static method signature
for every guest-visible binding. `tools/generate-clr-bindings.fsx` validates each
signature and emits direct typed F# calls in `IronKernel.Runtime/Generated/Bindings.Safe.fs`.

Generation rejects duplicate guest names, unknown types, unsupported conversion
types, missing overloads, and return-type mismatches. Runtime argument conversion
is limited to the types declared by the manifest; it never invokes the CLR
default binder.

## Threat model

Capability environments control host authority within one IronKernel runtime.
They are not a CPU, memory, or termination sandbox. Run untrusted programs in a
separate OS process with resource limits. The VS Code playground provides a
timeout and output limits, but those are availability controls rather than a
complete security boundary.

`HostAsync` is unrestricted-only. Copying `await-task` or `task-delay` into a
restricted environment still fails at invocation because both primitives check
the current environment.
