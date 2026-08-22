# IronKernel for Visual Studio Code

Language support and a local playground backed by the real IronKernel runtime.
The extension never implements a second evaluator in JavaScript.

## Features

- Syntax highlighting for lists, vectors, improper lists, keywords, `vau`, and CLR interop
- Distinct colors for **operatives** (unevaluated operands) vs **applicatives** (args evaluated first), matching the website token sets
- `.ikproj` files open as XML (MSBuild project syntax highlighting)
- Bracket matching, comments, indentation, and IronKernel snippets
- **Run Current File** and **Compile Current File to IKC** commands
- **Run Project** and **Build Project** for `.ikproj` (nearest project, picker, or explorer context menu)
- Check on save: `ik check --json` runs on saved `.ikr` files and publishes
  span-accurate diagnostics (disable with `ironkernel.checkOnSave`)
- Source-range diagnostics in VS Code's Problems view
- A playground with runnable examples, validation, cancellation, output limits, and timeouts

## Development

```bash
cd editors/vscode
npm install
npm run typecheck
npm test
npm run package
```

Open this directory in VS Code and press `F5` to launch an Extension Development
Host, or install the generated `.vsix` with **Extensions: Install from VSIX…**.

## Runtime discovery

The extension resolves IronKernel in this order:

1. The absolute path in `ironkernel.executablePath` (release `IronKernel` binary
   or the `ik` global-tool shim, e.g. `~/.dotnet/tools/ik`)
2. `dotnet run --project IronKernel/IronKernel.fsproj --` when that project exists
   in the workspace (IronKernel development checkouts)
3. `IronKernel` (`IronKernel.exe` on Windows) on `PATH`

Step 3 does **not** look for `ik`. If you only installed the .NET tool, set
`ironkernel.executablePath` to the absolute path of the `ik` shim, or put a
release binary directory on `PATH`. See the
[getting-started guide](../../website/docs/getting-started.html#editor) for
install + settings examples.

Use `ironkernel.projectPath` when the .NET runtime project lives elsewhere in
the workspace. Use `ironkernel.ikprojPath` to pin an IronKernel `.ikproj` for
Run/Build Project; otherwise the extension walks up from the active file, then
searches the workspace (with a picker if several match).
Standalone release binaries must remain beside `kernel.ikr` and `promises.ikr`.
Set `ironkernel.profile` to `minimal`, `safe`, or `unrestricted` to control the
host authority available to editor commands and playground runs.

## Commands

- `IronKernel: Run Current File`
- `IronKernel: Check Current File` — `check <file.ikr> --json`, also run on save
- `IronKernel: Compile Current File to IKC`
- `IronKernel: Run Project` — `run <project.ikproj>` (plus `ironkernel.runArgs`)
- `IronKernel: Build Project` — `build <project.ikproj>` → `bin/*.ikc`
- `IronKernel: Open Playground`
- `IronKernel: Show Output`

Right-click a `.ikproj` in the explorer for Run/Build Project as well.

The playground executes arbitrary IronKernel and therefore arbitrary permitted
.NET operations. Execution is disabled in Restricted Mode. It uses direct
process argument arrays, never a command shell, and limits source size, output,
and execution time.

## `.ikr` association

`.ikr` is IronKernel's primary source extension and is registered automatically.
Legacy `.scm` files are intentionally not claimed because doing so conflicts
with Scheme tooling. To edit a legacy file as IronKernel, add:

```json
{
  "files.associations": {
    "*.scm": "ironkernel"
  }
}
```
