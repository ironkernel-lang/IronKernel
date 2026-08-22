# ADR 0009: Editor tooling grows from the runtime outward

Status: Accepted — phase 1 implemented

## Decision

Deepen the existing VS Code extension into runtime-backed tooling, in a fixed
order: structured diagnostics from the CLI first, environment enumeration
primitives second, an in-process language server third, parser error recovery
fourth, and the visible surfaces — environment inspector, profile status,
debug adapter — only on top of those. No separate IDE, and no language server
that shells out to the current text-scraping contract.

Phase 1 ships with this ADR: `ik check [--json]`, a machine-readable
diagnostics format, and the extension consuming it on save.

## Problem

The language has several concepts a generic editor cannot show — operatives vs
applicatives, first-class environments, capability profiles, compiled vs
residual paths — and the extension that exists is thinner than it looks:

- **Diagnostics are stderr scraping.** The extension regex-matches
  `Prefix error: file:line:col: message` and infers the end column by counting
  `^` characters two lines below (`editors/vscode/src/diagnostics.ts`) — it
  re-parses the caret art `showError` draws for humans. It fires only after an
  explicit run or compile; nothing analyzes a buffer on open, edit, or save.
  One emitter (`Project startup error:` in `Project.fs`) did not even match
  the regex; `Build error:` and `Test startup error:` did not either.
- **Operative/applicative coloring is a name list, maintained twice** — one
  regex alternation in `syntaxes/ironkernel.tmLanguage.json`, a second copy in
  `website/assets/site.js`. A user-defined operative gets no color; a shadowed
  `if` keeps one. The distinction is the language's primary mental model,
  rendered lexically.
- **`compile` catches parse errors only.** `Analyze.analyzeLocatedGuarded`
  returns a `CoreExpr`, not a `ThrowsError`; unbound variables and arity
  errors surface at run time. `ik build` on a typo'd name exits 0.
- **Environments are opaque to Kernel.** The host record is a plain
  `Dictionary` plus a parent list and a capability set (`Ast.fs`,
  `EnvironmentRecord`), but the only probe is `$binds?` and `showVal` prints
  `<environment>`. No frame enumeration, no parent walk, no capability read.
- **No session protocol.** The REPL is bare stdin/stdout; `trapError` folds
  errors into stdout as `error : …` text, so a consumer cannot separate
  results from failures without string-matching.
- **The parser is fail-fast.** FParsec reports the first failure with no
  partial tree, so a half-typed buffer yields one error and nothing to
  complete against.

## What already exists to build on

These are the reasons the plan starts at the runtime rather than at the
protocol:

- `IronKernel/IronKernel.fsproj` is deliberately exe-and-library, so a server
  can call `Parser`, `Analyze`, `Emit`, and `Project.load` in-process — no
  process spawn per keystroke, no output parsing.
- Span data is real end-to-end for errors: `Parser.readLocatedExprList`
  returns a fully-spanned tree, `CLocated` carries spans through the IR, and
  `LocatedError` carries them out. What was missing was a machine format, not
  the data.
- `contract-of` returns `(mode operands result effect trust)` for primitives
  and contracted combiners — hover, signature help, and *semantic*
  operative/applicative classification, nearly for free.
- The `.ikproj` model plus `orderedSources`/`orderedTestSources` already
  defines a workspace and its load order.
- `Mono.Terminal`'s completion hook (`AutoCompleteEvent`) exists and is
  unused; REPL tab-completion is wiring, once bindings are enumerable.

## Plan

**Phase 1 — structured diagnostics.** *Done.* `ik check [--json]
[<file.ikr> | project.ikproj]` parses and analyzes without evaluating or
writing anything — by construction it is `compile` minus the write
(`Emit.checkSourceFileForProfile`), so any semantic checking later added to
the analyze path flows into editors with no further work. Exit codes: 0
clean, 1 findings, 2 usage. The JSON is a versioned contract:

```json
{"version": 1, "diagnostics": [{
  "severity": "error", "message": "…", "file": "…",
  "range": {"start": {"line": 1, "column": 5}, "end": {"line": 1, "column": 9}},
  "related": [{"file": "…", "range": {…}}]
}]}
```

Lines and columns are 1-based to match the human diagnostics; `end` is
exclusive; a finding without a span (an unreadable file) carries `file` and no
`range`; nested `LocatedError` wrappers become the innermost span as the
primary location with the enclosing spans under `related`. `showError` was
split into `errorLocations`/`errorMessage` so both renderings share one
traversal — its human output is unchanged. Project check walks sources, main,
and tests (not dependency sources, which are published artifacts and not this
project's to fix), and does not require a restore.

The extension now runs `check --json` on save (`ironkernel.checkOnSave`,
default on, trusted workspaces only) and via **Check Current File**,
publishing span-accurate diagnostics instead of scraping. The caret-art regex
remains only for what `run` prints — runtime errors have no JSON channel yet —
and the three mismatched prefixes are fixed or matched.

**Phase 2 — environment enumeration.** Primitives to list a frame's bindings,
walk `parents`, and read the capability set, over the existing `SymbolTable`
machinery. This one gap blocks completion, the environment inspector, and
REPL tab-completion all at once, which is why it precedes the server.

**Phase 3 — the language server.** F#, referencing IronKernel in-process.
Semantic tokens from actual binding resolution and `contract-of` — retiring
both hand-maintained name lists — hover and signature help from contracts,
completion from phase 2, diagnostics from phase 1's pipeline. Ships with
marketplace publishing, which CI has already reduced to a decision
(`vsce package` runs on every push; the `.vsix` is an artifact nobody
publishes).

**Phase 4 — parser error recovery.** A first failure with no partial tree is
acceptable for check-on-save and fatal for as-you-type diagnostics and
mid-edit completion. This is the largest single piece and nothing above
depends on it, which is why it is fourth and not first.

**Phase 5 — the visible surfaces.** Environment inspector (a UI over phase
2), a profile status-bar item that also reads the project's own `<Profile>`,
compiled-vs-residual highlighting (the IR's `CLocated` forms already mark
what the analyzer touched).

**Phase 6 — debug adapter.** Requires a persistent session protocol that does
not exist — the REPL cannot even separate errors from values today — so the
protocol is the prerequisite, and it should serve the inspector and
remote-eval too, not just the DAP.

## Alternatives

**A separate IDE.** What Racket, Elixir, and Gleam did instead — deepen the
extension/LSP surface — worked, and this project's size makes a second binary
a distraction. Rejected.

**LSP first, wrapping the CLI.** An LSP speaking to `ik` over stdout would
inherit the caret-scraping contract and pay a process spawn per request. The
enablers are in the runtime; the protocol layer is the easy part. Rejected as
an ordering, not as a goal.

**Growing the TextMate name lists (or tree-sitter).** Any lexical approach
keeps the two hand-maintained operative/applicative lists and still cannot
color a user-defined operative, because operative-ness is a property of the
bound value, not the text. Semantic tokens from the server obsolete both
lists. Rejected.

**Debug adapter early.** "Harder, high value" understates the gap: there is
no session protocol at all. Building the DAP first would force one into
existence in DAP's shape rather than a shape the inspector and playground can
share. Deferred, not rejected.

**A single unversioned JSON blob.** The `version` field costs one property
and makes the day the format changes a negotiation instead of a breakage.

## Consequences

The JSON format is now a contract with an external consumer; changes go
through the version field. `check` is defined as `compile` minus the write,
so the two cannot drift — and when the analyzer learns to reject unbound
variables at compile time, every editor gets it the same day. The stderr
regex is demoted to a fallback for runtime errors and can retire when a
structured channel exists for `run`.

The phases after 1 are ordered by what they unblock, not by visibility: the
flashy items (inspector, DAP) are deliberately last because each is a thin
view over a capability the runtime does not yet expose. The temptation to
reorder toward visibility is the failure mode this ADR exists to record.
