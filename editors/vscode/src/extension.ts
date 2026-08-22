import * as path from "node:path";
import * as vscode from "vscode";
import { resolveRuntime, runProcess, type RuntimeCommand } from "./cli.js";
import {
  parseCheckReport,
  parseDiagnostics,
  type CheckDiagnostic,
  type CheckLocation
} from "./diagnostics.js";
import { PlaygroundPanel } from "./playgroundPanel.js";
import { findIkprojWalkingUp, isIkprojPath, rankIkProjects } from "./projects.js";

const timeoutMs = 120000;

export function activate(context: vscode.ExtensionContext): void {
  const output = vscode.window.createOutputChannel("IronKernel");
  const diagnostics = vscode.languages.createDiagnosticCollection("ironkernel");
  context.subscriptions.push(output, diagnostics);

  context.subscriptions.push(
    vscode.commands.registerCommand("ironkernel.showOutput", () => output.show()),
    vscode.commands.registerCommand("ironkernel.openPlayground", () => {
      PlaygroundPanel.createOrShow(context, output);
    }),
    vscode.commands.registerCommand("ironkernel.checkFile", async () => {
      const document = await activeIronKernelDocument();
      if (document) {
        await runCheck(document, output, diagnostics);
      }
    }),
    vscode.workspace.onDidSaveTextDocument((document) => {
      if (
        document.languageId === "ironkernel" &&
        vscode.workspace.isTrusted &&
        vscode.workspace
          .getConfiguration("ironkernel", document.uri)
          .get<boolean>("checkOnSave", true)
      ) {
        void runCheck(document, output, diagnostics);
      }
    }),
    vscode.commands.registerCommand("ironkernel.runFile", async () => {
      const document = await activeIronKernelDocument();
      if (document) {
        const args = vscode.workspace
          .getConfiguration("ironkernel", document.uri)
          .get<string[]>("runArgs", []);
        await executeCli(
          document.uri,
          ["run", document.uri.fsPath, ...args],
          "Running IronKernel file",
          output,
          diagnostics
        );
      }
    }),
    vscode.commands.registerCommand("ironkernel.compileFile", async () => {
      const document = await activeIronKernelDocument();
      if (document) {
        const parsed = path.parse(document.uri.fsPath);
        const outputPath = path.join(parsed.dir, `${parsed.name}.ikc`);
        await executeCli(
          document.uri,
          ["compile", document.uri.fsPath, "-o", outputPath],
          "Compiling IronKernel file",
          output,
          diagnostics
        );
      }
    }),
    vscode.commands.registerCommand("ironkernel.runProject", async (resource?: vscode.Uri) => {
      const projectPath = await resolveIkProject(resource);
      if (!projectPath) {
        return;
      }
      const configuration = vscode.workspace.getConfiguration(
        "ironkernel",
        vscode.Uri.file(projectPath)
      );
      const args = configuration.get<string[]>("runArgs", []);
      await saveIronKernelDocumentsNear(projectPath);
      await executeCli(
        vscode.Uri.file(projectPath),
        ["run", projectPath, ...args],
        "Running IronKernel project",
        output,
        diagnostics
      );
    }),
    vscode.commands.registerCommand("ironkernel.buildProject", async (resource?: vscode.Uri) => {
      const projectPath = await resolveIkProject(resource);
      if (!projectPath) {
        return;
      }
      await saveIronKernelDocumentsNear(projectPath);
      await executeCli(
        vscode.Uri.file(projectPath),
        ["build", projectPath],
        "Building IronKernel project",
        output,
        diagnostics
      );
    })
  );
}

async function requireTrustedWorkspace(): Promise<boolean> {
  if (vscode.workspace.isTrusted) {
    return true;
  }
  void vscode.window.showWarningMessage(
    "Trust this workspace before executing IronKernel code."
  );
  return false;
}

async function activeIronKernelDocument(): Promise<vscode.TextDocument | undefined> {
  if (!(await requireTrustedWorkspace())) {
    return undefined;
  }

  const document = vscode.window.activeTextEditor?.document;
  if (!document || document.languageId !== "ironkernel") {
    void vscode.window.showInformationMessage("Open an IronKernel source file first.");
    return undefined;
  }
  if (document.isUntitled) {
    void vscode.window.showInformationMessage("Save the IronKernel file before running it.");
    return undefined;
  }
  if (document.isDirty && !(await document.save())) {
    return undefined;
  }
  return document;
}

async function resolveIkProject(resource?: vscode.Uri): Promise<string | undefined> {
  if (!(await requireTrustedWorkspace())) {
    return undefined;
  }

  if (resource && isIkprojPath(resource.fsPath)) {
    return resource.fsPath;
  }

  const activeUri = vscode.window.activeTextEditor?.document.uri;
  const configuration = vscode.workspace.getConfiguration("ironkernel", activeUri);
  const configured = configuration.get<string>("ikprojPath", "").trim();
  if (configured !== "") {
    const folder = activeUri
      ? vscode.workspace.getWorkspaceFolder(activeUri)
      : vscode.workspace.workspaceFolders?.[0];
    const resolved = path.isAbsolute(configured)
      ? configured
      : path.resolve(folder?.uri.fsPath ?? process.cwd(), configured);
    return resolved;
  }

  if (activeUri && isIkprojPath(activeUri.fsPath)) {
    return activeUri.fsPath;
  }

  if (activeUri && !activeUri.scheme.startsWith("untitled")) {
    const nearest = await findIkprojWalkingUp(activeUri.fsPath);
    if (nearest) {
      return nearest;
    }
  }

  const found = await vscode.workspace.findFiles(
    "**/*.ikproj",
    "**/{node_modules,bin,obj,.git,dist}/**",
    50
  );
  const projects = rankIkProjects(
    activeUri?.fsPath,
    found.map((uri) => uri.fsPath)
  );

  if (projects.length === 0) {
    void vscode.window.showInformationMessage(
      "No .ikproj file found in this workspace. Open one or set ironkernel.ikprojPath."
    );
    return undefined;
  }

  if (projects.length === 1) {
    return projects[0];
  }

  const items = projects.map((projectPath) => ({
    label: path.basename(projectPath),
    description: vscode.workspace.asRelativePath(projectPath),
    projectPath
  }));
  const picked = await vscode.window.showQuickPick(items, {
    placeHolder: "Select an IronKernel project (.ikproj)"
  });
  return picked?.projectPath;
}

async function saveIronKernelDocumentsNear(projectPath: string): Promise<void> {
  const root = path.dirname(projectPath);
  for (const document of vscode.workspace.textDocuments) {
    if (
      document.languageId === "ironkernel" &&
      document.isDirty &&
      !document.isUntitled &&
      document.uri.fsPath.startsWith(root + path.sep)
    ) {
      await document.save();
    }
  }
}

async function resolveConfiguredRuntime(
  scopeUri: vscode.Uri,
  output: vscode.OutputChannel
): Promise<{ runtime: RuntimeCommand; maxOutputBytes: number } | undefined> {
  const folder = vscode.workspace.getWorkspaceFolder(scopeUri);
  const configuration = vscode.workspace.getConfiguration("ironkernel", scopeUri);
  let runtime: RuntimeCommand;
  try {
    runtime = await resolveRuntime(
      folder?.uri.fsPath ?? vscode.workspace.workspaceFolders?.[0]?.uri.fsPath,
      configuration.get<string>("executablePath", ""),
      configuration.get<string>("projectPath", "IronKernel/IronKernel.fsproj")
    );
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    output.appendLine(`[launch failed] ${message}`);
    void vscode.window.showErrorMessage(`Unable to resolve IronKernel: ${message}`);
    return undefined;
  }
  const profile = configuration.get<string>("profile", "unrestricted");
  return {
    runtime: {
      ...runtime,
      prefixArgs: [...runtime.prefixArgs, "--profile", profile]
    },
    maxOutputBytes: configuration.get<number>("maxOutputBytes", 1024 * 1024)
  };
}

const checksInFlight = new Map<string, AbortController>();

async function runCheck(
  document: vscode.TextDocument,
  output: vscode.OutputChannel,
  collection: vscode.DiagnosticCollection
): Promise<void> {
  const resolved = await resolveConfiguredRuntime(document.uri, output);
  if (!resolved) {
    return;
  }
  const key = document.uri.toString();
  checksInFlight.get(key)?.abort();
  const controller = new AbortController();
  checksInFlight.set(key, controller);
  try {
    const result = await runProcess(
      resolved.runtime,
      ["check", document.uri.fsPath, "--json"],
      {
        timeoutMs,
        maxOutputBytes: resolved.maxOutputBytes,
        signal: controller.signal
      }
    );
    if (result.cancelled) {
      return;
    }
    const report = parseCheckReport(result.stdout);
    if (report === undefined) {
      output.appendLine(`[check produced no report; exit ${result.exitCode ?? "unknown"}]`);
      if (result.stderr) {
        output.append(result.stderr);
      }
      return;
    }
    publishCheckDiagnostics(document.uri, report, collection);
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    output.appendLine(`[check failed] ${message}`);
  } finally {
    if (checksInFlight.get(key) === controller) {
      checksInFlight.delete(key);
    }
  }
}

function toRange(location: CheckLocation): vscode.Range {
  if (!location.range) {
    return new vscode.Range(0, 0, 0, 1);
  }
  const startLine = location.range.start.line - 1;
  const startColumn = location.range.start.column - 1;
  let endLine = location.range.end.line - 1;
  let endColumn = location.range.end.column - 1;
  if (endLine < startLine || (endLine === startLine && endColumn <= startColumn)) {
    endLine = startLine;
    endColumn = startColumn + 1;
  }
  return new vscode.Range(startLine, startColumn, endLine, endColumn);
}

function publishCheckDiagnostics(
  checkedUri: vscode.Uri,
  report: CheckDiagnostic[],
  collection: vscode.DiagnosticCollection
): void {
  const byDocument = new Map<string, vscode.Diagnostic[]>();
  // A clean report must still overwrite the checked file's stale entries.
  byDocument.set(checkedUri.toString(), []);
  for (const entry of report) {
    const uri = vscode.Uri.file(entry.file);
    const diagnostic = new vscode.Diagnostic(
      toRange(entry),
      entry.message,
      vscode.DiagnosticSeverity.Error
    );
    diagnostic.source = "IronKernel";
    if (entry.related && entry.related.length > 0) {
      diagnostic.relatedInformation = entry.related.map(
        (location) =>
          new vscode.DiagnosticRelatedInformation(
            new vscode.Location(vscode.Uri.file(location.file), toRange(location)),
            "in this enclosing form"
          )
      );
    }
    const key = uri.toString();
    const values = byDocument.get(key) ?? [];
    values.push(diagnostic);
    byDocument.set(key, values);
  }
  for (const [key, values] of byDocument) {
    collection.set(vscode.Uri.parse(key), values);
  }
}

async function executeCli(
  scopeUri: vscode.Uri,
  args: string[],
  title: string,
  output: vscode.OutputChannel,
  collection: vscode.DiagnosticCollection
): Promise<void> {
  const resolved = await resolveConfiguredRuntime(scopeUri, output);
  if (!resolved) {
    return;
  }
  const { runtime, maxOutputBytes } = resolved;
  collection.clear();
  output.show(true);
  output.appendLine(`> ${runtime.command} ${[...runtime.prefixArgs, ...args].join(" ")}`);

  await vscode.window.withProgress(
    {
      location: vscode.ProgressLocation.Notification,
      title,
      cancellable: true
    },
    async (_progress, token) => {
      const controller = new AbortController();
      const cancellation = token.onCancellationRequested(() => controller.abort());
      try {
        const result = await runProcess(runtime, args, {
          timeoutMs,
          maxOutputBytes,
          signal: controller.signal
        });
        if (result.stdout) {
          output.append(result.stdout);
        }
        if (result.stderr) {
          output.append(result.stderr);
        }
        output.appendLine(
          `\n[exit ${result.exitCode ?? "unknown"}${result.cancelled ? ", cancelled" : ""}]`
        );
        publishDiagnostics(result.stderr, collection);
        if (result.exitCode === 0 && !result.cancelled) {
          if (args[0] === "build") {
            void vscode.window.showInformationMessage("IronKernel project built.");
          }
        } else if (result.exitCode !== 0 && !result.cancelled) {
          void vscode.window.showErrorMessage("IronKernel reported an error.");
        }
      } catch (error) {
        const message = error instanceof Error ? error.message : String(error);
        output.appendLine(`[launch failed] ${message}`);
        void vscode.window.showErrorMessage(`Unable to launch IronKernel: ${message}`);
      } finally {
        cancellation.dispose();
      }
    }
  );
}

function publishDiagnostics(
  stderr: string,
  collection: vscode.DiagnosticCollection
): void {
  const byDocument = new Map<string, vscode.Diagnostic[]>();
  for (const parsed of parseDiagnostics(stderr)) {
    const uri = vscode.Uri.file(parsed.file);
    const diagnostic = new vscode.Diagnostic(
      new vscode.Range(
        parsed.line,
        parsed.column,
        parsed.line,
        Math.max(parsed.column + 1, parsed.endColumn)
      ),
      parsed.message,
      vscode.DiagnosticSeverity.Error
    );
    diagnostic.source = "IronKernel";
    const key = uri.toString();
    const values = byDocument.get(key) ?? [];
    values.push(diagnostic);
    byDocument.set(key, values);
  }
  for (const [uri, values] of byDocument) {
    collection.set(vscode.Uri.parse(uri), values);
  }
}

export function deactivate(): void {
  // Resources registered in ExtensionContext are disposed by VS Code.
}
