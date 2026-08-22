export interface ParsedDiagnostic {
  file: string;
  line: number;
  column: number;
  endColumn: number;
  message: string;
}

const headerPattern =
  /^(?:Script error|Compile error|Package error|Project error|Startup error|Test startup error|Build error|Check error):\s+(.+):(\d+):(\d+):\s+(.*)$/;

export interface CheckPosition {
  line: number;
  column: number;
}

export interface CheckRange {
  start: CheckPosition;
  end: CheckPosition;
}

export interface CheckLocation {
  file: string;
  range?: CheckRange;
}

export interface CheckDiagnostic extends CheckLocation {
  severity: string;
  message: string;
  related?: CheckLocation[];
}

function readPosition(value: unknown): CheckPosition | undefined {
  if (typeof value !== "object" || value === null) {
    return undefined;
  }
  const { line, column } = value as { line?: unknown; column?: unknown };
  if (typeof line !== "number" || typeof column !== "number" || line < 1 || column < 1) {
    return undefined;
  }
  return { line, column };
}

function readLocation(value: unknown): CheckLocation | undefined {
  if (typeof value !== "object" || value === null) {
    return undefined;
  }
  const entry = value as { file?: unknown; range?: unknown };
  if (typeof entry.file !== "string" || entry.file === "") {
    return undefined;
  }
  if (entry.range === undefined) {
    return { file: entry.file };
  }
  const range = entry.range as { start?: unknown; end?: unknown };
  const start = readPosition(range.start);
  const end = readPosition(range.end);
  if (!start || !end) {
    return undefined;
  }
  return { file: entry.file, range: { start, end } };
}

/**
 * Parses `ik check --json` output (a version-1 check report). Returns
 * undefined when stdout is not such a report, so callers can tell "clean"
 * from "the CLI never produced one".
 */
export function parseCheckReport(stdout: string): CheckDiagnostic[] | undefined {
  let parsed: unknown;
  try {
    parsed = JSON.parse(stdout);
  } catch {
    return undefined;
  }
  if (typeof parsed !== "object" || parsed === null) {
    return undefined;
  }
  const report = parsed as { version?: unknown; diagnostics?: unknown };
  if (report.version !== 1 || !Array.isArray(report.diagnostics)) {
    return undefined;
  }

  const diagnostics: CheckDiagnostic[] = [];
  for (const entry of report.diagnostics) {
    const location = readLocation(entry);
    if (!location) {
      continue;
    }
    const { severity, message, related } = entry as {
      severity?: unknown;
      message?: unknown;
      related?: unknown;
    };
    diagnostics.push({
      ...location,
      severity: typeof severity === "string" ? severity : "error",
      message: typeof message === "string" ? message : "IronKernel error",
      related: Array.isArray(related)
        ? related.map(readLocation).filter((value): value is CheckLocation => value !== undefined)
        : undefined
    });
  }
  return diagnostics;
}

export function parseDiagnostics(stderr: string): ParsedDiagnostic[] {
  const lines = stderr.replace(/\r\n/g, "\n").split("\n");
  const diagnostics: ParsedDiagnostic[] = [];

  for (let index = 0; index < lines.length; index += 1) {
    const line = lines[index] ?? "";
    const match = headerPattern.exec(line);
    if (!match) {
      continue;
    }

    const lineNumber = Number.parseInt(match[2] ?? "1", 10);
    const columnNumber = Number.parseInt(match[3] ?? "1", 10);
    const caretLine = lines[index + 2] ?? "";
    const caretMatch = /^(\s*)(\^+)/.exec(caretLine);
    const caretWidth = caretMatch?.[2]?.length ?? 1;

    diagnostics.push({
      file: match[1] ?? "",
      line: Math.max(0, lineNumber - 1),
      column: Math.max(0, columnNumber - 1),
      endColumn: Math.max(0, columnNumber - 1) + caretWidth,
      message: (match[4] ?? "IronKernel error").trim()
    });
  }

  return diagnostics;
}
