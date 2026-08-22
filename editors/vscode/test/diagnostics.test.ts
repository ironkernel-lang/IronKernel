import { describe, expect, it } from "vitest";
import { parseCheckReport, parseDiagnostics } from "../src/diagnostics.js";

describe("parseDiagnostics", () => {
  it("parses a ranged Unix diagnostic", () => {
    const diagnostics = parseDiagnostics(
      "Script error: /work/demo.ikr:2:3: Getting an unbound variable: 'missing'\n" +
        "  (missing 42)\n" +
        "  ^^^^^^^^^^^^\n"
    );

    expect(diagnostics).toEqual([
      {
        file: "/work/demo.ikr",
        line: 1,
        column: 2,
        endColumn: 14,
        message: "Getting an unbound variable: 'missing'"
      }
    ]);
  });

  it("parses Windows drive letters from the right-hand position fields", () => {
    const [diagnostic] = parseDiagnostics(
      "Compile error: C:\\source\\demo.ikr:10:4: Parse error: Expecting ')'\n"
    );

    expect(diagnostic?.file).toBe("C:\\source\\demo.ikr");
    expect(diagnostic?.line).toBe(9);
    expect(diagnostic?.column).toBe(3);
    expect(diagnostic?.endColumn).toBe(4);
  });

  it("parses Project error diagnostics", () => {
    const [diagnostic] = parseDiagnostics(
      "Project error: /work/app/src/main.ikr:1:1: Getting an unbound variable: 'x'\n"
    );
    expect(diagnostic?.file).toBe("/work/app/src/main.ikr");
    expect(diagnostic?.message).toBe("Getting an unbound variable: 'x'");
  });

  it("ignores unrelated output", () => {
    expect(parseDiagnostics("Hello,world!\n")).toEqual([]);
  });
});

describe("parseCheckReport", () => {
  it("parses a version-1 report with ranges and related locations", () => {
    const report = parseCheckReport(
      JSON.stringify({
        version: 1,
        diagnostics: [
          {
            severity: "error",
            message: "Parse error: Expecting ')'",
            file: "/work/demo.ikr",
            range: { start: { line: 4, column: 1 }, end: { line: 4, column: 1 } },
            related: [
              {
                file: "/work/demo.ikr",
                range: { start: { line: 1, column: 1 }, end: { line: 4, column: 1 } }
              }
            ]
          }
        ]
      })
    );

    expect(report).toEqual([
      {
        severity: "error",
        message: "Parse error: Expecting ')'",
        file: "/work/demo.ikr",
        range: { start: { line: 4, column: 1 }, end: { line: 4, column: 1 } },
        related: [
          {
            file: "/work/demo.ikr",
            range: { start: { line: 1, column: 1 }, end: { line: 4, column: 1 } }
          }
        ]
      }
    ]);
  });

  it("keeps a rangeless diagnostic and distinguishes a clean report from garbage", () => {
    const clean = parseCheckReport('{"version":1,"diagnostics":[]}');
    expect(clean).toEqual([]);

    const rangeless = parseCheckReport(
      '{"version":1,"diagnostics":[{"severity":"error","message":"Failed to read","file":"/gone.ikr"}]}'
    );
    expect(rangeless).toEqual([
      { severity: "error", message: "Failed to read", file: "/gone.ikr", related: undefined }
    ]);

    expect(parseCheckReport("")).toBeUndefined();
    expect(parseCheckReport("Wrote demo.ikc\n")).toBeUndefined();
    expect(parseCheckReport('{"version":2,"diagnostics":[]}')).toBeUndefined();
  });

  it("drops malformed entries instead of failing the report", () => {
    const report = parseCheckReport(
      JSON.stringify({
        version: 1,
        diagnostics: [
          { severity: "error", message: "no file here" },
          {
            severity: "error",
            message: "bad range",
            file: "/work/demo.ikr",
            range: { start: { line: 0, column: 1 }, end: { line: 1, column: 1 } }
          },
          { severity: "error", message: "kept", file: "/work/demo.ikr" }
        ]
      })
    );
    expect(report?.map((entry) => entry.message)).toEqual(["kept"]);
  });
});
