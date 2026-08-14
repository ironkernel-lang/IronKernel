#!/usr/bin/env python3
"""Run each expression in its own process and classify how it fails.

Usage:
    dotnet build IronKernel.sln -c Release
    python3 tools/scan-clr-faults.py \\
        IronKernel/bin/Release/net10.0/IronKernel tools/clr-fault-cases.txt

A primitive that lets a CLR exception escape aborts the whole process, so the
failure cannot be caught, reported with a source span, or survived by the REPL.
Three such faults were found and fixed by hand before this scan existed
(division by zero, arithmetic overflow, file I/O); it exists so the next one is
found by running it rather than by a user hitting it.

A Kernel error is fine. What this looks for is a CLR exception escaping the
evaluator, which aborts the process and takes the REPL or script host with it.
"""
import os
import subprocess
import sys
import tempfile

BIN = sys.argv[1]
CASES = [line.rstrip("\n") for line in open(sys.argv[2], encoding="utf-8") if line.strip()]

faults, errors, values = [], [], []
for case in CASES:
    with tempfile.NamedTemporaryFile("w", suffix=".ikr", delete=False, encoding="utf-8") as handle:
        handle.write('(. System.Console WriteLine "start")\n')
        handle.write("(. System.Console WriteLine %s)\n" % case)
        path = handle.name
    try:
        done = subprocess.run([BIN, path], capture_output=True, timeout=60)
        out = (done.stdout + done.stderr).decode("utf-8", "replace")
        if done.returncode not in (0, 1) or "Unhandled exception" in out:
            faults.append((case, out.strip().split("\n")[-1][:80], done.returncode))
        elif "Script error" in out:
            errors.append(case)
        else:
            values.append(case)
    except subprocess.TimeoutExpired:
        faults.append((case, "TIMEOUT", None))
    finally:
        os.unlink(path)

print(f"faulted (process aborted): {len(faults)}")
for case, detail, code in faults:
    print(f"   FAULT  {case}\n          -> exit={code} {detail}")
print(f"signalled a Kernel error : {len(errors)}")
print(f"returned a value         : {len(values)}")
