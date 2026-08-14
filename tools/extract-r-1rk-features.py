#!/usr/bin/env python3
"""Extract the feature manifest for the Kernel Revised-1 Report (R-1RK).

The report is not in this repository; it is John N. Shutt's WPI technical
report 05-07, "Revised-1 Report on the Kernel Programming Language":

    https://ftp.cs.wpi.edu/pub/techreports/pdf/05-07.pdf

Usage:
    pdftotext -layout 05-07.pdf r-1rk.txt
    python3 tools/extract-r-1rk-features.py r-1rk.txt docs/kernel-r-1rk-features.json

The report's table of contents is the authority for what a conformance matrix
must cover. Each numbered entry is either a feature entry naming one or more
bindings ("12.5.1 number?, finite?, integer?") or a prose subsection ("12.3.2
Exact real numbers"). Modules the report marks "(optional)" are flagged, since
an implementation may omit them and still conform.
"""
import json
import re
import sys


def extract(text):
    lines = text.split("\n")
    start = next(i for i, l in enumerate(lines) if re.match(r"^0 Introduction", l.strip()))
    end = next(i for i, l in enumerate(lines)
               if i > start + 50 and re.match(r"^\s*0\s+Introduction\s*$", l))

    chapters, sections, entries = {}, {}, []
    for line in lines[start:end]:
        s = line.rstrip()
        if not s.strip():
            continue
        m = re.match(r"^\s*(\d+)\s+([A-Z][^.]*?)\s+(\d+)\s*$", s)
        if m:
            chapters[m.group(1)] = m.group(2).strip()
            continue
        m = re.match(r"^\s*(\d+\.\d+)\s+(.+?)\s*\.\s*\.[\s.]*\d+\s*$", s)
        if m:
            sections[m.group(1)] = m.group(2).strip()
            continue
        m = re.match(r"^\s*(\d+\.\d+\.\d+)\s+(.+?)\s*\.\s*\.[\s.]*\d+\s*$", s)
        if m:
            number, title = m.group(1), m.group(2).strip()
            parts = [p.strip() for p in title.split(",") if p.strip()]
            # A feature entry names bindings; a prose subsection is a capitalised phrase.
            is_binding = all(" " not in p for p in parts) and not re.match(r"^[A-Z]", title)
            entries.append({
                "entry": number,
                "title": title,
                "bindings": parts if is_binding else [],
            })

    manifest = []
    for e in entries:
        if not e["bindings"]:
            continue
        chapter, section = e["entry"].split(".")[0], ".".join(e["entry"].split(".")[:2])
        section_title = sections.get(section, "")
        manifest.append({
            "entry": e["entry"],
            "chapter": chapter,
            "chapterTitle": chapters.get(chapter, ""),
            "section": section,
            "sectionTitle": section_title,
            "title": e["title"],
            "bindings": e["bindings"],
            "optional": "(optional)" in section_title.lower(),
        })
    return manifest


def main():
    source, target = sys.argv[1], sys.argv[2]
    with open(source, encoding="utf-8", errors="replace") as handle:
        manifest = extract(handle.read())
    with open(target, "w", encoding="utf-8") as handle:
        json.dump({
            "report": "Revised-1 Report on the Kernel Programming Language (WPI TR 05-07)",
            "reportUrl": "https://ftp.cs.wpi.edu/pub/techreports/pdf/05-07.pdf",
            "entries": manifest,
        }, handle, indent=2)
        handle.write("\n")
    print(f"{len(manifest)} feature entries, "
          f"{len({b for e in manifest for b in e['bindings']})} distinct bindings")


if __name__ == "__main__":
    main()
