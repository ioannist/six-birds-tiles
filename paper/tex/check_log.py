#!/usr/bin/env python3
"""WRITING_PLAN.md step 10 completion bar, checked mechanically from main.log:
no undefined references, no missing citations, no overfull box above 10pt.
Exit 1 with the offending lines if any bar fails."""
import re
import sys

LOG = sys.argv[1] if len(sys.argv) > 1 else "main.log"
text = open(LOG, encoding="utf-8", errors="replace").read()
bad = []
for m in re.finditer(r"LaTeX Warning: (Reference|Citation) `[^']*' .*undefined", text):
    bad.append(m.group(0))
if "There were undefined references" in text:
    bad.append("There were undefined references")
if "There were undefined citations" in text:
    bad.append("There were undefined citations")
for m in re.finditer(r"^Overfull \\[hv]box \(([0-9.]+)pt too (?:wide|high)\)[^\n]*", text, re.M):
    if float(m.group(1)) > 10.0:
        bad.append(m.group(0))
for m in re.finditer(r"LaTeX Warning: Float too large for page by ([0-9.]+)pt[^\n]*", text):
    bad.append(m.group(0))
for m in re.finditer(r"LaTeX Warning: (?:Label|Reference) `[^']*' multiply defined[^\n]*", text):
    bad.append(m.group(0))
if bad:
    print("check: FAIL")
    for b in bad:
        print("  " + b)
    sys.exit(1)
print("check: PASS (no undefined references, no missing citations, no overfull box above 10pt, no oversized float, no duplicate label)")
