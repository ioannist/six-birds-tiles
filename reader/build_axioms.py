#!/usr/bin/env python3
"""T1/T1n: obtain fresh axiom output after a Lean build and compare supplied records."""
import difflib
import re
import subprocess
from pathlib import Path

from check_package import check


def main():
    root = Path(__file__).resolve().parents[1]
    # Python experiments and lake build may have refreshed their own reports.
    # Every source, canonical input and immutable supplied snapshot is still checked.
    check(root, allow_runtime_reports=True)
    project = root / "lean/R44"
    supplied = (root / "reader/supplied_build_axioms.log").read_text()
    declarations = re.findall(r"^'([^']+)' (?:depends|does not depend)", supplied, re.M)
    if not declarations:
        raise ValueError("empty supplied axiom list")
    source = "import R44\n" + "".join(f"#print axioms {name}\n" for name in declarations)
    target = project / "ReaderFreshAxioms.lean"
    if target.exists():
        raise FileExistsError(target)
    try:
        target.write_text(source)
        proc = subprocess.run(["lake", "env", "lean", "-j", "4", target.name],
                              cwd=project, text=True, capture_output=True)
    finally:
        target.unlink()
    output = proc.stdout + proc.stderr
    (root / "reader/fresh_axioms.log").write_text(output)
    if proc.returncode:
        raise RuntimeError(output)
    normalize = lambda s: re.sub(r"\s+", " ", s).strip()
    pattern = r"'[^']+' (?:depends on axioms: \[[^]]*\]|does not depend on any axioms)"
    old = [normalize(s) for s in re.findall(pattern, supplied, re.S)]
    new = [normalize(s) for s in re.findall(pattern, output, re.S)]
    diff = "".join(difflib.unified_diff([s+"\n" for s in old], [s+"\n" for s in new],
                                        fromfile="supplied", tofile="fresh"))
    (root / "reader/fresh_axioms.diff").write_text(diff)
    print(diff or "T1/T1n supplied/fresh axiom blocks match")
    if old != new:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
