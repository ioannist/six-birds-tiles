#!/usr/bin/env python3
"""T2 byte-identity checks for the extracted reader package (stdlib)."""
import hashlib
import json
from pathlib import Path


# These files are outputs of documented reader commands, never mathematical inputs.
RUNTIME_REPORTS = frozenset({
    "verify/replay_report.json",
    "verify/packets/r44_unrestricted_alignment/results/mutation_controls.json",
    "lean/R44/build_axioms.log",
})


def check(root, allow_runtime_reports=False):
    manifest = json.loads((root / "reader/package_manifest.json").read_text())
    print("T2 source commit:", manifest["source_commit"])
    for name, expected in manifest["canonical_sha256"].items():
        actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"canonical digest mismatch: {name}")
        print("T2", actual, name)
    for name, expected in manifest["files_sha256"].items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != expected:
            if allow_runtime_reports and name in RUNTIME_REPORTS:
                print("T2 changed runtime report (not a source input):", name)
                continue
            raise ValueError(f"package digest mismatch: {name}")
    print("T2 STATUS: PASS (byte identity only; unsigned manifest)")
    return manifest


if __name__ == "__main__":
    check(Path(__file__).resolve().parents[1])
