#!/usr/bin/env python3
"""Generate a standalone, output-free notebook from reviewable Python sources."""
import argparse
import json
from pathlib import Path
import sys

import jupytext

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    text = (ROOT / "notebook/r44_notebook.py").read_text()
    runtime = (ROOT / "notebook/runtime.py").read_text()
    pin = json.loads((ROOT / "reader/pin.json").read_text())
    evidence = json.loads((ROOT / "reader/generated/claim_map.json").read_text())
    if evidence["source_commit"] != pin["source_commit"]:
        raise ValueError("Evidence map source pin differs")
    text = text.replace("from runtime import Session", runtime)
    text = text.replace("PIN = {}  # R44_PIN", "PIN = " + repr(pin))
    text = text.replace("CLAIM_MAP = {}  # R44_CLAIM_MAP", "CLAIM_MAP = " + repr(evidence))
    nb = jupytext.reads(text, fmt="py:percent")
    nb.metadata["colab"] = {"name": "Chair44 (R44) — run it yourself", "provenance": []}
    for i, cell in enumerate(nb.cells):
        cell["id"] = f"r44-{i:02}"
        if cell.cell_type == "code":
            cell.outputs = []
            cell.execution_count = None
            cell.metadata["jupyter"] = {"source_hidden": True}
            cell.metadata["cellView"] = "form"
    result = jupytext.writes(nb, fmt="ipynb")
    target = ROOT / "notebook/r44_notebook.ipynb"
    if args.check:
        if target.read_text() != result:
            sys.exit("Notebook differs from its Python sources; run notebook/build.py")
    else:
        target.write_text(result)
    print("STATUS: PASS (standalone notebook; outputs cleared)")


if __name__ == "__main__":
    main()
