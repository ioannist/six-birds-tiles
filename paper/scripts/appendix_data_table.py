#!/usr/bin/env python3
"""Table 6 (FIGURES.md): input hashes and tool versions. sha256 of the canonical inputs is
computed live from the working tree (they are unchanged since the pin; the replay asserts the
same values); Lean and Mathlib versions are read at the pinned commit; the replay time is read
from verify/replay_report.json. Re-run at freeze."""
import argparse
import hashlib
import json
import os
import platform

from _texutil import ROOT, common_args, finish, git_show, pathtt, tex, write_rows

INPUTS = [
    "solid/r44_solid.json",
    "solid/native_panels.csv",
    "certificates/candidate_certificate.json",
    "certificates/companion_collision_certificate.json",
    "certificates/collision_core_witnesses.jsonl.gz",
]


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    ap = common_args(argparse.ArgumentParser(description=__doc__))
    args = ap.parse_args()
    rows = []
    for p in INPUTS:
        digest = sha(os.path.join(ROOT, p))
        rows.append([pathtt(p), r"\texttt{" + digest[:16] + r"\dots{}" + digest[-8:] + "}"])
    toolchain = git_show(args.commit, "lean/R44/lean-toolchain").strip()
    manifest = json.loads(git_show(args.commit, "lean/R44/lake-manifest.json"))
    revs = {p["name"]: p.get("rev", "")[:12] for p in manifest["packages"]}
    rows.append(["Lean toolchain", r"\texttt{" + tex(toolchain) + "}"])
    rows.append(["Mathlib commit", r"\texttt{" + tex(revs.get("mathlib", "?")) + "}"])
    rows.append(["batteries / aesop / Qq / proofwidgets",
                 r"\texttt{" + ", ".join(tex(revs.get(k, "?")) for k in ("batteries", "aesop", "Qq", "proofwidgets")) + "}"])
    rep_path = os.path.join(ROOT, "verify", "replay_report.json")
    if os.path.exists(rep_path):
        rep = json.load(open(rep_path, encoding="utf-8"))
        rows.append([pathtt("verify/replay.py") + " (Python standard library)",
                     f"{tex(rep.get('status', '?'))}, {rep.get('seconds', '?')} s"])
        replay_ok = all(rep["canonical_sha256"].get(p, sha(os.path.join(ROOT, p))) == sha(os.path.join(ROOT, p))
                        for p in rep["canonical_sha256"])
    else:
        replay_ok = True
    rows.append(["Python (replay and tables)", tex(platform.python_version())])
    write_rows(args.out, "appendix_data_table", rows,
               f"sha256 computed live; Lean versions at {args.commit}",
               colspec="L{0.42\\linewidth} L{0.5\\linewidth}", header=["artifact", "sha256 / version"])
    finish(replay_ok, "replay report hashes disagree with the working tree")


if __name__ == "__main__":
    main()
