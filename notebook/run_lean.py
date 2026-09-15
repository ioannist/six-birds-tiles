#!/usr/bin/env python3
"""Run the pinned Lean sources in a new, isolated directory; stdlib only.

No expensive work runs at container startup. Invoke this script explicitly.
The output receipt is unsigned and records only this process's execution.
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import io
import json
import platform
import shutil
import subprocess
import sys
import tarfile
import time
import zipfile
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath

PIN = "838bca514679b2531d31f4e0dfd66641269e2a8c"
MATHEMATICAL_BASELINE = "d90313a717994936f254990f88d2624bbcce5bcd"
CANONICAL = {
    "solid/r44_solid.json": "f320d7a0c2d784a3eb29f001dc035808f67591d9ea8d3dd45949e66442f0ed55",
    "certificates/candidate_certificate.json": "44e9b3f6048497de02d1be72d0c80ddc94aaaf235382138c7468ffdbc5de5ff2",
    "certificates/companion_collision_certificate.json": "36e89e2fe81f4788e7edea2a68fef013557e5b73f5a16ac76348fe241b068b08",
    "certificates/collision_core_witnesses.jsonl.gz": "ae64a5283400c61e15f4a8758d949f3ad8428645cb3691e0b5cdb539161f8a45",
}
# These seven delivery archives are inputs to the existing, unchanged
# scripts/discharge_diff_audit.sh. They contain proof sources, not review reports.
DELIVERIES = (
    "proof/external_lean/F1_exchange2/r44_F1_exchange2_discharge.zip",
    "proof/external_lean/F2_exchange3/r44_F2_exchange3_discharge.zip",
    "proof/external_lean/F3_exchange4/r44_F3_exchange4_discharge.zip",
    "proof/external_lean/F4_exchange5/r44_F4_exchange5_discharge.zip",
    "proof/external_lean/F5_exchange6/r44_exchange6_bridges.zip",
    "proof/external_lean/F6_exchange7/r44_exchange7_native_interpretation.zip",
    "proof/external_lean/r44_F1_complete_dihedral_list_draft.zip",
)
FORBIDDEN = {
    "TILE_DISCOVERY_THREAD.txt", ".codex", ".agents", "offgit", "history",
    "archive", ".lake", "review", "__pycache__",
}
STAGES = (
    "delivery_audit", "toolchain_install", "toolchain_version", "mathlib_cache",
    "build", "controls", "fresh_axioms",
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_path(name: str) -> PurePosixPath:
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts or FORBIDDEN.intersection(path.parts):
        raise ValueError(f"Excluded archive member: {name}")
    if "provenance/sbt_papers" in str(path):
        raise ValueError(f"Excluded archive member: {name}")
    return path


def export_source(repo: Path, destination: Path) -> dict[str, str]:
    """Select committed inputs before archive creation; never copy the worktree."""
    actual = subprocess.check_output(
        ["git", "-C", str(repo), "rev-parse", f"{PIN}^{{commit}}"], text=True
    ).strip()
    if actual != PIN:
        raise ValueError("Pinned source revision did not resolve exactly")
    names = subprocess.check_output(
        ["git", "-C", str(repo), "ls-tree", "-r", "--name-only", PIN, "lean/R44"],
        text=True,
    ).splitlines()
    selected = [name for name in names if not FORBIDDEN.intersection(PurePosixPath(name).parts)]
    selected += list(CANONICAL) + list(DELIVERIES)
    data = subprocess.check_output(
        ["git", "-C", str(repo), "archive", "--format=tar", PIN, "--", *selected]
    )
    destination.mkdir()
    # Manual extraction accepts only regular files/directories, including on
    # Python versions that predate tarfile's extraction filters.
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:") as archive:
        for member in archive:
            relative = safe_path(member.name)
            target = destination / relative
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
            elif member.isfile():
                target.parent.mkdir(parents=True, exist_ok=True)
                source = archive.extractfile(member)
                if source is None:
                    raise ValueError(f"Unreadable archive member: {member.name}")
                target.write_bytes(source.read())
                target.chmod(member.mode & 0o777)
            else:
                raise ValueError(f"Unsupported archive member type: {member.name}")
    digests = {name: sha256(destination / name) for name in CANONICAL}
    if digests != CANONICAL:
        raise ValueError(f"Canonical digest mismatch: {digests}")
    for name in DELIVERIES:
        with zipfile.ZipFile(destination / name) as delivery:
            for member in delivery.infolist():
                safe_path(member.filename)
    for item in destination.rglob("*"):
        safe_path(item.relative_to(destination).as_posix())
    return digests


def run_stage(name: str, command: list[str], cwd: Path, output: Path, receipt: dict) -> None:
    started = time.monotonic()
    log = output / f"{name}.log"
    step = {"name": name, "command": command, "log": log.name, "returncode": None}
    receipt["cells_executed"].append(step)
    print(f"Running {name}; live log: {log}", flush=True)
    try:
        with log.open("w") as stream:
            result = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
        step["returncode"] = result.returncode
        if result.returncode:
            raise RuntimeError(f"{name} failed (exit {result.returncode}); read {log}")
    finally:
        step["wall_seconds"] = round(time.monotonic() - started, 3)


def execute(repo: Path, output: Path, prepare_only: bool = False) -> int:
    # Refuse reuse so project oleans from a prior run cannot masquerade as a
    # fresh source build and no earlier receipt can be overwritten.
    output.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    receipt = {
        "commit": PIN,
        "mathematical_baseline": MATHEMATICAL_BASELINE,
        "canonical_sha256": {},
        "python": sys.version,
        "platform": platform.platform(),
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "tier": "T1/T1n, classified by each declaration's axiom set in fresh_axioms",
        "notice": "This utility adds no evidence for the theorem. This unsigned receipt records only this session's execution.",
        "replay_report": None,
        "replay_report_note": "Python replay is a separate notebook action and was not executed by this runner.",
        "cells_executed": [],
        "cells_skipped": [],
        "lean_ran": False,
        "status": "INCOMPLETE",
    }
    try:
        source = output / "source"
        receipt["canonical_sha256"] = export_source(repo, source)
        print(f"Commit: {PIN}", flush=True)
        for name, digest in receipt["canonical_sha256"].items():
            print(f"{digest}  {name}", flush=True)
        project = source / "lean/R44"
        supplied = output / "supplied_records"
        supplied.mkdir()
        receipt["supplied_records"] = {}
        for name in ("build_axioms.log", "negative_control.log"):
            shutil.copyfile(project / name, supplied / name)
            receipt["supplied_records"][name] = {"sha256": sha256(supplied / name), "status": "supplied record, not a fresh build"}
        # Test all seven historical delivery dependencies before any download.
        run_stage("delivery_audit", ["bash", "scripts/discharge_diff_audit.sh"], project, output, receipt)
        if prepare_only:
            receipt["status"] = "PREPARED_ONLY"
            return 0
        if not shutil.which("elan") or not shutil.which("lake"):
            raise RuntimeError("elan/lake unavailable; open the supplied devcontainer or install elan first (see notebook/LEAN.md)")
        toolchain = (project / "lean-toolchain").read_text().strip()
        receipt["lean_toolchain"] = toolchain
        run_stage("toolchain_install", ["elan", "toolchain", "install", toolchain], project, output, receipt)
        run_stage("toolchain_version", ["lake", "env", "lean", "--version"], project, output, receipt)
        run_stage("mathlib_cache", ["lake", "exe", "cache", "get"], project, output, receipt)
        run_stage("build", ["lake", "build"], project, output, receipt)
        run_stage("controls", ["bash", "scripts/controls.sh"], project, output, receipt)
        control_lines = [line for line in (output / "controls.log").read_text().splitlines() if line.startswith("CONTROLS:")]
        if len(control_lines) != 1 or not control_lines[0].startswith("CONTROLS: PASS "):
            raise RuntimeError("Controls exited zero without its unique CONTROLS: PASS summary")
        receipt["controls_summary"] = control_lines[0]
        # Axioms.lean's run_cmd writes exactly the dependency lists printed by
        # its #print axioms commands. Remove the build's copy before direct
        # elaboration, so the receipt requires this final audit to write anew.
        (project / "build_axioms.log").unlink(missing_ok=True)
        run_stage("fresh_axioms", ["lake", "env", "lean", "-j", "4", "R44/Axioms.lean"], project, output, receipt)
        fresh = (project / "build_axioms.log").read_text()
        if "'R44.r44_einstein' depends on axioms:" not in fresh:
            raise RuntimeError("Fresh axiom audit did not produce the final theorem's dependency block")
        previous = (supplied / "build_axioms.log").read_text()
        difference = "".join(difflib.unified_diff(previous.splitlines(keepends=True), fresh.splitlines(keepends=True), fromfile="supplied/build_axioms.log", tofile="fresh/build_axioms.log"))
        (output / "fresh_build_axioms.log").write_text(fresh)
        (output / "axioms.diff").write_text(difference)
        receipt["fresh_axioms"] = fresh
        receipt["axioms_diff"] = difference
        receipt["axioms_match_supplied"] = not difference
        receipt["lean_ran"] = True
        receipt["status"] = "PASS" if not difference else "AXIOMS_DIFFER"
        return 0 if not difference else 1
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError, zipfile.BadZipFile, tarfile.TarError) as error:
        receipt["status"] = "FAIL"
        receipt["error"] = str(error)
        print(str(error), file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        receipt["status"] = "INTERRUPTED"
        return 130
    finally:
        completed = {step["name"] for step in receipt["cells_executed"]}
        receipt["cells_skipped"] = [name for name in STAGES if name not in completed]
        receipt["wall_seconds"] = round(time.monotonic() - started, 3)
        (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(f"Unsigned execution receipt: {output / 'receipt.json'}", flush=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1], help="Git checkout containing the pinned commit")
    parser.add_argument("--output", type=Path, required=True, help="New output directory (must not exist)")
    parser.add_argument("--prepare-only", action="store_true", help="Archive, assert hashes, preserve supplied logs, and audit delivery dependencies; no downloads or Lean build")
    args = parser.parse_args()
    try:
        return execute(args.repo.resolve(), args.output.resolve(), args.prepare_only)
    except FileExistsError:
        parser.error("--output must be a new directory; existing sessions are never overwritten")


if __name__ == "__main__":
    raise SystemExit(main())
