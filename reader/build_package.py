#!/usr/bin/env python3
"""Build the compact U5 package from one immutable git archive, with pinned reader tooling."""
import argparse
import hashlib
import io
import json
import os
import re
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile
import tempfile
import zipfile

from make_claim_map import generate

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FORBIDDEN = {"TILE_DISCOVERY_THREAD.txt", ".codex", "offgit", "history", "archive", ".lake", ".git", "__pycache__", "review"}
TOOLS = ("pin.json", "REVIEW_PROMPT.md", "check_package.py", "build_axioms.py", "make_claim_map.py")
FIGURES = ("figures/r44_parent_cluster.png", "figures/r44_patch64.png",
           "figures/print-preview/figure1-corrected.pdf", "figures/print-preview/figure3-corrected.pdf")
PAPER_CHECKERS = ("nonconvex_witness.py", "planar_areas.py", "seed_language_closure.py", "coincidence_tree.py", "_texutil.py")
READING_LEAN = ("Types.lean", "FiniteModel.lean", "Theorems.lean", "LogicalSpineFoundation.lean", "LogicalSpine.lean")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def presentation_log(text):
    """Hide builder-local paths in generated logs, preserving diagnostic text."""
    text = re.sub(r"/home/[^/\s]+", "<LOCAL_HOME>", text)
    text = re.sub(r"/tmp/r44-reader-package-[^/\s]+", "<BUILD_DIR>", text)
    return "T3 presentation log; builder-local home and staging prefixes redacted.\n" + text


def run(args, cwd=ROOT):
    result = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f"command failed: {args}\n{result.stdout[-3000:]}\n{result.stderr[-3000:]}")
    return result.stdout


def safe_name(name):
    path = PurePosixPath(name)
    return not path.is_absolute() and ".." not in path.parts and not (set(path.parts) & FORBIDDEN) and "provenance" not in path.parts


def include(name):
    if not safe_name(name):
        return False
    p = PurePosixPath(name)
    if name == "THEOREM.md" or name in FIGURES:
        return True
    if p.parts[0] in {"solid", "certificates", "verify"}:
        return True
    if name.startswith("lean/R44/"):
        return not any(s in p.parts for s in ("external", "review")) and p.name not in {"MECHANIZATION_PLAN.md", "PAPER_UPDATES.md"}
    if name.startswith("paper/tex/"):
        return p.suffix == ".tex" or p.name in {"Makefile", "check_log.py"}
    if name in {"paper/CLAIMS_LEDGER.md", "paper/refs.bib", "paper/APPENDIX_DATA.md"}:
        return True
    if p.parent == PurePosixPath("paper/scripts") and p.name in PAPER_CHECKERS:
        return True
    if p.parent == PurePosixPath("proof"):
        return p.suffix == ".md" and p.name != "REVIEW_PROMPT.md" and not p.name.startswith("SOURCE_AUDIT")
    return name.startswith("proof/external_lean/") and name.endswith(".zip")


def check_archives(data, label, depth=0):
    if depth > 8:
        raise ValueError("unexpected deeply nested archive")
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        for member in archive.infolist():
            if not safe_name(member.filename):
                raise ValueError(f"excluded member in {label}: {member.filename}")
            if member.filename.endswith(".zip"):
                check_archives(archive.read(member), label + "::" + member.filename, depth + 1)


def quotation(path, start, end):
    lines = path.read_text().splitlines()
    begin = next(i for i, line in enumerate(lines) if start in line)
    finish = next(i for i in range(begin + 1, len(lines)) if end in lines[i]) if end else len(lines)
    return begin + 1, "\n".join(lines[begin:finish])


def make_source_excerpts(stage):
    """Omit only prior-review material; retain original line identities and explicit provenance."""
    records = {}
    for name in ("THEOREM.md", "paper/CLAIMS_LEDGER.md"):
        path = stage / name
        original = path.read_bytes()
        lines = original.decode().splitlines(keepends=True)
        if name == "THEOREM.md":
            start = next(i for i, line in enumerate(lines) if line.strip() == "## Review status")
            omitted = list(range(start, len(lines)))
        else:
            omitted = [i for i, line in enumerate(lines) if line.startswith("| M8 |")]
            if len(omitted) != 1:
                raise ValueError("expected exactly one review-only M8 row")
        lines[0] = lines[0].rstrip("\n") + " [U5 SOURCE EXCERPT; prior-review-only lines omitted; original line numbers preserved]\n"
        for i in omitted:
            lines[i] = f"[U5 omitted prior-review-only source line {i + 1}; original whole-file SHA256 {sha(original)}]\n"
        derived = "".join(lines).encode()
        path.write_bytes(derived)
        records[name] = dict(original_sha256=sha(original), excerpt_sha256=sha(derived),
            omitted_original_lines=[i + 1 for i in omitted],
            modified_header_line=1,
            note="Explicit source excerpt; all mathematical text retained verbatim. Line numbers match the original. The original full-file and frozen-prefix digests cannot be recomputed from this excerpt.")
    name = "paper/tex/sec8_mechanization.tex"
    path = stage / name
    original = path.read_bytes()
    body = original.decode()
    start = body.index("The\ndevelopment was reviewed adversarially twice")
    end = body.index("pending. We make no claim of simplicity", start) + len("pending. ")
    removed = body[start:end]
    first_line = body[:start].count("\n") + 1
    last_line = body[:end].count("\n") + 1
    marker = r"\emph{[U5: prior-review status omitted.]}"
    replacement = marker + "\n" + "% [U5 omitted prior-review-only source line]\n" * (removed.count("\n") - 1)
    changed = body[:start] + replacement + body[end:]
    lines = changed.splitlines(keepends=True)
    lines[0] = lines[0].rstrip("\n") + " % [U5 SOURCE EXCERPT; only prior-review status omitted; original line numbers preserved]\n"
    derived = "".join(lines).encode()
    if len(original.splitlines()) != len(derived.splitlines()):
        raise ValueError("paper excerpt must preserve original line count")
    path.write_bytes(derived)
    records[name] = dict(original_sha256=sha(original), excerpt_sha256=sha(derived),
        omitted_original_lines=list(range(first_line + 1, last_line)),
        partially_omitted_original_lines=[first_line, last_line], modified_header_line=1,
        omitted_fragment_sha256=sha(removed.encode()),
        note="Only the contiguous prior-review-status narrative is omitted. Both surrounding sentences are retained verbatim. Original line numbers are preserved; the PDF is built from this visibly marked TeX excerpt. This is not the full original paper source.")
    (stage / "reader/source_excerpts.json").write_text(json.dumps(records, indent=2) + "\n")
    return records


def reading_notes(stage):
    """Source-navigation notes and a mechanical comparison of supplied axiom records."""
    document = (stage / "lean/R44/AXIOMS.md").read_text()
    log = (stage / "lean/R44/build_axioms.log").read_text()
    pattern = r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)"
    def records(text):
        return {m.group(1): sorted({s.strip() for s in (m.group(2) or "").split(",") if s.strip()})
                for m in re.finditer(pattern, text, re.S)}
    documented, logged = records(document), records(log)
    first_block = re.search(r"```text\n(.*?)```", document, re.S).group(1)
    comparison = dict(document_sha256=sha(document.encode()), log_sha256=sha(log.encode()),
        documented_declarations=len(documented), logged_declarations=len(logged),
        absent_from_first_document_block=sorted(logged.keys() - records(first_block).keys()),
        absent_from_full_document=sorted(logged.keys() - documented.keys()),
        document_only=sorted(documented.keys() - logged.keys()),
        differing_axiom_sets=sorted(name for name in documented.keys() & logged.keys() if documented[name] != logged[name]),
        scope="T2 text/set comparison of supplied records only; not a fresh Lean build.")
    if (len(documented) != 169 or len(logged) != 169 or
            comparison["absent_from_first_document_block"] != ["R44.DischargeAssembly.registered_assembly_collar_data"] or
            comparison["absent_from_full_document"] or comparison["document_only"] or comparison["differing_axiom_sets"] or
            not document.splitlines()[303].startswith("'R44.DischargeAssembly.registered_assembly_collar_data'")):
        raise ValueError("supplied axiom presentations changed; update the source-reading notes for the new pin")
    (stage / "reader/axiom_document_comparison.json").write_text(json.dumps(comparison, indent=2) + "\n")
    return """# Reading notes — T3 source navigation; T2 supplied-record comparison

This utility is not evidence for the theorem. The notes identify source locations and
reporting scopes; they do not repair or restate mathematical arguments.

## T1/T1n — actual Lean sources in the reading bundle

The bundle contains complete `Types.lean`, `FiniteModel.lean`, `Theorems.lean`,
`LogicalSpineFoundation.lean` and `LogicalSpine.lean`, under `lean/R44/R44/`.
Read the foundation's `RigidMotion`, `Packing`, `Tiling`, `Q`, `Per` and `Sym`
definitions directly. The spine contains `Hypotheses`, parent/coarsening definitions,
the existence assembly and `r44_einstein`. `all_periods_grid` is a private helper in
the spine; absence of a separately printed axiom record is not absence of source.

The bundle also includes the original prefix of `Generated/CoreData.lean`, through the
complete literal `panels` declaration, with original line numbers and both full-source
and excerpt hashes. `FiniteModel.lean` constructs `nativeFeatures` from those panels.
This makes the object's defining data readable. Remaining generated certificate/mesh
tables, `MateData.lean`, imported proof modules and Mathlib are in the companion zip
or its pinned dependencies. The reading bundle is not a standalone Lean build and
does not supply every proof dependency. Hashes do not establish semantic correctness.

## T2 — distinguish the two supplied axiom presentations

Use `lean/R44/build_axioms.log` for the supplied axiom records and all source-map
`build_axioms.log:N` citations. The complete log and `negative_control.log` are embedded
in this text bundle, explicitly as supplied records rather than a fresh build.
`negative_control.log` is a historical diagnostic snapshot: it mentions the retired
`HypothesesContradiction.lean` and does not record every currently shipped control.
Use the current `scripts/controls.sh` for a fresh, complete control run; do not infer
its result from that historical log. Historical counts in `lean/R44/README.md`
(including its older 22-finite-theorem sentence) do not override the current 23-item
inventory in `Theorems.lean` and ledger M1.
`AXIOMS.md` is preserved as documentation: its first block, described there as exact,
omits `R44.DischargeAssembly.registered_assembly_collar_data`; the same document lists
that record later, at line 304. It is not a line-for-line copy of the log. At this pin,
the full document's 169 declaration/axiom sets agree with the log's 169 sets.
`reader/axiom_document_comparison.json` records the mechanical comparison and source hashes.
Never substitute AXIOMS.md line numbers for build_axioms.log line numbers. The decision-
method table is not a declaration inventory: e.g. it discusses `transported_role_geometry`
in its carrier-frame rows rather than assigning it a standalone row. Actual source for
that auxiliary theorem is `Proved/CarrierFeatureFrameReduction.lean` in the zip.

## T3 — source precedence and historical shorthand

For current mathematical statements at the source snapshot, read the paper and actual
Lean declarations; consult the complete supplied log for reported axiom dependencies.
`THEOREM.md` is a navigation document. Its historical `(from H1)` annotation beside
`local_finiteness` must be read with the current `HYPOTHESES.md` and actual declaration;
it is not an additional hypothesis asserted by this utility. The original proof packets
retain their historical no-review/no-Lean status sentences; ERRATA and the paper contain
the later corrections. The obsolete planning `paper/STATEMENT.md` is intentionally absent.
References to historical rulings or prior-review locations are source citations, not supplied
review reports or endorsements. Review-result narratives themselves are omitted explicitly.

The paper says build resources are not reported in that paper version. START_HERE's
planning estimates come from the author build diary in `lean/R44/README.md`, whose
Performance section is included below: its 9,769,136 KB measurement describes one
historical run, and other entries exceed it. These are different reporting scopes,
not measurements of the reader's machine or guarantees. Replay timing records likewise
describe individual author sessions, not a universal runtime.

Repeated hashes on omitted lines are the SHA256 of the entire original source file,
not hashes of individual omitted lines. `source_excerpts.json` gives original/derived
whole-file hashes and omitted original line numbers. The theorem excerpt in START_HERE
begins with its docstring; the declaration's own line is separately identified there.
"""


def start_here(stage, pin, preview):
    spine = stage / "lean/R44/R44/LogicalSpine.lean"
    lineno, statement = quotation(spine, "/-- The unconditional R44 conclusion", "end")
    declaration_line = next(i for i, line in enumerate(spine.read_text().splitlines(), 1) if line.startswith("theorem r44_einstein :"))
    return f"""# Ask your AI to audit Chair44 (R44) — T3 reading; T2 replay; T1/T1n formal audit

This utility is not evidence for the theorem. It organizes the supplied proof and checks.

{'DEVELOPMENT PREVIEW: reader tooling is separately hashed; no release approval is implied.' if preview else 'Reader package: source and tooling hashes are in reader/package_manifest.json.'}

## T2 identity checks, followed by T1/T1n semantic inspection

One source snapshot: `{pin['source_commit']}`. Mathematical source and data inputs
come from `git archive` of that commit. The paper's embedded mathematical baseline is
`{pin['mathematical_baseline_commit']}`. The later source snapshot is necessary because
the baseline commit predates the reconciled paper and ledger. The builder compares the
complete Lean project and all four canonical inputs with the baseline before packaging.
Reader navigation/tooling is an explicitly separate, hashed layer in the manifest.
`THEOREM.md`, `paper/CLAIMS_LEDGER.md` and `paper/tex/sec8_mechanization.tex` are visibly
labelled source excerpts: only prior-review status and review-only ledger row M8 are omitted. Original line
numbers are preserved. `reader/source_excerpts.json` records original and excerpt hashes
and every omitted line; these excerpts are not byte-identical to the full sources.
The map was generated from the frozen original ledger before excerpting. Its original
frozen digest cannot be recomputed from the excerpt; regeneration requires the pinned
original ledger and TeX from the repository. Nonessential Lean planning/update notes and
the obsolete planning document `paper/STATEMENT.md` are excluded.

Read this identity path before assessing the claim:

1. `solid/r44_solid.json`: `{pin['canonical_sha256']['solid/r44_solid.json']}`.
2. `python3 lean/R44/gen/extract.py --check`: compare generated literals with the
   canonical inputs and `lean/R44/gen/GENERATED.sha256`.
3. Inspect `lean/R44/R44/Generated/CoreData.lean` and `MateData.lean`.
4. Inspect `Q` in `lean/R44/R44/LogicalSpineFoundation.lean` and its imported definitions.
5. Inspect `r44_einstein` in `lean/R44/R44/LogicalSpine.lean`.

Hashes check byte identity and generated-data consistency. They cannot establish that
the generated data has the intended geometric meaning or that the definitions faithfully
express the displayed solid. Those links require reading the definitions and proofs.

## T1n claim — verbatim Lean source

Docstring excerpt starts at `lean/R44/R44/LogicalSpine.lean:{lineno}`;
the theorem declaration starts at `lean/R44/R44/LogicalSpine.lean:{declaration_line}`:

```lean
{statement}
```

For the English claim and permitted motions, read `paper/tex/sec1_intro.tex`;
for the complete illustrated mathematical argument open `paper/tex/main.pdf`.
The PDF is freshly typeset from the same visibly marked TeX excerpt and pinned figure inputs;
the prior-review-status narrative is omitted in both PDF and TeX, while all mathematical text
is retained verbatim. This reader PDF is not the full original paper. Its build
record in `reader/pdf_build.log`. It is presentation, not a fresh formal proof build.

## T3 reading route

If you are the reviewing assistant, read `reader/REVIEW_PROMPT.md` now and use its
five required challenge sections in your report, including any checks you could
not perform. This applies to both the reading and execution routes below.
For a new conversation, copy that prompt. Supply either this entire zip
to an executing agent or `reader/reading_bundle.txt` to a reading-only assistant.
The text bundle contains the paper's TeX with the labelled review-only omission in section 8
(equations preserved), not PDF text extraction.
File sections carry original line numbers, so findings can use file:line.
Actual Lean definitions and theorem sources are included in the text bundle; start with
`reader/reading_notes.md` for their locations, supplied-log precedence and the precise
boundary between the reading bundle and the complete executable zip.
`reader/claim_map.md` and `.json` link verbatim ledger rows, paper annotations and
the declaration's supplied axiom record. Source references to excluded historical
material are preserved as quotations; prior review reports themselves are excluded.
The unchanged nested verification packets may contain their original author briefs
and provenance notes; these are not independent reviewer verdicts or current instructions.
`proof/PROOFS_registered.md`, `proof/ALIGNMENT_PROOF.md` and the nested packet notes are
historical sources preserved verbatim. Their statements about pending review or absence of
Lean formalization describe those packets when written. For the source snapshot's current
mathematical statements use the paper; for formal scope inspect `LogicalSpine.lean`,
`HYPOTHESES.md` and the supplied axiom records. `proof/ERRATA.md` contains corrections
cited by the source map and is included in both the zip and text bundle.

## T2 execution route — Python standard library, no installation

From the extracted package root, before any experiment:

```bash
python3 reader/check_package.py
python3 lean/R44/gen/extract.py --check
python3 verify/replay.py
python3 verify/packets/r44_unrestricted_alignment/src/test_mutations.py
```

The first command prints and checks the commit and all four canonical digests, then
checks all packaged file digests silently. Run it before the other commands. It uses an unsigned
manifest; independently compare the download's SHA256SUMS if available.
The replay uses exact certificate predicates and writes `verify/replay_report.json`.
The six mutations use temporary input copies and write their result under the packet's
`results/`; rerunning the package hash check after execution can report those deliberate
output changes. For a fresh identity check, extract a fresh copy of the download.
Expected runtime: the authors recorded about 28 seconds for replay; this is not a
measurement of your machine. Every check's scope is in its own output.

For the additional finite evidence cited by ledger O10, O11, L3, L8, L9 and L10,
the original standalone scripts and their helper are included:

```bash
python3 paper/scripts/nonconvex_witness.py
python3 paper/scripts/planar_areas.py
python3 paper/scripts/seed_language_closure.py
python3 paper/scripts/coincidence_tree.py --out reader/scratch-figures
```

The delivery-source audit also needs no Lean build:

```bash
(cd lean/R44 && bash scripts/discharge_diff_audit.sh)
```

The optional theorem-free periodicity search and its receipts (ledger N9), illustration
production audits (O12), superseded experiments and historical/provenance materials are
intentionally omitted. Their source references remain quotations. They are not dependencies
of the packaged replay or formal build; use the pinned repository for those optional routes.

## T1/T1n execution route — Lean, optional and separate

Allow about 16 GB RAM (9.8 GB peak recorded), 30 minutes or more and a multi-gigabyte
Mathlib cache download. A fresh package build took 26 minutes 53 seconds on the
authors' host; timings vary. If unavailable, skip this route and read
`reader/supplied_build_axioms.log` and `lean/R44/negative_control.log` as **supplied records,
not a fresh build**. The negative-control log is historical and does not cover every
current control; see `reader/reading_notes.md`. Toolchain and dependency pins are under `lean/R44/`.

In `lean/R44/`, with Lean's elan launcher installed:

```bash
lake exe cache get
lake build
chmod +x scripts/discharge_diff_audit.sh
bash scripts/controls.sh
```

The `chmod` step restores executable permission if your zip extractor discarded it;
the ZIP itself records that permission. Retain the fresh `CONTROLS:` line and the
commands' complete logs. The package includes
the seven original author delivery archives needed by `discharge_diff_audit.sh`.
The optional command `python3 reader/build_axioms.py` from the package root obtains fresh axiom output after
the build and writes `reader/fresh_axioms.log` and `reader/fresh_axioms.diff`.
It compares against the immutable `reader/supplied_build_axioms.log`, preserved before
any build can overwrite the original output location. It may follow the Python route:
only the three known regenerated report paths are allowed to differ, while every source
and the immutable supplied snapshot must still match the package manifest.
It exits nonzero if the fresh axiom blocks differ from those supplied records.

T1 = Lean with only standard axioms; T1n = Lean plus named native compiler hooks;
T2 = finite Python computation; T3 = written proof or cited import. Formal tiers depend
on the axiom set, not tactic spelling. Historical ledger D/Q/C labels are quotations,
not additional proof tiers. The utility does not replace any of these sources.
"""


def build(args):
    tooling_snapshot = {name: (HERE / name).read_bytes() for name in TOOLS + ("build_package.py",)}
    pin = json.loads(tooling_snapshot["pin.json"])
    if not args.preview and run(["git", "status", "--porcelain", "--untracked-files=all"]).strip():
        raise ValueError("release packaging requires a clean tree (including untracked files); --preview builds an explicitly marked immutable-source preview")
    commit = run(["git", "rev-parse", pin["source_commit"] + "^{commit}"]).strip()
    if commit != pin["source_commit"]:
        raise ValueError("source pin must be a full commit hash")
    baseline = pin["mathematical_baseline_commit"]
    changes = run(["git", "diff", "--name-only", baseline, commit, "--", "lean/R44", *pin["canonical_sha256"]]).splitlines()
    changes = [name for name in changes if "/review/" not in name]
    if changes:
        raise ValueError(f"mathematical baseline changed: {changes}")
    names = run(["git", "ls-tree", "-r", "--name-only", commit]).splitlines()
    selected = [name for name in names if include(name)]
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="r44-reader-package-") as tmp:
        stage = Path(tmp) / "package"
        stage.mkdir()
        archive_path = Path(tmp) / "source.tar"
        with archive_path.open("wb") as archive_file:
            subprocess.run(["git", "archive", "--format=tar", commit, "--", *selected], cwd=ROOT,
                           stdout=archive_file, check=True)
        with tarfile.open(archive_path) as archive:
            for member in archive.getmembers():
                if not safe_name(member.name) or not (member.isfile() or member.isdir()):
                    raise ValueError(f"unsafe archive member: {member.name}")
                archive.extract(member, stage, filter="data")
        # Pin and assert every canonical input before running any checker or renderer.
        print("T2 source commit:", commit, flush=True)
        for name, expected in pin["canonical_sha256"].items():
            actual = sha((stage / name).read_bytes())
            if actual != expected:
                raise ValueError(f"canonical digest mismatch: {name}")
            print("T2", actual, name, flush=True)
        source_hashes = {name: sha((stage / name).read_bytes()) for name in selected}
        (stage / "reader").mkdir()
        for name in TOOLS:
            (stage / "reader" / name).write_bytes(tooling_snapshot[name])
        (stage / "reader/supplied_build_axioms.log").write_bytes((stage / "lean/R44/build_axioms.log").read_bytes())
        generate(stage, stage / "reader", pin)
        excerpts = make_source_excerpts(stage)
        print("T3 source map generated", flush=True)
        # PDF is untracked in the repository; rebuild from the archived paper, never copy it.
        env = os.environ.copy()
        env["SOURCE_DATE_EPOCH"] = run(["git", "show", "-s", "--format=%ct", commit]).strip()
        pdf = subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
                             cwd=stage / "paper/tex", env=env, capture_output=True, text=True, errors="replace")
        (stage / "reader/pdf_build.log").write_text(presentation_log(pdf.stdout + pdf.stderr))
        if pdf.returncode:
            raise RuntimeError("pinned PDF build failed:\n" + (pdf.stdout + pdf.stderr)[-4000:])
        print("T3 pinned PDF typeset", flush=True)
        (stage / "START_HERE.md").write_text(start_here(stage, pin, args.preview))
        (stage / "reader/reading_notes.md").write_text(reading_notes(stage))
        # Only the PDF and pinned TeX/source inputs survive; figure rasters are not distributed.
        shutil.rmtree(stage / "figures")
        for path in (stage / "paper/tex").rglob("*"):
            if path.is_file() and str(path.relative_to(stage)) not in selected and path.name != "main.pdf":
                path.unlink()
        for path in stage.rglob("*.zip"):
            check_archives(path.read_bytes(), str(path.relative_to(stage)))
        print("T2 replay self-test starting", flush=True)
        # Execute on a second extraction-equivalent tree, retaining all supplied records intact.
        test = Path(tmp) / "test"
        shutil.copytree(stage, test)
        logs = []
        commands = [
            [sys.executable, "lean/R44/gen/extract.py", "--check"],
            [sys.executable, "verify/replay.py"],
            [sys.executable, "verify/packets/r44_unrestricted_alignment/src/test_mutations.py"],
            ["bash", "scripts/discharge_diff_audit.sh"],
        ]
        for command in commands:
            cwd = test / "lean/R44" if command[0] == "bash" else test
            logs.append("$ " + " ".join(command) + "\n" + run(command, cwd))
        for checker in PAPER_CHECKERS:
            if checker == "_texutil.py":
                continue
            command = [sys.executable, "paper/scripts/" + checker]
            if checker == "coincidence_tree.py":
                command += ["--out", "reader/scratch-figures"]
            logs.append("$ " + " ".join(command) + "\n" + run(command, test))
        (stage / "reader/package_selftest.log").write_text("T2 packaging self-test; not a Lean build\n\n" + "\n".join(logs))
        print("T2 extract, replay, mutations and delivery audit self-tests passed", flush=True)
        bundle_files = ["START_HERE.md", "reader/REVIEW_PROMPT.md", "reader/reading_notes.md", "reader/source_excerpts.json",
            "reader/axiom_document_comparison.json", "THEOREM.md", "paper/CLAIMS_LEDGER.md",
            "lean/R44/AXIOMS.md", "lean/R44/HYPOTHESES.md", "reader/claim_map.md",
            "lean/R44/build_axioms.log", "lean/R44/negative_control.log",
            *sorted(name for name in selected if name.startswith("paper/tex/") and name.endswith(".tex")),
            "paper/refs.bib", "proof/PROOFS_registered.md", "proof/ALIGNMENT_PROOF.md", "proof/ERRATA.md",
            *("lean/R44/R44/" + name for name in READING_LEAN)]
        bundle = ["CHAIR44 (R44) AI READING BUNDLE — T3 reading; T1/T1n supplied records\nThis utility is not evidence for the theorem.\nExecutable sources are in the companion zip.\n"]
        for name in bundle_files:
            body = (stage / name).read_text()
            bundle.append(f"\n===== {name} | SHA256 {sha(body.encode())} =====\n" + "\n".join(f"{i}: {line}" for i, line in enumerate(body.splitlines(), 1)))
        for name, first, last in (
            ("lean/R44/R44/Generated/CoreData.lean", 1, 276),
            ("lean/R44/README.md", 631, len((stage / "lean/R44/README.md").read_text().splitlines())),
        ):
            body = (stage / name).read_text()
            lines = body.splitlines()[first - 1:last]
            excerpt = "\n".join(lines) + "\n"
            bundle.append(f"\n===== {name} | ORIGINAL LINES {first}-{last} ONLY | ORIGINAL WHOLE-FILE SHA256 {sha(body.encode())} | EXCERPT SHA256 {sha(excerpt.encode())} =====\n" +
                          "\n".join(f"{i}: {line}" for i, line in enumerate(lines, first)))
        reading = "\n".join(bundle) + "\n"
        if len(reading.encode()) >= 2_000_000:
            raise ValueError("reading bundle exceeds 2 MB")
        (stage / "reader/reading_bundle.txt").write_text(reading)
        files = {str(path.relative_to(stage)): sha(path.read_bytes()) for path in sorted(stage.rglob("*")) if path.is_file()}
        if any(not safe_name(name) for name in files):
            raise ValueError("excluded output member")
        manifest = dict(pin, preview=args.preview,
            scope="Unsigned file identity manifest. Utility tooling is separately hashed; source inputs come from one git archive. source_excerpts records the explicitly labelled review-only omissions.",
            source_files_sha256=source_hashes,
            source_excerpts=excerpts,
            tooling_sha256={name: sha(data) for name, data in tooling_snapshot.items()},
            derived_files=[name for name, digest in files.items() if source_hashes.get(name) != digest and not name.startswith("reader/")],
            files_sha256=files)
        (stage / "reader/package_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        run([sys.executable, "reader/check_package.py"], stage)
        prefix = f"r44-ai-review-{commit[:10]}" + ("-preview" if args.preview else "")
        zipped = output / (prefix + ".zip")
        with zipfile.ZipFile(zipped, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for path in sorted(stage.rglob("*")):
                if path.is_file():
                    info = zipfile.ZipInfo(str(path.relative_to(stage)), date_time=(2026, 9, 10, 0, 0, 0))
                    info.external_attr = (path.stat().st_mode & 0xFFFF) << 16
                    info.compress_type = zipfile.ZIP_DEFLATED
                    archive.writestr(info, path.read_bytes())
        if zipped.stat().st_size >= 25_000_000:
            zipped.unlink()
            raise ValueError("zip exceeds 25 MB")
        reading_path = output / (prefix + "-reading.txt")
        reading_path.write_text(reading)
        sums = "".join(f"{sha(p.read_bytes())}  {p.name}\n" for p in (zipped, reading_path))
        (output / "SHA256SUMS.txt").write_text(sums)
        for name in ("claim_map.json", "claim_map.md", "package_manifest.json", "package_selftest.log"):
            shutil.copy2(stage / "reader" / name, output / name)
        shutil.copy2(stage / "START_HERE.md", output / "START_HERE.md")
        print(sums, end="")
        print(f"T2 sizes: zip={zipped.stat().st_size}; reading={reading_path.stat().st_size}")
        print("T2 STATUS: PASS (package assembly and self-tests; no fresh Lean build)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="output directory")
    parser.add_argument("--preview", action="store_true", help="allow dirty checkout; still archive only the immutable source pin, label outputs preview")
    args = parser.parse_args()
    build(args)
