#!/usr/bin/env python3
"""Packaging boundary controls; no mathematical checks are reimplemented here."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

from build_package import check_archives, include, make_source_excerpts, presentation_log, safe_name, sha
from check_package import check
from make_claim_map import generate


class PackageBoundaries(unittest.TestCase):
    def test_private_and_review_paths_rejected_even_when_nested(self):
        for name in ["TILE_DISCOVERY_THREAD.txt", "folder/TILE_DISCOVERY_THREAD.txt",
                     ".codex/notes", "offgit/data", "history/source", "archive/source",
                     "provenance/sbt_papers/x", "lean/R44/.lake/cache",
                     "proof/review/verdict.md", "viewer/review/report.md", "../escape", "/escape"]:
            with self.subTest(name=name):
                self.assertFalse(safe_name(name))
                inner = io.BytesIO()
                with zipfile.ZipFile(inner, "w") as z:
                    z.writestr(name, "private")
                outer = io.BytesIO()
                with zipfile.ZipFile(outer, "w") as z:
                    z.writestr("nested.zip", inner.getvalue())
                with self.assertRaises(ValueError):
                    check_archives(outer.getvalue(), "outer.zip")

    def test_allowlist_retains_dependencies_but_not_repository_bulk(self):
        for name in ["solid/r44_solid.json", "lean/R44/lake-manifest.json",
                     "lean/R44/scripts/discharge_diff_audit.sh",
                     "paper/scripts/seed_language_closure.py", "paper/scripts/nonconvex_witness.py",
                     "paper/scripts/planar_areas.py", "paper/scripts/coincidence_tree.py", "paper/scripts/_texutil.py",
                     "proof/external_lean/F1_exchange2/r44_F1_exchange2_discharge.zip",
                     "verify/packets/r44_unrestricted_alignment/upstream/einstein_r44_proof_submission.zip"]:
            self.assertTrue(include(name), name)
        for name in ["simulations/periodicity_search_report.json", "figures/large.png",
                     "README.md", "paper/tex/main.pdf", "proof/review/REVIEW.md",
                     "paper/scripts/seed_fixed_point.py", "lean/R44/MECHANIZATION_PLAN.md",
                     "lean/R44/PAPER_UPDATES.md", "paper/STATEMENT.md"]:
            self.assertFalse(include(name), name)

    def test_canonical_corruption_fails_before_other_files_are_read(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "reader").mkdir()
            (root / "solid").mkdir()
            (root / "solid/example.json").write_text("changed")
            manifest = dict(source_commit="test", canonical_sha256={"solid/example.json": sha(b"original")},
                            files_sha256={"missing-file": sha(b"missing")})
            (root / "reader/package_manifest.json").write_text(json.dumps(manifest))
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(ValueError, "canonical digest"):
                check(root)

    def test_map_rejects_changed_frozen_ledger_before_generation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "paper").mkdir()
            (root / "paper/tex").mkdir()
            (root / "paper/CLAIMS_LEDGER.md").write_text(
                "changed\nFrozen digest (sha256 of this file above this line): " + "0" * 64)
            with self.assertRaisesRegex(ValueError, "frozen ledger digest"):
                generate(root, root / "generated", {})

    def test_lean_audit_allows_reports_but_rejects_changed_sources(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            files = {"reader/supplied_build_axioms.log": b"supplied",
                     "lean/R44/build_axioms.log": b"supplied",
                     "verify/replay_report.json": b"old report",
                     "lean/R44/R44.lean": b"proof source"}
            for name, body in files.items():
                path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(body)
            manifest=dict(source_commit="test",canonical_sha256={},files_sha256={p:sha(b) for p,b in files.items()})
            (root/"reader/package_manifest.json").write_text(json.dumps(manifest))
            (root/"verify/replay_report.json").write_text("fresh report")
            (root/"lean/R44/build_axioms.log").write_text("fresh axiom output")
            with contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaisesRegex(ValueError,"package digest"):
                    check(root)
                check(root,allow_runtime_reports=True)
                for name in ["reader/supplied_build_axioms.log","lean/R44/R44.lean"]:
                    path=root/name;original=path.read_bytes();path.write_text("changed")
                    with self.assertRaisesRegex(ValueError,"package digest"):
                        check(root,allow_runtime_reports=True)
                    path.write_bytes(original)

    def test_review_excerpts_preserve_math_and_original_line_numbers(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "paper").mkdir()
            (root / "paper/tex").mkdir()
            (root / "reader").mkdir()
            original = {
                "THEOREM.md": "# Claim\nA mathematical statement.\n## Review status\nHOLDS-AS-STATED\n",
                "paper/CLAIMS_LEDGER.md": "# Ledger\n| T1 | Mathematical statement |\n| M8 | HOLDS-AS-STATED |\nFrozen digest source marker\n",
                "paper/tex/sec8_mechanization.tex": "\\section{Mechanization}\nMathematical experiment. The\ndevelopment was reviewed adversarially twice\nthe second round found no blocking or major issue; third round\npending. We make no claim of simplicity, and we\nretain the mathematical argument.\n",
            }
            for name, body in original.items():
                (root / name).write_text(body)
            records = make_source_excerpts(root)
            for name, body in original.items():
                changed = (root / name).read_text()
                self.assertNotIn("HOLDS-AS-STATED", changed)
                self.assertIn("SOURCE EXCERPT", changed.splitlines()[0])
                self.assertEqual(len(body.splitlines()), len(changed.splitlines()))
                omitted = set(records[name]["omitted_original_lines"])
                omitted.update(records[name].get("partially_omitted_original_lines", []))
                for i, (before, after) in enumerate(zip(body.splitlines(), changed.splitlines()), 1):
                    if i != 1 and i not in omitted:
                        self.assertEqual(before, after)
                self.assertEqual(records[name]["original_sha256"], sha(body.encode()))
                self.assertEqual(records[name]["excerpt_sha256"], sha(changed.encode()))
            tex = (root / "paper/tex/sec8_mechanization.tex").read_text()
            self.assertNotIn("no blocking or major", tex)
            self.assertIn("Mathematical experiment.", tex)
            self.assertIn("We make no claim of simplicity, and we\nretain the mathematical argument.", tex)

    def test_generated_log_redacts_builder_paths_only(self):
        output = presentation_log("/home/example/.TinyTeX/package.sty /tmp/r44-reader-package-abc/paper/main.tex\nUndefined reference\n")
        self.assertNotIn("/home/example", output)
        self.assertNotIn("r44-reader-package-abc", output)
        self.assertIn(".TinyTeX/package.sty", output)
        self.assertIn("Undefined reference", output)


if __name__ == "__main__":
    unittest.main()
