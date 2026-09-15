"""Standard-library integration tests for the paper-facing simulation tools."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import time
import unittest
from pathlib import Path


SIMULATIONS = Path(__file__).resolve().parents[1]
REPOSITORY = SIMULATIONS.parent
OUTPUT = SIMULATIONS / "tests" / "_generated"


def run_script(*arguments, expected=0):
    completed = subprocess.run(
        [sys.executable, *map(str, arguments)],
        cwd=REPOSITORY,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=110,
        check=False,
    )
    if completed.returncode != expected:
        raise AssertionError(
            f"command returned {completed.returncode}, expected {expected}:\n{completed.stdout}"
        )
    return completed.stdout


class SimulationIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        shutil.rmtree(OUTPUT, ignore_errors=True)
        OUTPUT.mkdir(parents=True)
        cls.started = time.monotonic()
        cls.patch_stdout = run_script(
            SIMULATIONS / "patches.py",
            "--max-depth",
            "2",
            "--obj-through",
            "2",
            "--proof-max-level",
            "2",
            "--output-dir",
            OUTPUT / "patches",
        )

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(OUTPUT, ignore_errors=True)

    def test_patch_counts_contacts_nesting_and_obj(self):
        report = json.loads(self.patch_stdout)
        patches = report["patches"]
        self.assertEqual([row["tile_count"] for row in patches], [1, 8, 64])
        self.assertEqual([row["baseline_cell_count"] for row in patches], [7, 56, 448])
        self.assertTrue(all(row["cells_disjoint"] for row in patches))
        self.assertTrue(all(row["all_face_contacts_in_44_atlas"] for row in patches))
        self.assertEqual(report["two_refinement_embeddings"][0]["embedded_pose_count"], 1)
        self.assertEqual(report["nested_A_pairs"][0]["c_to"], 2)
        proof_patches = report["proof_A_patches"]
        self.assertEqual([row["tile_count"] for row in proof_patches], [1, 64, 4096])
        self.assertEqual(
            [row["baseline_cell_count"] for row in proof_patches],
            [7, 448, 28672],
        )
        literal_a2 = json.loads((OUTPUT / "patches" / "A_2.json").read_text())
        self.assertEqual(literal_a2["nested_from_previous"]["embedded_pose_count"], 64)
        for depth, copies in enumerate((1, 8, 64)):
            pose_record = json.loads((OUTPUT / "patches" / f"sigma_{depth}.json").read_text())
            self.assertEqual(len(pose_record["poses"]), copies)
            obj = OUTPUT / "patches" / f"sigma_{depth}.obj"
            mtl = OUTPUT / "patches" / f"sigma_{depth}.mtl"
            self.assertTrue(obj.is_file() and obj.stat().st_size > 0)
            self.assertTrue(mtl.is_file() and mtl.stat().st_size > 0)
        obj_text = (OUTPUT / "patches" / "sigma_0.obj").read_text()
        self.assertIn("usemtl positive", obj_text)
        self.assertIn("usemtl negative", obj_text)

    def test_parent_recognition_on_depth_two(self):
        stdout = run_script(
            SIMULATIONS / "parents.py",
            OUTPUT / "patches" / "A_2.json",
        )
        report = json.loads(stdout)
        self.assertGreater(report["determined_interior_tiles"], 0)
        self.assertGreater(report["undetermined_boundary_tiles"], 0)
        self.assertEqual(report["recovered_parent_count"], 512)
        self.assertTrue(report["construction_parents_match_for_all_determined_tiles"])
        self.assertEqual(report["errors"], [])

    def test_default_family_is_byte_identical(self):
        destination = OUTPUT / "default_family.json"
        stdout = run_script(SIMULATIONS / "family.py", "--output", destination)
        self.assertIn("DEFAULT MATCH", stdout)
        self.assertEqual(destination.read_bytes(), (REPOSITORY / "solid/r44_solid.json").read_bytes())

    def test_repeated_family_magnitude_is_rejected(self):
        heights = ["1", "1", *map(str, range(3, 13))]
        stdout = run_script(
            SIMULATIONS / "family.py",
            *heights,
            "--output",
            OUTPUT / "invalid.json",
            expected=2,
        )
        self.assertIn("REJECTED", stdout)
        self.assertIn("repeated", stdout)
        self.assertFalse((OUTPUT / "invalid.json").exists())


if __name__ == "__main__":
    unittest.main()
