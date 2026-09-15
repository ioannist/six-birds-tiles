"""Execution-receipt regressions, including failed reruns and interruptions."""
import contextlib
import io
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from runtime import Session


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.session = Session({"source_commit":"test", "mathematical_baseline_commit":"test", "canonical_sha256":{}}, {})

    def test_failed_rerun_clears_old_success(self):
        for cell, key in [("finite_replay","replay_report"), ("atlas_equality","atlas_difference"),
                          ("mutation_controls","mutation_controls"), ("periodic_controls","periodic_controls"),
                          ("companion_census","companion_census")]:
            self.session.receipt[key] = {"status":"PASS"}
            with self.assertRaises(RuntimeError):
                self.session.run(cell, lambda: (_ for _ in ()).throw(RuntimeError("test failure")))
            saved = json.loads(self.session.receipt_path.read_text())
            self.assertNotIn(key, saved)
            self.assertEqual(saved["cells"][cell]["status"], "FAIL")

    def test_interruption_is_terminal(self):
        with self.assertRaises(KeyboardInterrupt):
            self.session.run("finite_replay", lambda: (_ for _ in ()).throw(KeyboardInterrupt()))
        saved = json.loads(self.session.receipt_path.read_text())
        self.assertEqual(saved["cells"]["finite_replay"]["status"], "interrupted")
        self.assertIn("seconds", saved["cells"]["finite_replay"])

    def test_unexecuted_cells_are_skipped(self):
        with contextlib.redirect_stdout(io.StringIO()):
            self.session.download()
        saved = json.loads(self.session.receipt_path.read_text())
        self.assertEqual(saved["cells"]["companion_census"]["status"], "skipped")
        self.assertFalse(saved["lean_ran"])


if __name__ == "__main__":
    unittest.main()
