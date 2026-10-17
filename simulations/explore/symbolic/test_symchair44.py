"""Tests for symchair44.py: the sympy generator against the canonical data.

Only these tests read solid/r44_solid.json and certificates/candidate_certificate.json;
the generator itself reads nothing.  Skipped if sympy is missing.

    python3 -m unittest simulations/explore/symbolic/test_symchair44.py
    python3 simulations/explore/symbolic/test_symchair44.py
"""
import json
import sys
import unittest
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(REPO / "simulations"))

try:
    import symchair44 as S
    HAVE = True
except ImportError:
    HAVE = False

SOLID = json.loads((REPO / "solid" / "r44_solid.json").read_text())
CERT = json.loads((REPO / "certificates" / "candidate_certificate.json").read_text())


def pose(p):
    return ((tuple(p[0][0]), tuple(p[0][1])), tuple(p[1]))


@unittest.skipUnless(HAVE, "sympy not installed")
class SymChair44(unittest.TestCase):
    def test_mesh_equals_canonical_solid(self):
        solid = S.Solid(S.label_table(S.CHILDREN))
        fr = lambda x: Fr(int(x.p), int(x.q))
        Vm = [tuple(fr(x) for x in v) for v in solid.vertices]
        Vj = [tuple(Fr(x) for x in v) for v in SOLID["vertices"]]
        self.assertEqual((len(Vm), len(solid.edges), len(solid.triangles)), (2138, 6408, 4272))
        self.assertEqual(set(Vm), set(Vj))

        def canon(t):
            m = min(range(3), key=lambda i: t[i])
            return t[m:] + t[:m]
        self.assertEqual({canon(tuple(Vj[i] for i in t)) for t in SOLID["triangles"]},
                         {canon(tuple(Vm[i] for i in t)) for t in solid.triangles})

    def test_children_and_labels_are_derived_not_read(self):
        self.assertEqual({pose(c) for c in CERT["children"]}, set(S.CHILDREN))
        labels = S.label_table(S.CHILDREN)
        self.assertEqual(labels, CERT["profile"])
        self.assertEqual(labels, SOLID["profile"])
        self.assertEqual(sum(labels), 0)

    def test_volume_is_seven_for_all_w_h(self):
        solid = S.Solid(S.label_table(S.CHILDREN), symbolic=True)
        self.assertEqual(solid.volume(), 7)

    def test_atlas_matches_certificate(self):
        A = S.atlas()
        self.assertEqual((len(A["raw"]), len(CERT["raw_contacts"])), (2388, 2388))
        self.assertEqual({pose(c) for c in CERT["raw_contacts"]}, set(A["raw"]))
        self.assertEqual({pose(c) for c in CERT["legal_contacts"]}, set(A["legal"]))
        self.assertEqual({pose(c) for c in CERT["contact_states"]}, set(A["realized"]))
        self.assertEqual((len(A["equations"]), len(CERT["signed_rows"])), (372, 372))
        self.assertEqual(S.equation_rank(A["equations"]), 192 - SOLID["kernel_dimension"])

    def test_agrees_with_repository_patch_code(self):
        import patches
        poses = [(f, tuple(t)) for f, t in S.sigma_poses(S.CHILDREN, 2)]
        self.assertEqual(poses, list(patches.sigma_depth(2)))

    def test_chirality_forced_by_contacts(self):
        A = S.atlas()
        self.assertEqual(A["mirror"], 1194)
        self.assertEqual({S.frame_det(p[0]) for p in A["legal"]}, {1})


if __name__ == "__main__":
    unittest.main(verbosity=2)
