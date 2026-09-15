"""Fast unit tests for simulations/periodicity_search.py (no SAT solving needed except one
trivial instance; skipped entirely if python-sat is missing)."""
import unittest
from fractions import Fraction
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

try:
    import periodicity_search as ps
    HAVE_SAT = True
except ImportError:
    HAVE_SAT = False


@unittest.skipUnless(HAVE_SAT, "python-sat not installed")
class PeriodicitySearchUnitTests(unittest.TestCase):
    def test_hnf_counts(self):
        # sublattices of Z^3 of index n: sum over abc=n of a^2 b
        for n, expected in ((1, 1), (2, 7), (3, 13), (4, 35), (6, 91), (8, 155)):
            self.assertEqual(sum(1 for _ in ps.hnf_lattices(n)), expected)
        for n in (2, 3, 4):
            self.assertEqual(len(set(ps.hnf_lattices(n))), sum(1 for _ in ps.hnf_lattices(n)))

    def test_reduce_mod_is_canonical(self):
        L = ((4, 0, 0), (3, 2, 0), (1, 1, 3))
        for v in ((5, -7, 11), (-4, 2, -9), (0, 0, 0), (100, 1, -1)):
            r = ps.reduce_mod(v, L)
            self.assertEqual(ps.reduce_mod(r, L), r)
            self.assertTrue(0 <= r[0] < 4 and 0 <= r[1] < 2 and 0 <= r[2] < 3)
            # v - r must be a lattice vector: solve against the rows
            d = tuple(v[i] - r[i] for i in range(3))
            k3, rem = divmod(d[2], 3); self.assertEqual(rem, 0)
            d = (d[0] - k3 * 1, d[1] - k3 * 1, 0)
            k2, rem = divmod(d[1], 2); self.assertEqual(rem, 0)
            d = (d[0] - k2 * 3, 0, 0)
            self.assertEqual(d[0] % 4, 0)

    def test_frames(self):
        self.assertEqual(len(ps.frames(False)), 48)
        self.assertEqual(len(ps.frames(True)), 24)
        self.assertIn(((0, 1, 2), (1, 1, 1)), ps.frames(True))

    def test_tile_from_solid(self):
        t = ps.Tile.from_solid()
        self.assertEqual(len(t.cells), 7)
        self.assertEqual(len(t.panels), 24)
        self.assertEqual(sum(len(v) for v in t.panels.values()), 192)
        for feats in t.panels.values():
            self.assertEqual(len(feats), 8)
            for m, h in feats:
                self.assertNotEqual(h, 0)
                self.assertLessEqual(abs(h), Fraction(12, 10000))
                self.assertTrue(all(0 <= c <= 1 for c in m))
        flat = ps.Tile.from_solid(ignore_features=True)
        self.assertTrue(all(h == 0 for v in flat.panels.values() for _, h in v))

    def test_framed_signature_is_shift_invariant_and_frame_covariant(self):
        t = ps.Tile.from_solid()
        ft = ps.FramedTile(t, ((0, 1, 2), (1, 1, 1)))
        p0 = ps.Placed(ft, (0, 0, 0)); p1 = ps.Placed(ft, (5, -3, 2))
        self.assertEqual(sorted(p0.panels.values()), sorted(p1.panels.values()))
        # every frame keeps 7 distinct cells and 24 panels with 8 features each
        for fr in ps.frames(False):
            f = ps.FramedTile(t, fr)
            self.assertEqual(len(set(f.cells)), 7)
            self.assertEqual(len(f.panels), 24)
            self.assertTrue(all(len(sig) == 8 for sig, _ in f.panels.values()))

    def test_unit_cube_torus_is_satisfiable(self):
        cube = ps.Tile.unit_cube()
        sat, witness, n, _ = ps.solve_torus(cube, ps.frames(False), ((1, 0, 0), (0, 1, 0), (0, 0, 1)), "cadical153")
        self.assertTrue(sat)
        self.assertEqual(len(witness), 1)


if __name__ == "__main__":
    unittest.main()
