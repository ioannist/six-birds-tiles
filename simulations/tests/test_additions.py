"""Standard-library tests for orientation_spectrum.py and surface_laws.py."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import orientation_spectrum as OS
import surface_laws as SL
import coincidence_rate as CR


class OrientationSpectrum(unittest.TestCase):
    def test_spectrum(self):
        result = OS.spectrum()
        self.assertTrue(OS.check(result))
        self.assertEqual(result["root_multiplicities"], {0: 3, 8: 1, 2: 20})

    def test_matrix_is_nonnegative_with_row_sums_eight(self):
        species, M = OS.orientation_matrix()
        self.assertEqual(len(species), 24)
        self.assertTrue(all(x >= 0 for row in M for x in row))
        self.assertTrue(all(sum(row) == 8 for row in M))

    def test_charpoly_of_a_known_matrix(self):
        self.assertEqual(OS.characteristic_polynomial([[2, 1], [1, 2]]), [1, -4, 3])  # (x-1)(x-3)


class SurfaceLaws(unittest.TestCase):
    def test_depths_zero_to_three(self):
        for depth in range(4):
            self.assertTrue(SL.check(SL.measure(depth)))

    def test_known_values(self):
        row = SL.measure(2)
        self.assertEqual((row["boundary"], row["shared"], row["interfaces"]), (384, 576, [192, 576]))


class CoincidenceRate(unittest.TestCase):
    def test_rate(self):
        c, sizes, (depth, addresses, total) = CR.check()
        self.assertEqual((depth, addresses, total), (3, 336, 512))
        self.assertEqual(c[3:6], [176, 400, 848])


if __name__ == "__main__":
    unittest.main()
