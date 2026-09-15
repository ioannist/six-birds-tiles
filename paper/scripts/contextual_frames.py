#!/usr/bin/env python3
"""Exact three-frame interface check; prints only, stdlib, no theorem imports.

Scope: the 192 feature records in the canonical solid, not an independent mesh
audit or a verification of the monotile theorem. Diagonal packing is supplied
by the manuscript's subdivision; off-diagonal overlaps are detected locally.
"""

import json
from fractions import Fraction as F
from pathlib import Path


def cycle(vector, power):
    return vector[power:] + vector[:power]


def main():
    path = Path(__file__).resolve().parents[2] / "solid/r44_solid.json"
    solid = json.loads(path.read_text())
    features = []
    for patch in solid["patches"]:
        base = [tuple(map(F, vertex)) for vertex in patch["base"]]
        centre = tuple(sum(vertex[i] for vertex in base) / 4 for i in range(3))
        coefficient = patch["coefficient"]
        apex = tuple(map(F, patch["apex"]))
        normal = tuple((apex[i] - centre[i]) / (F(coefficient) / 10000)
                       for i in range(3))
        assert sum(abs(x) for x in normal) == 1
        assert all(x in (-1, 0, 1) for x in normal)
        features.append((centre, normal, coefficient, patch["role"]))
    assert len(features) == len({item[0] for item in features}) == 192
    witness = (F(5, 4), F(11, 8), F(1))
    matrix = []
    counts = []
    witness_seen = False
    for a in range(3):
        root = {cycle(c, a): (cycle(n, a), h, r) for c, n, h, r in features}
        row = []
        for b in range(3):
            contacts = []
            for centre, normal, height, role in features:
                centre = tuple(x + 1 for x in cycle(centre, b))
                normal = cycle(normal, b)
                if centre not in root:
                    continue
                rn, rh, rr = root[centre]
                if rn != tuple(-x for x in normal):
                    continue
                contacts.append((rh, height))
                if a == 0 and b == 1 and centre == witness:
                    assert (rr, rh, rn) == (188, 12, (0, 0, 1))
                    assert (role, height, normal) == (4, 5, (0, 0, -1))
                    witness_seen = True
            assert len(contacts) == 24
            mismatches = sum(h != -k for h, k in contacts)
            # At a shared base centre the root occupies z<h/10000,
            # the neighbour z>-k/10000 in the root's normal coordinate.
            # The strict interval is nonempty iff h+k>0.
            overlaps = sum(h + k > 0 for h, k in contacts)
            assert mismatches == (0 if a == b else 24)
            assert (overlaps > 0) == (a != b)
            row.append(int(mismatches == 0))
            counts.append({"a": a, "b": b, "centres": len(contacts),
                           "mismatches": mismatches, "overlap_sites": overlaps})
        matrix.append(row)
    assert witness_seen
    print(json.dumps({"compatibility": matrix, "pairs": counts,
                      "witness": {"point": list(map(str, witness)),
                                  "roles": [188, 4], "coefficients": [12, 5]},
                      "status": "PASS"}, indent=2))


if __name__ == "__main__":
    main()
