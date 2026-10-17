#!/usr/bin/env python3
"""Surface and interface laws of the R44 supertiles (exact, standard library only).

Tier: T2, finite and replayed.  Built on ``patches.sigma_depth``; no new geometry.

For the depth-N patch (8**N copies of Q) the script counts unit faces of the
seven-cube chair shell and finds, for N = 0..4,

    boundary faces              = 24 * 4**N
    faces shared by two tiles   = 12 * (8**N - 4**N)
    boundary faces per direction = 4**(N+1)   for each of +-x, +-y, +-z
    B_c (interfaces at coarseness c) = 12 * 4**N * (2**c - 1)

The first identity is the second plus counting: 24 faces on each of 8**N tiles,
less two for every shared face.  The last is the law B_c = (T(c) P(N-c) - P(N))/2
with T(c) = 8**c tiles and P(k) = 24 * 4**k boundary faces, i.e. the same form
that the Spectre's supertile interfaces obey.  Coarseness c is the number of
leading substitution digits two tiles share: tiles in contact that first differ
at digit c+1.

Consequence.  The supertile boundary grows by nu = 4 = lambda**2 per level
against a linear inflation lambda = 2, so log nu / log lambda = 2 = d - 1: an
ordinary surface, with no fractal excess.  (For the planar Spectre the same
ratio is 1.399, above d - 1 = 1.)

``simulations/explore/lean/SurfaceLaws.lean`` proves the two counting identities
for every N in the Lean kernel with no library and no native compiler hook.

    python3 simulations/surface_laws.py [--max-depth 4]
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict

from patches import sigma_depth
from r44 import exposed_faces


def digits(depth):
    """Base-8 child indices of every depth-N copy, in sigma_depth order."""
    out = [()]
    for _ in range(depth):
        out = [d + (c,) for d in out for c in range(8)]
    return out


def measure(depth):
    poses = sigma_depth(depth)
    owners = defaultdict(list)
    for index, pose in enumerate(poses):
        for key, sign in exposed_faces(pose).items():
            owners[key].append((index, sign))
    normals = Counter((key[0], v[0][1]) for key, v in owners.items() if len(v) == 1)
    for key, v in owners.items():
        assert len(v) <= 2 and (len(v) == 1 or v[0][1] == -v[1][1]), "overlap or mismatched faces"
    shared = sum(1 for v in owners.values() if len(v) == 2)
    dig = digits(depth)
    interfaces = [
        sum(1 for v in owners.values()
            if len(v) == 2 and dig[v[0][0]][:c] != dig[v[1][0]][:c])
        for c in range(1, depth + 1)
    ]
    return {
        "depth": depth,
        "copies": len(poses),
        "boundary": sum(normals.values()),
        "shared": shared,
        "per_direction": sorted(set(normals.values())),
        "directions": len(normals),
        "interfaces": interfaces,
    }


def check(row):
    n = row["depth"]
    assert row["copies"] == 8 ** n
    assert row["boundary"] == 24 * 4 ** n
    assert row["shared"] == 12 * (8 ** n - 4 ** n)
    assert row["directions"] == 6 and row["per_direction"] == [4 ** (n + 1)]
    assert row["interfaces"] == [12 * 4 ** n * (2 ** c - 1) for c in range(1, n + 1)]
    # the interface law in the Spectre's form, T(c) = 8^c, P(k) = 24 * 4^k
    assert row["interfaces"] == [(8 ** c * 24 * 4 ** (n - c) - 24 * 4 ** n) // 2 for c in range(1, n + 1)]
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--max-depth", type=int, default=4)
    arguments = parser.parse_args()
    print("depth copies   boundary  shared   per-direction  interfaces B_1..B_N")
    for n in range(arguments.max_depth + 1):
        row = measure(n)
        check(row)
        print("%5d %6d %10d %7d %9d x6   %s" % (n, row["copies"], row["boundary"], row["shared"],
                                               row["per_direction"][0], row["interfaces"]))
    print("all laws hold: boundary = 24*4^N, shared = 12(8^N - 4^N), flat direction histogram,")
    print("B_c = 12*4^N*(2^c - 1) = (T(c)P(N-c) - P(N))/2;  D_b = log 4 / log 2 = 2 = d - 1")


if __name__ == "__main__":
    main()
