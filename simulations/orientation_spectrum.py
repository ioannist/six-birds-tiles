#!/usr/bin/env python3
"""Orientation transfer spectrum of the R44 substitution (exact, standard library only).

Tier: T2, finite and replayed.  Nothing here bears on the theorem or on any
Lean-checked statement.  It is a computation about the eight certified child
poses, and it answers a question the finite certificates do not ask: what does
the substitution do to *orientations*, as a linear map?

Let the 24 proper rotations be the species.  A tile in orientation F has eight
children, in orientations F*H for the eight child frames H of
``certificates/candidate_certificate.json``.  The count matrix is

    M[F][F'] = #{ children c : F * H_c = F' }          (24 x 24, entries 0..8)

and every statement below is exact integer or Fraction arithmetic:

  * characteristic polynomial  x^3 (x - 8) (x - 2)^20
  * M (M - 8)(M - 2) = 0, so the minimal polynomial is x (x - 8)(x - 2): M is
    diagonalizable and its zero sector is semisimple (rank M^n = 21 for all n >= 1)
  * every row and column sums to 8 (the number of children), the Perron
    eigenvalue, with the uniform vector as left and right eigenvector
  * so orientation frequencies tend to 1/24 each, and the error shrinks by
    exactly (2/8) = 1/4 per refinement
  * no negative eigenvalue; every eigenvalue is a rational integer

What this narrows.  The substitution inflates lengths by the integer 2.  The
Pisot route to pure-point diffraction and the irrational-frequency witness of
aperiodicity both need an inflation that is a Pisot number and tile frequencies
that are irrational.  Here the inflation is the integer 2 and every frequency
is rational (1/24), so neither applies.  The replacement is 2-adic and is
already recorded upstream (THEOREM.md: the 168-label cell substitution has a
modular coincidence, and the Lee-Moody / Schlottmann import gives pure-point,
limit-periodic structure; T3).  ``coincidence_rate.py`` adds an exact rate.

    python3 simulations/orientation_spectrum.py
    python3 simulations/orientation_spectrum.py --json
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction

from r44 import frame_determinant, frame_multiply, load_json, parse_pose


def rotations():
    out = []
    for permutation in itertools.permutations(range(3)):
        for signs in itertools.product((1, -1), repeat=3):
            frame = (permutation, signs)
            if frame_determinant(frame) == 1:
                out.append(frame)
    return out


def child_frames():
    certificate = load_json("certificates/candidate_certificate.json")
    return [parse_pose(pose)[0] for pose in certificate["children"]]


def orientation_matrix():
    species = rotations()
    index = {frame: i for i, frame in enumerate(species)}
    children = child_frames()
    assert all(frame_determinant(frame) == 1 for frame in children), "a child is a mirror image"
    matrix = [[0] * len(species) for _ in species]
    for frame in species:
        for child in children:
            matrix[index[frame]][index[frame_multiply(frame, child)]] += 1
    return species, matrix


# ----------------------------------------------------------- exact linear algebra
def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def multiply(a, b):
    n, m, p = len(a), len(b), len(b[0])
    return [[sum(a[i][k] * b[k][j] for k in range(m)) for j in range(p)] for i in range(n)]


def add(a, b, scale=1):
    return [[x + scale * y for x, y in zip(r, s)] for r, s in zip(a, b)]


def is_zero(a):
    return all(x == 0 for row in a for x in row)


def characteristic_polynomial(matrix):
    """Faddeev-LeVerrier over the integers: coefficients of x^n + c1 x^(n-1) + ... + cn."""
    n = len(matrix)
    coefficients = [1]
    current = identity(n)
    for k in range(1, n + 1):
        product = multiply(matrix, current)
        trace = sum(product[i][i] for i in range(n))
        c = Fraction(-trace, k)
        assert c.denominator == 1
        coefficients.append(int(c))
        current = add(product, identity(n), int(c))
    return coefficients


def divide_by_linear(coefficients, root):
    """Synthetic division by (x - root); returns (quotient, remainder)."""
    out = [coefficients[0]]
    for c in coefficients[1:]:
        out.append(c + root * out[-1])
    return out[:-1], out[-1]


def root_multiplicities(coefficients, candidates):
    found, rest = {}, list(coefficients)
    for r in candidates:
        m = 0
        while len(rest) > 1:
            quotient, remainder = divide_by_linear(rest, r)
            if remainder != 0:
                break
            rest, m = quotient, m + 1
        if m:
            found[r] = m
    return found, rest


def rank(matrix):
    rows = [[Fraction(x) for x in row] for row in matrix]
    r = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        rows[r] = [x / rows[r][col] for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


def spectrum():
    species, M = orientation_matrix()
    n = len(M)
    scalar = lambda c: [[c * int(i == j) for j in range(n)] for i in range(n)]
    cp = characteristic_polynomial(M)
    mult, rest = root_multiplicities(cp, (0, 8, 2, 1, -1, 3, 4, -2, -4, -8))
    minimal = multiply(multiply(M, add(M, scalar(8), -1)), add(M, scalar(2), -1))
    ranks, power = {}, identity(n)
    for k in range(1, 5):
        power = multiply(power, M)
        ranks[k] = rank(power)
    # frequencies: (M/8)^d against the uniform matrix J/24, exactly
    gaps, power = [], identity(n)
    for d in range(1, 7):
        power = multiply(power, M)
        scale = Fraction(8 ** d)
        gaps.append(max(abs(Fraction(x) / scale - Fraction(1, 24)) for row in power for x in row))
    return {
        "species": n,
        "charpoly_coefficients": cp,
        "root_multiplicities": mult,
        "charpoly_fully_factored": len(rest) == 1,
        "minimal_polynomial_divides_x_x8_x2": is_zero(minimal),
        "rank_M_to_n": ranks,
        "row_sums": sorted({sum(row) for row in M}),
        "column_sums": sorted({sum(col) for col in zip(*M)}),
        "frequency_gap": [str(g) for g in gaps],
        "gap_ratio": [str(gaps[i + 1] / gaps[i]) for i in range(len(gaps) - 1)],
        "children": len(child_frames()),
    }


def check(result):
    assert result["species"] == 24 and result["children"] == 8
    assert result["charpoly_fully_factored"]
    assert result["root_multiplicities"] == {0: 3, 8: 1, 2: 20}, result["root_multiplicities"]
    assert result["minimal_polynomial_divides_x_x8_x2"]
    assert set(result["rank_M_to_n"].values()) == {21}
    assert result["row_sums"] == result["column_sums"] == [8]
    assert all(r == "1/4" for r in result["gap_ratio"][1:]), result["gap_ratio"]
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args()
    result = spectrum()
    check(result)
    if arguments.json:
        print(json.dumps(result, indent=2))
        return
    print("orientation transfer matrix on the 24 rotations (exact)")
    print("  characteristic polynomial: x^%d (x-8)^%d (x-2)^%d"
          % (result["root_multiplicities"][0], result["root_multiplicities"][8], result["root_multiplicities"][2]))
    print("  minimal polynomial divides x(x-8)(x-2): %s  -> diagonalizable, zero sector semisimple"
          % result["minimal_polynomial_divides_x_x8_x2"])
    print("  rank M^n for n=1..4: %s" % list(result["rank_M_to_n"].values()))
    print("  row sums %s, column sums %s (eight children)" % (result["row_sums"], result["column_sums"]))
    print("  max |(M/8)^d - 1/24| for d=1..6: %s" % ", ".join(result["frequency_gap"]))
    print("  successive ratio of that gap: %s" % ", ".join(result["gap_ratio"]))
    print("  all eigenvalues are rational integers; the inflation is 2 and every frequency is 1/24,")
    print("  so the Pisot route to pure-point diffraction does not apply to R44")


if __name__ == "__main__":
    main()
