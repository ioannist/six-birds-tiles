#!/usr/bin/env python3
"""Exact planar boundary areas of Q on the nine coordinate planes x,y,z = 0,1,2 (Section 2, carrier
recovery; external review 2026-09-09, minor m2). Reads solid/r44_solid.json (exact rationals), sums
the triangles lying in each plane, and bounds the total area of all non-axis facets.

Exact arithmetic throughout (no floating point): a non-axis facet of doubled squared area q (a
rational) has area sqrt(q)/2 <= (q + m^2)/(4m) for every positive rational m (AM-GM); the witness m
is the integer square root of the numerator times the denominator, divided by the denominator.
Prints STATUS: PASS when the three area types are 2492/625 (height 0), 623/625 (height 1) and
1869/625 (height 2) on every axis and the non-axis total is below 1212/15625.
"""
import json
import math
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
solid = json.loads((ROOT / "solid/r44_solid.json").read_text())
V = [tuple(F(x) for x in v) for v in solid["vertices"]]
T = solid["triangles"]


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0])


def sqrt_upper(q):
    """A rational upper bound for sqrt(q), q a positive rational: (q + m^2) / (2m) with m ~ sqrt(q)."""
    m = F(math.isqrt(q.numerator * q.denominator), q.denominator)
    if m == 0:
        m = F(1)
    return (q + m * m) / (2 * m)


planar = {}
bound = F(0)          # exact upper bound for the total non-axis facet area
for t in T:
    a, b, c = (V[i] for i in t[:3])
    n = cross(tuple(b[k] - a[k] for k in range(3)), tuple(c[k] - a[k] for k in range(3)))
    axes = [k for k in range(3) if n[k] != 0]
    if len(axes) == 1 and a[axes[0]] in (0, 1, 2):
        key = (axes[0], int(a[axes[0]]))
        planar[key] = planar.get(key, F(0)) + abs(n[axes[0]]) / 2
    else:
        bound += sqrt_upper(sum(x * x for x in n)) / 2
expected = {0: F(2492, 625), 1: F(623, 625), 2: F(1869, 625)}
ok = all(planar.get((ax, h)) == expected[h] for ax in range(3) for h in (0, 1, 2)) and len(planar) == 9 \
    and bound < F(1212, 15625)
for ax in range(3):
    for h in (0, 1, 2):
        print(f"axis {ax} height {h}: {planar.get((ax, h))}")
print(f"non-axis facets: exact upper bound {bound} (about {bound.numerator * 10**6 // bound.denominator} e-6) "
      f"< 1212/15625")
print("STATUS:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
