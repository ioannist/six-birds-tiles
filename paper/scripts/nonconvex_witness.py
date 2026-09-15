#!/usr/bin/env python3
"""Exact witness that Q is not convex (ledger row O10).

Reads solid/r44_solid.json. Picks two vertices u, v of the mesh that are corners of the chair
carrier P adjacent to the missing corner cube, checks they are mesh vertices (hence in Q, which is
closed), and shows their midpoint m is not in Q by an exact ray-parity test against the closed
triangulated surface, along a generic rational direction. Standard library only.
"""
import json, sys
from fractions import Fraction as F
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
solid = json.loads((ROOT / "solid/r44_solid.json").read_text())
V = [tuple(F(c) for c in v) for v in solid["vertices"]]
T = solid["triangles"]
idx = {v: i for i, v in enumerate(V)}
u = (F(2), F(2), F(1)); v = (F(2), F(1), F(2))
assert u in idx and v in idx, "u, v must be mesh vertices"
m = tuple((a + b) / 2 for a, b in zip(u, v))          # (2, 3/2, 3/2)
d = (F(1), F(1, 7), F(1, 11))                            # generic rational direction

def sub(a, b): return tuple(x - y for x, y in zip(a, b))
def cross(a, b): return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])
def dot(a, b): return sum(x*y for x, y in zip(a, b))

def ray_hits(tri):
    """Exact Moller–Trumbore: does the ray m + t d (t > 0) meet the closed triangle? Reports
    degenerate (boundary) hits separately so the parity test can refuse them."""
    p0, p1, p2 = (V[i] for i in tri)
    e1, e2 = sub(p1, p0), sub(p2, p0)
    h = cross(d, e2); a = dot(e1, h)
    if a == 0: return None                                   # ray parallel to the plane
    s = sub(m, p0); b1 = dot(s, h) / a
    q = cross(s, e1); b2 = dot(d, q) / a
    t = dot(e2, q) / a
    if t <= 0: return False
    if b1 < 0 or b2 < 0 or b1 + b2 > 1: return False
    if b1 == 0 or b2 == 0 or b1 + b2 == 1 or t == 0: return "boundary"
    return True

def on_closed_triangle(pt, tri):
    """Exact test: is pt on the closed triangle (coplanar and inside or on an edge/vertex)?"""
    p0, p1, p2 = (V[i] for i in tri)
    n = cross(sub(p1, p0), sub(p2, p0))
    if dot(n, sub(pt, p0)) != 0: return False
    # barycentric via areas (exact rationals); pick a non-degenerate projection
    for (i, j) in ((0, 1), (0, 2), (1, 2)):
        det = (p1[i]-p0[i])*(p2[j]-p0[j]) - (p2[i]-p0[i])*(p1[j]-p0[j])
        if det != 0:
            a = ((pt[i]-p0[i])*(p2[j]-p0[j]) - (p2[i]-p0[i])*(pt[j]-p0[j])) / det
            b = ((p1[i]-p0[i])*(pt[j]-p0[j]) - (pt[i]-p0[i])*(p1[j]-p0[j])) / det
            return a >= 0 and b >= 0 and a + b <= 1
    return False

on_surface = sum(on_closed_triangle(m, tri) for tri in T)
print("triangles containing m (closed):", on_surface)
assert on_surface == 0, "m lies on the surface; parity test not applicable"

hits = 0; boundary = 0; parallel = 0
for tri in T:
    r = ray_hits(tri)
    if r is True: hits += 1
    elif r == "boundary": boundary += 1
    elif r is None: parallel += 1
print(f"u={u} v={v} both mesh vertices; m={m}; direction={d}")
print(f"proper crossings={hits}, boundary hits={boundary}, parallel triangles={parallel}")
assert boundary == 0, "degenerate ray; choose another direction"
inside = (hits % 2 == 1)
print("m inside Q:", inside)
# sanity: the same test on a point surely inside (centre of the cube at origin) and surely outside
def parity(pt):
    global m
    assert sum(on_closed_triangle(pt, tri) for tri in T) == 0, "control point on the surface"
    saved = m; m = pt; n = 0
    for tri in T:
        r = ray_hits(tri)
        assert r != "boundary"
        n += (r is True)
    m = saved; return n % 2 == 1
print("control: (1/2,1/2,1/2) inside:", parity((F(1,2),)*3), "; (3,3,3) inside:", parity((F(3),)*3))
print("STATUS:", "PASS (Q is not convex: u, v in Q, midpoint outside)" if not inside else "FAIL")
