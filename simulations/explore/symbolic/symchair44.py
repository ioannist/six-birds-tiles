#!/usr/bin/env python3
r"""symchair44.py - the Chair44 / R44 solid generated from scratch, in sympy.

Optional second route (tier T2, exploratory).  The repository's canonical solid is
solid/r44_solid.json and its tools are standard-library only.  This module loads NOTHING:
every number is produced by the Python below, in exact sympy arithmetic, so that the
generator itself can be printed as LaTeX (--latex / --pdf).  It needs `pip install sympy`
and is deliberately outside verify/.  test_symchair44.py compares it with the canonical
JSON, the certificate and simulations/patches.py, which only the tests read.

Origin: written for the Spectre fork brentharts/spectre (symchair44.py), derived from the
data and papers of Ioannis Tsiokos (CC BY 4.0).  What it adds is an independent
re-derivation, not a new proof; the einstein theorem does not rest on it.

What is generated, and from what
  1. lattice      the chair = 2x2x2 cubes minus the corner (1,1,1): 7 unit cells.
  2. panels       its 24 exposed unit faces, sorted by (axis, doubled centre).
  3. sites        8 pyramid sites per panel at the centre offsets (+-1/8, +-1/4), (+-1/4, +-1/8).
  4. grid         the cut lines 0, 1/4 -+ w, 3/8 -+ w, 5/8 -+ w, 3/4 -+ w, 1 (w = base half-width)
                  give a 9 x 9 grid per panel; 8 cells are pyramid bases.
  5. substitution the 8 children of the 2-scaled chair, found by exact cover (6561 rotation-only
                  tilings exist) and selected by the contact rule below.
  6. labels       the 24 x 8 signed height classes, DERIVED: sites that meet across the
                  face-contacts of the hierarchy must be exact complements (c_A + c_B = 0), a
                  signed union-find over those equations leaves 12 free classes.
  7. mesh         vertices, edges, triangles; apex height = (label) * h along the outward normal.
  8. atlas       the contacts: 2388 raw face contacts -> 44 with exact complement -> 30 that the
                  hierarchy realizes; 372 site equations c_a + c_b = 0 of rank 180 (kernel 12).
Check: with symbols w, h free, V = 2138, E = 6408, F = 4272, chi = 2, and the volume is
exactly 7 for ALL w, h, because the heights cancel in complement pairs (sum of labels = 0).

    python3 symchair44.py --verify
    python3 symchair44.py --latex out.tex [--pdf]      # the generator as LaTeX
    python3 symchair44.py --obj out.obj [--exag 100]    # the numeric solid (w=1/100, h=1/10000)
    python3 symchair44.py --atlas [--latex out.tex --pdf]   # contact atlas 2388 -> 44 -> 30 (and as LaTeX)
    python3 symchair44.py --screen                      # re-derive the substitution (about 3 min)
"""
import argparse
import itertools
import os
import subprocess
import sys
from collections import defaultdict

import sympy as sp

R = sp.Rational

# ----------------------------------------------------------------------------- symbols
w, h = sp.symbols("w h", positive=True)          # pyramid base half-width, height unit
W0, H0 = R(1, 100), R(1, 10000)                  # the R44 values
NUMERIC = {w: W0, h: H0}


# ------------------------------------------------------------------------- 1. lattice
CELLS = [c for c in itertools.product((0, 1), repeat=3) if c != (1, 1, 1)]


def frame_matrix(frame):
    """Signed permutation matrix of a frame (perm, signs):  (G x)_i = s_i x_{p_i}."""
    p, s = frame
    M = sp.zeros(3, 3)
    for i in range(3):
        M[i, p[i]] = s[i]
    return M


def all_frames():
    return [(p, s) for p in itertools.permutations(range(3)) for s in itertools.product((1, -1), repeat=3)]


def frame_det(frame):
    return int(frame_matrix(frame).det())


def frame_apply(frame, x):
    p, s = frame
    return tuple(s[i] * x[p[i]] for i in range(3))


def frame_mul(f, g):
    """f o g as a frame."""
    (p, s), (q, r) = f, g
    return tuple(q[p[i]] for i in range(3)), tuple(s[i] * r[p[i]] for i in range(3))


IDENTITY = ((0, 1, 2), (1, 1, 1))


def pose_matrix(pose):
    """The affine 3x4 matrix [G | t], the analogue of symspectre's 2x3 transformations."""
    f, t = pose
    return frame_matrix(f).row_join(sp.Matrix(t))


def mul_pose(A, B):
    """Symbolic composition of affine 3x4 maps, as in symspectre.mul_sympy."""
    AB = sp.Matrix(A)
    AB[:, :3] = A[:, :3] * B[:, :3]
    AB[:, 3] = A[:, :3] * B[:, 3] + A[:, 3]
    return AB


def refine_matrix(parent, child):
    """Refinement of a pose by a child of the root: (G, t) -> (G H, 2 t + G u)."""
    out = sp.Matrix(parent)
    out[:, :3] = parent[:, :3] * child[:, :3]
    out[:, 3] = 2 * parent[:, 3] + parent[:, :3] * child[:, 3]
    return out


def pose_cells(pose):
    """Unit cells (lower corners) of the chair placed by pose = (frame, translation)."""
    f, t = pose
    out = []
    for c in CELLS:
        x = frame_apply(f, c)
        out.append(tuple(x[i] + t[i] - (1 if f[1][i] < 0 else 0) for i in range(3)))
    return frozenset(out)


def exposed_faces(pose):
    """{(axis, doubled face centre): outward sign} for the unit faces on the chair surface."""
    cells = pose_cells(pose)
    out = {}
    for c in cells:
        for ax in range(3):
            for sd in (-1, 1):
                n = list(c)
                n[ax] += sd
                if tuple(n) in cells:
                    continue
                k = [2 * v + 1 for v in c]
                k[ax] += sd
                out[(ax, tuple(k))] = sd
    return out


ROOT = (IDENTITY, (0, 0, 0))


# --------------------------------------------------------------------------- 2. panels
_FACES = exposed_faces(ROOT)
PANELS = sorted(_FACES)                                   # [(axis, doubled centre)]
PANEL_SIGN = [_FACES[p] for p in PANELS]
PANEL_CENTRE = [tuple(R(v, 2) for v in k) for _, k in PANELS]
PANEL_AXES = [tuple(a for a in range(3) if a != ax) for ax, _ in PANELS]     # in-plane (u, v)
# orientation of (u, v, normal): +1 if e_u x e_v = +e_axis
PANEL_HANDED = [(-1 if ax == 1 else 1) for ax, _ in PANELS]
assert len(PANELS) == 24


# ---------------------------------------------------------------------------- 3. sites
# role = 8 * panel + k ; centre offset in the panel plane, (u, v) = increasing axes
SITE_OFFSETS = ([(R(a, 8), R(b, 4)) for a in (-1, 1) for b in (-1, 1)] +
                [(R(a, 4), R(b, 8)) for a in (-1, 1) for b in (-1, 1)])
SITES = []                                                # role -> (panel, native centre)
for _pi in range(24):
    _u, _v = PANEL_AXES[_pi]
    for _du, _dv in SITE_OFFSETS:
        _c = list(PANEL_CENTRE[_pi])
        _c[_u] += _du
        _c[_v] += _dv
        SITES.append((_pi, tuple(_c)))


# ----------------------------------------------------------------------------- 4. grid
def grid_lines(width=w):
    """The cut lines of a unit panel as exact expressions in the base half-width."""
    pts = [R(0)]
    for c in (R(1, 4), R(3, 8), R(5, 8), R(3, 4)):
        pts += [c - width, c + width]
    pts.append(R(1))
    return pts


GRID = grid_lines()
# a site occupies the grid cell whose lower line is (its centre coordinate - w)
_CELL_INDEX = {R(1, 2) + o: GRID.index(R(1, 2) + o - w) for o in (R(-1, 4), R(-1, 8), R(1, 8), R(1, 4))}
SITE_CELL = [(_CELL_INDEX[R(1, 2) + du], _CELL_INDEX[R(1, 2) + dv]) for du, dv in SITE_OFFSETS]


# ------------------------------------------------------------------ 5. the substitution
def double_chair():
    """The chair scaled by 2, as unit cells: 56 of them."""
    return frozenset(tuple(2 * c[i] + d[i] for i in range(3)) for c in CELLS
                     for d in itertools.product((0, 1), repeat=3))


def double_chair_tilings(rotations_only=True):
    """Every way of tiling the 2-scaled chair by 8 chairs (exact cover, bitmask search).

    Returns a sorted list of tilings, each a sorted tuple of 8 poses (frame, translation)."""
    target = double_chair()
    cellbit = {c: i for i, c in enumerate(sorted(target))}
    pieces = []
    for f in all_frames():
        if rotations_only and frame_det(f) != 1:
            continue
        for t in itertools.product(range(-1, 5), repeat=3):
            cs = pose_cells((f, t))
            if cs <= target:
                pieces.append(((f, t), sum(1 << cellbit[c] for c in cs)))
    by_bit = [[i for i, (_, m) in enumerate(pieces) if m >> b & 1] for b in range(len(cellbit))]
    full = (1 << len(cellbit)) - 1
    sols = []

    def rec(cov, chosen):
        if cov == full:
            sols.append(tuple(sorted(pieces[i][0] for i in chosen)))
            return
        best, bn = None, 10 ** 9
        for b in range(len(cellbit)):
            if not cov >> b & 1:
                n = sum(1 for i in by_bit[b] if not pieces[i][1] & cov)
                if n < bn:
                    best, bn = b, n
                if n == 0:
                    return
        for i in by_bit[best]:
            if not pieces[i][1] & cov:
                rec(cov | pieces[i][1], chosen + [i])

    rec(0, [])
    return sorted(sols)


def refine_pose(pose, children):
    (G, t) = pose
    return [(frame_mul(G, H), tuple(2 * t[i] + frame_apply(G, u)[i] for i in range(3))) for H, u in children]


def sigma_poses(children, depth):
    poses = [ROOT]
    for _ in range(depth):
        poses = [c for p in poses for c in refine_pose(p, children)]
    return poses


# -------------------------------------------------------- 6. labels from contact equations
# integer shadows of the exact tables (every site coordinate is a multiple of 1/8)
SITES8 = [tuple(int(8 * x) for x in c) for _, c in SITES]
PANEL_KEY = [k for _, k in PANELS]                          # doubled centres (ints)


def pose_panel_faces(pose):
    """{(axis, doubled centre): (native panel, outward sign)} of the chair placed by `pose`."""
    G, t = pose
    out = {}
    for pi, (ax, _) in enumerate(PANELS):
        n = [0, 0, 0]
        n[ax] = PANEL_SIGN[pi]
        n2 = frame_apply(G, n)
        ax2 = next(i for i in range(3) if n2[i])
        k2 = tuple(a + 2 * b for a, b in zip(frame_apply(G, PANEL_KEY[pi]), t))
        out[(ax2, k2)] = (pi, n2[ax2])
    return out


def pose_sites(pose):
    """World positions of the 192 sites, in eighths."""
    G, t = pose
    return [tuple(a + 8 * b for a, b in zip(frame_apply(G, SITES8[r]), t)) for r in range(192)]


def gluing(children, depth=2):
    """Signed union-find over the exact-complement equations c_A + c_B = 0 of a hierarchy patch.

    Returns (classes, contradictions, equations): classes = list of [(role, parity)], where the
    parity says whether a role carries +class or -class; a class is dead if it contradicts itself."""
    poses = sigma_poses(children, depth)
    owners = defaultdict(list)
    sites = {}
    for i, p in enumerate(poses):
        sites[i] = pose_sites(p)
        for key, (pi, s) in pose_panel_faces(p).items():
            owners[key].append((i, pi, s))
    parent, parity = list(range(192)), [0] * 192

    def find(x):
        if parent[x] == x:
            return x, 0
        r, p = find(parent[x])
        parent[x], parity[x] = r, parity[x] ^ p
        return r, parity[x]

    dead, neq = set(), 0
    for key, v in owners.items():
        if len(v) != 2:
            continue
        (i, pi, si), (j, pj, sj) = v
        assert si == -sj
        where = {sites[i][pi * 8 + k]: pi * 8 + k for k in range(8)}
        for k in range(8):
            rb = pj * 8 + k
            ra = where.get(sites[j][rb])
            if ra is None:
                return None                      # sites do not coincide: not a legal gluing
            (a, pa), (b, pb) = find(ra), find(rb)
            neq += 1
            if a == b:
                if pa == pb:
                    dead.add(a)                  # c = -c
            else:
                parent[a], parity[a] = b, pa ^ pb ^ 1
    groups = defaultdict(list)
    for r in range(192):
        a, p = find(r)
        groups[a].append((r, p))
    dead = {find(d)[0] for d in dead}
    return list(groups.values()), dead, neq


def label_table(children, depth=2):
    """Signed class labels (1..12) for the 192 roles: classes are numbered by first appearance
    in (panel, site) order and each class is signed + at its first appearance."""
    classes, dead, _ = gluing(children, depth)
    assert not dead
    cls = {}
    for g in classes:
        for r, p in g:
            cls[r] = (id(g), p)
    number, lab = {}, [0] * 192
    first_par = {}
    for r in range(192):
        gid, p = cls[r]
        if gid not in number:
            number[gid] = len(number) + 1
            first_par[gid] = p
        lab[r] = number[gid] * (1 if p == first_par[gid] else -1)
    return lab


def child_order(pose):
    """Corner children (translation entries in {0, 4}) in lexicographic order, the interior child last."""
    t = pose[1]
    return (0 if all(x in (0, 4) for x in t) else 1, t)


def orientations(children):
    """Number of distinct cube rotations used by the depth-2 patch (24 = all of them)."""
    F = {f for f, _ in children}
    return len({frame_mul(a, b) for a in F for b in F})


def screen_tilings(verbose=True):
    """The selection rule, run in full (about 3 minutes):

    among the 6561 rotation-only tilings of the doubled chair, keep those whose contact equations
    leave the MOST free height classes (the kernel), then those using the most orientations in the
    depth-2 patch, then the first in sorted order.  Returns (chosen, summary)."""
    tilings = double_chair_tilings()
    kern = []
    for t in tilings:
        g = gluing(list(t), 2)
        kern.append(-1 if g is None or g[1] else len(g[0]))
    best = max(kern)
    top = [t for t, k in zip(tilings, kern) if k == best]
    div = [orientations(t) for t in top]
    pick = [t for t, d in zip(top, div) if d == max(div)]
    chosen = tuple(sorted(pick[0], key=child_order))
    hist = defaultdict(int)
    for k in kern:
        hist[k] += 1
    summary = {"tilings": len(tilings), "classes_histogram": dict(sorted(hist.items())),
               "max_classes": best, "survivors": len(top), "survivor_orientations": sorted(set(div)),
               "after_orientation_rule": len(pick)}
    if verbose:
        print("  %d rotation-only tilings of the doubled chair" % len(tilings))
        print("  free height classes (kernel dimension) over all tilings:", summary["classes_histogram"])
        print("  %d tilings reach the maximum (%d); orientations used: %s -> %d keep all 24" % (
            len(top), best, summary["survivor_orientations"], len(pick)))
    return chosen, summary


# The result of screen_tilings(), recorded so that ordinary runs need not repeat the 3-minute
# search.  verify() re-checks that it tiles the doubled chair and leaves 12 classes;
# `symchair44.py --screen` re-derives it from scratch.
CHILDREN = tuple(sorted([
    ((((0, 1, 2), (1, 1, 1)), (0, 0, 0))),
    ((((1, 0, 2), (1, 1, -1)), (0, 0, 4))),
    ((((0, 2, 1), (1, -1, 1)), (0, 4, 0))),
    ((((2, 0, 1), (1, -1, -1)), (0, 4, 4))),
    ((((2, 1, 0), (-1, 1, 1)), (4, 0, 0))),
    ((((1, 2, 0), (-1, 1, -1)), (4, 0, 4))),
    ((((0, 1, 2), (-1, -1, 1)), (4, 4, 0))),
    ((((0, 1, 2), (1, 1, 1)), (1, 1, 1))),
], key=child_order))


# ------------------------------------------------------------------------------ 7. mesh
class Solid:
    """vertices (3-tuples of sympy expressions), oriented triangles (index triples), edges."""

    def __init__(self, labels, symbolic=False, hscale=1):
        self.labels = list(labels)
        self.symbolic = symbolic
        W, H = (w, h) if symbolic else (W0, H0 * hscale)
        self.vertices, self.triangles = [], []
        index = {}

        def vid(p):
            p = tuple(sp.sympify(x) for x in p)
            if p not in index:
                index[p] = len(self.vertices)
                self.vertices.append(p)
            return index[p]

        grid = grid_lines(W)
        site_at = {SITE_CELL[k]: k for k in range(8)}
        for pi, (ax, key) in enumerate(PANELS):
            sd, (u, v) = PANEL_SIGN[pi], PANEL_AXES[pi]
            ccw = sd * PANEL_HANDED[pi] > 0
            org = [R(x, 2) for x in key]
            org[u] -= R(1, 2)
            org[v] -= R(1, 2)

            def P(iu, iv):
                q = list(org)
                q[u] = q[u] + grid[iu]
                q[v] = q[v] + grid[iv]
                return tuple(q)

            def tri(a, b, c):
                self.triangles.append((vid(a), vid(b), vid(c)) if ccw else (vid(a), vid(c), vid(b)))

            for iu in range(9):
                for iv in range(9):
                    a, b, c, d = P(iu, iv), P(iu + 1, iv), P(iu + 1, iv + 1), P(iu, iv + 1)
                    if (iu, iv) in site_at:
                        label = self.labels[8 * pi + site_at[(iu, iv)]]
                        apex = [(a[i] + c[i]) / 2 for i in range(3)]
                        apex[ax] = R(key[ax], 2) + sd * label * H
                        for p, q in ((a, b), (b, c), (c, d), (d, a)):
                            tri(p, q, tuple(apex))
                    elif ccw:                                   # flat cell, diagonal fixed per orientation
                        tri(a, b, c)
                        tri(a, c, d)
                    else:
                        tri(a, b, d)
                        tri(b, c, d)
        es = set()
        for t in self.triangles:
            for i in range(3):
                es.add(tuple(sorted((t[i], t[(i + 1) % 3]))))
        self.edges = sorted(es)

    # ---- invariants
    def euler(self):
        return len(self.vertices) - len(self.edges) + len(self.triangles)

    def is_closed_manifold(self):
        """Every directed edge appears once, and its reverse once: a closed oriented surface."""
        directed = defaultdict(int)
        for t in self.triangles:
            for i in range(3):
                directed[(t[i], t[(i + 1) % 3])] += 1
        return all(c == 1 and directed.get((b, a)) == 1 for (a, b), c in directed.items())

    def volume(self):
        """Divergence theorem: sum of det[a b c] / 6 over the oriented triangles (exact)."""
        total = []
        for i, j, k in self.triangles:
            a, b, c = self.vertices[i], self.vertices[j], self.vertices[k]
            total.append(a[0] * (b[1] * c[2] - b[2] * c[1]) - a[1] * (b[0] * c[2] - b[2] * c[0])
                         + a[2] * (b[0] * c[1] - b[1] * c[0]))
        return sp.expand(sp.Add(*total) / 6)

    def numeric(self):
        sub = NUMERIC if self.symbolic else {}
        return [tuple(float(x.subs(sub)) for x in v) for v in self.vertices]

    def obj(self):
        """Wavefront OBJ text (build the Solid with hscale > 1 to make the pyramids visible; beyond hscale ~ 100 the
        exaggerated apexes start to coincide with other vertices)."""
        lines = ["# Chair44 generated by symchair44.py: w=1/100, h=%s" % (H0,)]
        lines += ["v %.9f %.9f %.9f" % v for v in self.numeric()]
        lines += ["f %d %d %d" % (a + 1, b + 1, c + 1) for a, b, c in self.triangles]
        return "\n".join(lines) + "\n"


# ----------------------------------------------------------------------- 8. contact atlas
def frame_inv(f):
    p, s = f
    q = tuple(p.index(j) for j in range(3))
    return q, tuple(s[q[j]] for j in range(3))


def relative_pose(root, other):
    """`other` expressed in the native coordinates of `root`:  root^-1 o other."""
    inv = frame_inv(root[0])
    return frame_mul(inv, other[0]), tuple(x for x in frame_apply(inv, tuple(b - a for a, b in zip(root[1], other[1]))))


def pose_inverse(pose):
    return relative_pose(pose, ROOT)


_RAW = None


def raw_contacts():
    """Every pose at which a second chair touches the root across unit faces without overlap
    (rotations and mirror images allowed).  2388 of them, half mirror images."""
    global _RAW
    if _RAW is None:
        root_cells, root_faces = pose_cells(ROOT), exposed_faces(ROOT)
        out = []
        for f in all_frames():
            for t in itertools.product(range(-4, 5), repeat=3):
                pose = (f, t)
                if pose_cells(pose) & root_cells:
                    continue
                if any(k in root_faces and root_faces[k] == -sd for k, sd in exposed_faces(pose).items()):
                    out.append(pose)
        _RAW = out
    return _RAW


def shared_faces(pose):
    """[(root panel, other panel, face key)] for the unit faces across which `pose` touches the root."""
    root, other = pose_panel_faces(ROOT), pose_panel_faces(pose)
    return sorted((root[k][0], pj, k) for k, (pj, sj) in other.items() if k in root and root[k][1] == -sj)


def site_pairs(pose):
    """Pyramid sites that coincide across the contact: ([(root role, other role)], unmatched roles)."""
    A, B = pose_sites(ROOT), pose_sites(pose)
    pairs, loose = [], []
    for pi, pj, _ in shared_faces(pose):
        where = {A[pi * 8 + k]: pi * 8 + k for k in range(8)}
        seen = set()
        for m in range(8):
            ra = where.get(B[pj * 8 + m])
            if ra is None:
                loose.append(pj * 8 + m)
            else:
                pairs.append((ra, pj * 8 + m))
                seen.add(ra)
        loose += [pi * 8 + k for k in range(8) if pi * 8 + k not in seen]
    return pairs, loose


def is_legal(pose, labels):
    """Exact complement on every shared face: matched sites sum to zero, every pyramid is matched
    (an unmatched pyramid would leave a void or a collision)."""
    pairs, loose = site_pairs(pose)
    return not loose and all(labels[a] + labels[b] == 0 for a, b in pairs)


def legal_contacts(labels):
    return [p for p in raw_contacts() if is_legal(p, labels)]


def realized_contacts(children, depth=3):
    """Relative poses of face-adjacent tile pairs that actually occur in the depth-`depth` patch."""
    poses = sigma_poses(children, depth)
    owners = defaultdict(list)
    for i, p in enumerate(poses):
        for key in pose_panel_faces(p):
            owners[key].append(i)
    out = set()
    for v in owners.values():
        if len(v) == 2:
            a, b = v
            out.add(relative_pose(poses[a], poses[b]))
            out.add(relative_pose(poses[b], poses[a]))
    return out


def contact_equations(contacts):
    """Distinct pairs {role a, role b} that must satisfy c_a + c_b = 0 over a set of contacts."""
    eqs = set()
    for p in contacts:
        pairs, _ = site_pairs(p)
        eqs |= {frozenset(x) for x in pairs}
    return eqs


def equation_rank(eqs):
    import numpy as np
    A = np.zeros((len(eqs), 192))
    for i, e in enumerate(sorted(tuple(sorted(e)) for e in eqs)):
        A[i, e[0]] = A[i, e[1]] = 1
    return int(np.linalg.matrix_rank(A))


def rotation_data(frame):
    """(angle, axis) of a proper rotation as exact sympy objects (axis None for the identity)."""
    G = frame_matrix(frame)
    assert G.det() == 1
    tr = G.trace()
    angle = sp.acos(R(int(tr) - 1, 2))
    if G == sp.eye(3):
        return angle, None
    v = (G - sp.eye(3)).nullspace()[0]
    first = next(x for x in v if x != 0)
    return angle, (v / first if first < 0 else v).T


def atlas(children=None):
    """The whole contact atlas, computed: raw -> legal -> realized."""
    ch = children if children is not None else CHILDREN
    labels = label_table(ch)
    raw = raw_contacts()
    legal = legal_contacts(labels)
    real = realized_contacts(ch)
    eqs = contact_equations(real)
    return {"labels": labels, "raw": raw, "mirror": sum(1 for p in raw if frame_det(p[0]) < 0),
            "legal": sorted(legal), "realized": sorted(real),
            "unrealized": sorted(set(legal) - real), "equations": eqs}


def verify_atlas(A=None, verbose=True):
    A = A or atlas()
    legal, real = set(A["legal"]), set(A["realized"])
    report = []

    def check(name, ok, detail=""):
        report.append((name, bool(ok)))
        if verbose:
            print("  %-62s %s %s" % (name, "ok" if ok else "FAIL", detail))

    check("raw face contacts", len(A["raw"]) == 2388, "%d (%d mirror images)" % (len(A["raw"]), A["mirror"]))
    check("exact-complement legal contacts", len(legal) == 44, str(len(legal)))
    check("every legal contact is a proper rotation", all(frame_det(p[0]) == 1 for p in legal))
    check("realized contacts occur among the legal ones", len(real) == 30 and real <= legal, "%d of %d" % (len(real), len(legal)))
    check("legal but never realized", len(legal - real) == 14, str(len(legal - real)))
    inv = lambda S_: {pose_inverse(p) for p in S_}
    check("legal and realized sets are closed under inverse", inv(legal) == legal and inv(real) == real)
    nq = len(A["equations"])
    rk = equation_rank(A["equations"])
    check("site equations c_a + c_b = 0 over the 30 contacts", nq == 372, "%d equations, rank %d, kernel %d" % (nq, rk, 192 - rk))
    check("kernel dimension = 12 free height classes", 192 - rk == 12)
    return all(ok for _, ok in report), report


# --------------------------------------------------------------------------- verification
def verify(solid=None, children=None, symbolic=False, verbose=True):
    """Every claim here is computed, none is read from a file."""
    ch = children if children is not None else CHILDREN
    lab = label_table(ch)
    solid = solid or Solid(lab, symbolic=symbolic)
    report = []

    def check(name, ok, detail=""):
        report.append((name, bool(ok), detail))
        if verbose:
            print("  %-62s %s %s" % (name, "ok" if ok else "FAIL", detail))

    classes, dead, neq = gluing(ch, 3)
    check("seven unit cells, 24 panels, 192 sites", len(CELLS) == 7 and len(PANELS) == 24 and len(SITES) == 192)
    check("children tile the doubled chair (8 chairs, 56 cells)",
          len(ch) == 8 and set().union(*[pose_cells(c) for c in ch]) == double_chair()
          and sum(len(pose_cells(c)) for c in ch) == 56)
    check("gluing equations consistent on the depth-3 patch", not dead, "%d equations" % neq)
    check("12 free height classes", len(classes) == 12, "(kernel dimension)")
    check("labels use exactly the classes 1..12 (with signs)", sorted(set(map(abs, lab))) == list(range(1, 13)))
    check("sum of all 192 labels = 0 (volume independent of w, h)", sum(lab) == 0, "sum = %d" % sum(lab))
    check("vertices", len(solid.vertices) == 2138, str(len(solid.vertices)))
    check("edges", len(solid.edges) == 6408, str(len(solid.edges)))
    check("triangles", len(solid.triangles) == 4272, str(len(solid.triangles)))
    check("Euler characteristic 2", solid.euler() == 2)
    check("closed oriented 2-manifold", solid.is_closed_manifold())
    vol = solid.volume()
    check("volume = 7 exactly" + (" (for all w, h)" if solid.symbolic else ""), vol == 7, "= %s" % vol)
    return all(ok for _, ok, _ in report), report, solid


# ------------------------------------------------------------------------------ LaTeX
def _pm(M, env="pmatrix"):
    """Clean LaTeX matrix (sympy's own wrapper adds a second pair of brackets)."""
    M = sp.Matrix(M)
    rows = [" & ".join(sp.latex(M[i, j]) for j in range(M.cols)) for i in range(M.rows)]
    return r"\begin{%s} %s \end{%s}" % (env, r" \\ ".join(rows), env)


def _tex_table(rows, header):
    cols = "rccl" if len(header) == 4 else "r" * len(header)
    out = [r"\begin{tabular}{%s}" % cols, r"\hline", " & ".join(header) + r" \\", r"\hline"]
    out += [" & ".join(str(c) for c in r) + r" \\" for r in rows]
    out += [r"\hline", r"\end{tabular}"]
    return "\n".join(out)


def latex_document(children=None, solid=None, atlas_data=None):
    """The generator as a LaTeX document: every formula is sp.latex of the object the code uses."""
    ch = children if children is not None else CHILDREN
    lab = label_table(ch)
    solid = solid or Solid(lab)
    L = sp.latex
    ex, ey = sp.symbols(r"e_u e_v")
    tex = [r"""\documentclass{article}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{longtable}
\usepackage[a4paper, margin=0.9in]{geometry}
\setcounter{MaxMatrixCols}{20}
\begin{document}
\title{The R44 chair, generated symbolically}
\date{}
\maketitle
This document is produced by \texttt{symchair44.py}: every matrix below is \texttt{sympy.latex} of the
object the generator uses, and nothing is read from a data file.
"""]
    tex.append(r"\section*{Parameters}")
    tex.append(r"\begin{equation*} w = %s,\qquad h = %s \end{equation*}" % (L(W0), L(H0)))
    tex.append(r"\section*{The chair: seven unit cells}")
    tex.append(r"\begin{equation*} \mathcal{C} = \{0,1\}^3 \setminus \{(1,1,1)\}"
               r" = \left\{%s\right\} \end{equation*}" % ",\\ ".join(_pm(sp.Matrix(c).T) for c in CELLS))
    tex.append(r"\section*{Panels}")
    tex.append(r"The 24 exposed unit faces, sorted by (axis, doubled centre); the centre $\mathbf{c}_p$ is a half-integer vector.")
    rows = [(i, "xyz"[ax], "%+d" % PANEL_SIGN[i], "$\\left(%s\\right)$" % ",\\,".join(L(x) for x in PANEL_CENTRE[i]))
            for i, (ax, _) in enumerate(PANELS)]
    tex.append(r"\begin{center}\small")
    tex.append(_tex_table(rows, ["$p$", "normal", "sign", r"centre $\mathbf c_p$"]))
    tex.append(r"\end{center}")
    tex.append(r"\section*{Pyramid sites and the cut-line grid}")
    tex.append(r"\begin{equation*} \text{offsets }(\delta_u,\delta_v)_k = %s,\qquad k=0,\dots,7 \end{equation*}"
               % L(sp.Matrix(SITE_OFFSETS)))
    tex.append(r"\begin{equation*} \mathbf{g}(w) = %s \end{equation*}" % L(sp.Matrix(GRID).T))
    tex.append(r"A site at offset $\delta$ occupies the grid cell whose lower line is $\tfrac12+\delta-w$; "
               r"the cell indices are $%s$." % L(sp.Matrix(SITE_CELL)))
    j, s_, cu, cv, cn = sp.symbols(r"\gamma s c_u c_v c_n")
    base = sp.Matrix([[cu + 0 - w, cv - w, cn], [cu + w, cv - w, cn], [cu + w, cv + w, cn],
                      [cu - w, cv + w, cn], [cu, cv, cn + s_ * j * h]])
    tex.append(r"\section*{A pyramid}")
    tex.append(r"Rows: the four base corners and the apex, in (in-plane $u$, in-plane $v$, normal) coordinates; "
               r"$s=\pm1$ is the outward sign and $\gamma\in\{\pm1,\dots,\pm12\}$ the signed height class.")
    tex.append(r"\begin{equation*} %s \end{equation*}" % _pm(base))
    tex.append(r"\section*{Substitution}")
    tex.append(r"Eight chairs tile the doubled chair; their poses $[G\,|\,t]$ (rotations only):")
    for i, pose in enumerate(ch):
        tex.append(r"\begin{equation*} A_%d = %s \end{equation*}" % (i, _pm(pose_matrix(pose))))
    tex.append(r"Refinement of a pose: $[G\,|\,t]\mapsto[GH\,|\,2t+Gu]$, i.e.")
    Gs, ts, Hs, us = (sp.MatrixSymbol(n, a, b) for n, a, b in (("G", 3, 3), ("t", 3, 1), ("H", 3, 3), ("u", 3, 1)))
    tex.append(r"\begin{equation*} \begin{pmatrix} G & t\end{pmatrix}\ast\begin{pmatrix} H & u\end{pmatrix}"
               r" = \begin{pmatrix} GH & 2t+Gu\end{pmatrix} \end{equation*}")
    tex.append(r"\section*{Height classes}")
    tex.append(r"On a face contact, sites coincide and the heights are exact complements, "
               r"$\gamma_A+\gamma_B=0$.  A signed union-find over all contacts of the depth-2 patch "
               r"leaves 12 free classes; numbering them by first appearance gives the $24\times 8$ table "
               r"(row $p$ = panel, column $k$ = site):")
    T = sp.Matrix(24, 8, lab)
    tex.append(r"\begin{equation*}\scriptsize %s \end{equation*}" % _pm(T, "bmatrix"))
    tex.append(r"\section*{The solid}")
    tex.append(r"Each panel is cut by the grid into $9\times9$ cells; the 8 site cells carry pyramids "
               r"(4 triangles each), the other 73 are split along one diagonal (2 triangles each): $73\cdot 2+8\cdot4=178$ "
               r"triangles per panel, $24\cdot178=4272$ in all.")
    tex.append(r"\begin{equation*} V=%d,\quad E=%d,\quad F=%d,\quad V-E+F=%d \end{equation*}" %
               (len(solid.vertices), len(solid.edges), len(solid.triangles), solid.euler()))
    tex.append(r"\begin{equation*} \operatorname{vol}=\frac16\sum_{\text{triangles}}\det[a\;b\;c]"
               r" = 7 + \tfrac43 w^2 h\sum_{p,k}\gamma_{p,k} = %s \quad(\textstyle\sum\gamma=%d) \end{equation*}" %
               (L(sp.Integer(7)), sum(lab)))
    if atlas_data:
        tex.append(atlas_latex(atlas_data))
    tex.append(r"\end{document}")
    return "\n".join(tex) + "\n"


def _contact_rows(poses, labels):
    L = sp.latex
    rows = []
    for n, pose in enumerate(poses, 1):
        ang, axis = rotation_data(pose[0])
        fs = shared_faces(pose)
        pairs = ",".join("%d\\!\\mapsto\\!%d" % (a, b) for a, b, _ in fs)
        rows.append("%d & $\\scriptstyle %s$ & $%s$ & $%s$ & %d & $\\scriptstyle %s$ \\\\" % (
            n, _pm(pose_matrix(pose)), L(ang), "-" if axis is None else _pm(axis),
            len(fs), pairs))
    return rows


def atlas_latex(A):
    """The contact atlas as a LaTeX section: counts, the equations, a worked example, and the contacts."""
    L = sp.latex
    labels = A["labels"]
    tex = [r"\clearpage", r"\section*{The contact atlas}"]
    tex.append(r"A second chair touches the root across unit faces at a pose $T=[G\,|\,t]$ (relative to the root). "
               r"Of the %d such non-overlapping poses, %d are mirror images. Where pyramid sites coincide across the "
               r"shared faces the heights must be exact complements, and every pyramid must be matched (otherwise "
               r"a void or a collision remains):" % (len(A["raw"]), A["mirror"]))
    tex.append(r"\begin{equation*} \gamma_{r}+\gamma_{r'}=0\quad\text{for every coincident pair }(r,r'),\qquad r=8p+k \end{equation*}")
    tex.append(r"\begin{equation*} %d \;\xrightarrow{\ \text{exact complement}\ }\; %d \;\xrightarrow{\ \text{realized in the hierarchy}\ }\; %d "
               r"\qquad(\text{the other }%d\text{ are legal but never occur}) \end{equation*}" % (
                   len(A["raw"]), len(A["legal"]), len(A["realized"]), len(A["unrealized"])))
    rk = equation_rank(A["equations"])
    tex.append(r"All %d legal contacts are proper rotations. The %d contacts that occur in the hierarchy yield "
               r"%d distinct equations $\gamma_r+\gamma_{r'}=0$; as a linear system $M\gamma=0$ with $M\in\{0,1\}^{%d\times192}$ "
               r"it has rank %d, so the kernel has dimension $192-%d=%d$: the 12 free height classes." % (
                   len(A["legal"]), len(A["realized"]), len(A["equations"]), len(A["equations"]), rk, rk, 192 - rk))
    # worked example: the realized contact with the most shared faces
    best = max(A["realized"], key=lambda p: (len(shared_faces(p)), p))
    pairs, _ = site_pairs(best)
    ang, axis = rotation_data(best[0])
    tex.append(r"\subsection*{A worked contact}")
    tex.append(r"The realized contact with the most shared faces: $T=%s$, a rotation by $%s$%s, sharing %d unit faces "
               r"(root panel $\mapsto$ other panel: %s)." % (
                   _pm(pose_matrix(best)), L(ang),
                   "" if axis is None else r" about $%s$" % _pm(axis),
                   len(shared_faces(best)), ", ".join("$%d\\mapsto%d$" % (a, b) for a, b, _ in shared_faces(best))))
    eqs = " \\\\\n".join(r"\gamma_{%d,%d}+\gamma_{%d,%d} &= %d+(%d)=0" % (
        a // 8, a % 8, b // 8, b % 8, labels[a], labels[b]) for a, b in pairs)
    tex.append(r"\begin{align*}" + "\n" + eqs + "\n" + r"\end{align*}")
    head = (r"\begin{longtable}{r c c c r l}" + "\n" + r"\hline $n$ & $[G\,|\,t]$ & angle & axis & faces & panels \\ \hline" + "\n"
            r"\endhead")
    def table(title, poses):
        ordered = sorted(poses, key=lambda p: (rotation_data(p[0])[0], len(shared_faces(p)), p))
        return "\n".join([r"\subsection*{%s}" % title, r"\begin{center}\footnotesize", head] +
                         _contact_rows(ordered, labels) + [r"\hline", r"\end{longtable}", r"\end{center}"])
    tex.append(table("The %d realized contacts" % len(A["realized"]), A["realized"]))
    tex.append(table("The %d legal contacts that never occur" % len(A["unrealized"]), A["unrealized"]))
    return "\n".join(tex)


def write_latex(path, pdf=False, children=None, with_atlas=False):
    txt = latex_document(children, atlas_data=atlas(children) if with_atlas else None)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(txt)
    if pdf:
        outdir = os.path.dirname(os.path.abspath(path))
        subprocess.check_call(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                               "-output-directory", outdir, path], stdout=subprocess.DEVNULL)
    return path


# ------------------------------------------------------------------------------- driver
def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--symbolic", action="store_true", help="keep w, h symbolic in the mesh (slower)")
    ap.add_argument("--latex", metavar="FILE.tex")
    ap.add_argument("--pdf", action="store_true", help="compile the .tex with pdflatex")
    ap.add_argument("--obj", metavar="FILE.obj")
    ap.add_argument("--atlas", action="store_true", help="derive the contact atlas (2388 -> 44 -> 30); with --latex, print it too")
    ap.add_argument("--screen", action="store_true", help="re-derive the substitution from scratch (about 3 minutes)")
    ap.add_argument("--exag", type=float, default=1.0, help="height exaggeration for --obj")
    a = ap.parse_args(argv)
    if a.screen:
        chosen, _ = screen_tilings()
        print("  selected substitution equals the recorded CHILDREN:", chosen == CHILDREN)
    if a.verify or a.symbolic:
        ok, _, solid = verify(symbolic=a.symbolic)
        print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    if a.atlas:
        ok, _ = verify_atlas()
        print("ATLAS CHECKS PASSED" if ok else "ATLAS CHECKS FAILED")
    if a.latex:
        print("wrote", write_latex(a.latex, a.pdf, with_atlas=a.atlas))
    if a.obj:
        solid = Solid(label_table(CHILDREN), hscale=a.exag)
        open(a.obj, "w").write(solid.obj())
        print("wrote", a.obj)
    if not (a.verify or a.symbolic or a.latex or a.obj or a.screen or a.atlas):
        ap.print_help()


if __name__ == "__main__":
    main()
