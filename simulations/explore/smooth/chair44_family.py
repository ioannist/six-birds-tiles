#!/usr/bin/env python3
"""chair44_family.py - a continuum of Chair44-like decorated chairs, and a search over it.

IDEA.  Chair44 = a seven-cube chair whose 24 unit panels carry tiny pyramids.  The pyramid
heights are not arbitrary: whenever two chairs meet across a unit face (one of the 30 contacts
that occur inside the substitution hierarchy) the two panels must be exact complements
(bump <-> dent).  Following these identifications, the 24 panels glue into a quotient in
which a generic panel point has an orbit of 16 points with alternating signs.  The 192
pyramid sites form exactly 12 such orbits, which is why there are 12 height classes.

So ANY function on a fundamental domain (area 24/16 = 1.5 panels), extended along the
orbits with alternating sign, is a valid decoration at the level of face contacts - smooth
bumps, large undulations, anything.  `Identification.project` builds those fields.

WHAT IS CHECKED  (lattice face contacts only)
  * hierarchy patches (sigma_d) are gapless: every adjacent pair is an exact complement
  * the set of exactly-complementary contacts is the published 44-contact atlas
  * volume neutrality (the decorated tile has volume 7)
WHAT IS NOT CHECKED
  * placements that are not lattice-aligned (sliding / tilted contacts).  Those are where
    the published proof needs its conditions on the pyramid heights/slopes; a smooth or
    large-amplitude variant passing the lattice test is a *candidate* einstein tile, not a
    proven one.

CLI
  python3 chair44_family.py --check
  python3 chair44_family.py --merge-scan
  python3 chair44_family.py --search [--iters 60 --atoms 4 --seed 1 --json best.json]
  python3 chair44_family.py --obj out.obj [--field r44|smooth|projected] [--amp 0.06]
        (--amp = peak surface displacement in cube edges; every field is normalised to peak 1)
                            [--depth 1] [--rho 0.08] [--shape cosine] [--phi-json best.json]
"""
import argparse
import itertools
import json
import math
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction as Fr

import numpy as np

import chair44 as C

SHAPES = {
    "pyramid": lambda x, y: np.maximum(0.0, 1.0 - np.maximum(np.abs(x), np.abs(y))),
    "cone": lambda x, y: np.maximum(0.0, 1.0 - np.sqrt(x * x + y * y)),
    "cosine": lambda x, y: np.where(x * x + y * y < 1, 0.5 * (1 + np.cos(np.pi * np.sqrt(x * x + y * y))), 0.0),
    "smooth": lambda x, y: _cinf(x * x + y * y),
}


def _cinf(r2):
    with np.errstate(divide="ignore", over="ignore", invalid="ignore"):
        return np.where(r2 < 1, np.exp(1 - 1 / (1 - r2)), 0.0)


def tang(ax):
    return [k for k in range(3) if k != ax]


## ------------------------------------------------------------- identifications
class Identification:
    """Panel identifications forced by a set of face contacts (default: the 30 that occur
    in the hierarchy), their orbits, and the antisymmetric projection of height fields."""

    def __init__(self, contacts=None):
        self.deco = C.Decoration()
        self.panels = self.deco.panels
        self.root_index = {}
        for i, (ax, sd, c) in enumerate(self.panels):
            n = [0, 0, 0]
            n[ax] = sd
            self.root_index[(c, tuple(n))] = i
        self.contacts = tuple(contacts if contacts is not None
                              else C.observed_contacts(C.sigma_depth(3)))
        self.maps = defaultdict(list)                    # i -> [(j, M, b)]
        for pose in self.contacts:
            for i, j, M, b in self.shared(pose):
                self.maps[i].append((j, M, b))
        self.orbits, self.conflicts = self._orbits()
        self.classes = self._panel_classes()
        self.reps = [min(c) for c in self.classes]

    # -- charts: panel i, local (u,v) in [0,1]^2 <-> native 3D point on the panel plane
    def chart_to_native(self, i, u, v):
        ax, sd, c = self.panels[i]
        a, b = tang(ax)
        x = list(c)
        x[a] = c[a] + (u - Fr(1, 2))
        x[b] = c[b] + (v - Fr(1, 2))
        return tuple(x)

    def native_to_chart(self, i, x):
        ax, sd, c = self.panels[i]
        a, b = tang(ax)
        return (x[a] - c[a] + Fr(1, 2), x[b] - c[b] + Fr(1, 2))

    def shared(self, pose):
        """[(i, j, M, b)]: root panel i is glued to panel j of the chair in `pose`;
        chart map (u,v) -> M (u,v) + b, with M a signed 2x2 permutation, b integer."""
        f, t = pose
        finv = C.frame_inv(f)
        out = []
        for j, (ax, sd, c) in enumerate(self.panels):
            n = [0, 0, 0]
            n[ax] = sd
            n2 = C.frame_apply(f, n)
            cw = C.vadd(C.frame_apply(f, c), t)
            i = self.root_index.get((cw, tuple(-x for x in n2)))
            if i is None:
                continue

            def F(u, v, i=i, j=j):
                x = self.chart_to_native(i, u, v)
                return self.native_to_chart(j, C.frame_apply(finv, C.vsub(x, t)))
            b = F(Fr(0), Fr(0))
            e1, e2 = F(Fr(1), Fr(0)), F(Fr(0), Fr(1))
            M = ((e1[0] - b[0], e2[0] - b[0]), (e1[1] - b[1], e2[1] - b[1]))
            assert all(x.denominator == 1 for r in M for x in r) and all(x.denominator == 1 for x in b)
            out.append((i, j, tuple(tuple(int(x) for x in r) for r in M), tuple(int(x) for x in b)))
        return out

    def _orbits(self):
        orbits, conflicts = {}, 0
        I = ((1, 0), (0, 1))
        for i in range(len(self.panels)):
            seen = {(i, I, (0, 0)): 1}
            stack = [(i, I, (0, 0))]
            while stack:
                k, M, b = stack.pop()
                s = seen[(k, M, b)]
                for j, N, c in self.maps[k]:
                    M2 = tuple(tuple(sum(N[r][q] * M[q][s2] for q in range(2)) for s2 in range(2)) for r in range(2))
                    b2 = tuple(sum(N[r][q] * b[q] for q in range(2)) + c[r] for r in range(2))
                    key = (j, M2, b2)
                    if key in seen:
                        conflicts += seen[key] != -s
                    else:
                        seen[key] = -s
                        stack.append(key)
            orbits[i] = [(j, M, b, s) for (j, M, b), s in seen.items()]
        return orbits, conflicts

    def _panel_classes(self):
        """Panels linked by the identifications.  For Chair44: a class of 16 panels (an orbit
        meets each once -> one free function on a whole panel) and a class of 8 panels (an
        orbit meets each twice -> one free function on half a panel): 1 + 1/2 = 24/16."""
        seen, classes = set(), []
        for i in range(len(self.panels)):
            if i in seen:
                continue
            c = sorted({j for j, M, b, s in self.orbits[i]})
            seen.update(c)
            classes.append(c)
        return classes

    def project(self, phis):
        """Field object: H_i(p) = sum over the orbit of p of  sign * phi_j(image of p).

        `phis` is a list with one function (u,v)->array per panel CLASS (placed on the class
        representative; use independent functions - sharing one function between classes
        ties them together and creates spurious extra symmetry), or a list of 24 functions /
        None (one per panel) for full control."""
        if callable(phis):
            raise ValueError("pass one function per panel class (len %d) or per panel (24)" % len(self.classes))
        phis = list(phis)
        if len(phis) == len(self.classes):
            per = [None] * len(self.panels)
            for r, f in zip(self.reps, phis):
                per[r] = f
            phis = per
        assert len(phis) == len(self.panels)
        return ProjectedField(self, phis)


## ---------------------------------------------------------------------- fields
class ProjectedField:
    def __init__(self, ident, phi):
        self.ident = ident
        self.phi = list(phi)

    def eval(self, i, U, V):
        out = np.zeros_like(U, dtype=float)
        for j, M, b, s in self.ident.orbits[i]:
            u2 = M[0][0] * U + M[0][1] * V + b[0]
            v2 = M[1][0] * U + M[1][1] * V + b[1]
            f = self.phi[j]
            if f is not None:
                out += s * f(u2, v2)
        return out


class SiteField:
    """Pyramid-like bumps of the Chair44 height classes, with an adjustable footprint:
    shape in SHAPES, half-width rho (rho -> 0 recovers the tiny published pyramids)."""

    def __init__(self, ident, profile=None, rho=0.08, shape="pyramid"):
        self.ident, self.rho, self.shape = ident, rho, SHAPES[shape]
        prof = ident.deco.profile if profile is None else profile
        top = max(abs(float(x)) for x in prof)
        self.sites = defaultdict(list)
        for role, (pi, ctr) in enumerate(ident.deco.sites):
            u, v = ident.native_to_chart(pi, ctr)
            self.sites[pi].append((float(u), float(v), float(prof[role]) / top))

    def eval(self, i, U, V):
        out = np.zeros_like(U, dtype=float)
        for u0, v0, c in self.sites[i]:
            out += c * self.shape((U - u0) / self.rho, (V - v0) / self.rho)
        return out


class ScaledField:
    """`field` multiplied by a constant."""

    def __init__(self, field, scale):
        self.field, self.ident, self.scale = field, field.ident, scale

    def eval(self, i, U, V):
        return self.scale * self.field.eval(i, U, V)


def normalize(field, G=64):
    """Rescale so that max |H| = 1 (then `amp` in smooth_chair_mesh is the peak displacement
    in units of the cube edge)."""
    top = float(np.abs(grid_eval(field, G)).max())
    return ScaledField(field, 1.0 / top)


def window(u, v, m=0.1):
    """Smooth D4-symmetric window vanishing near the panel boundary."""
    def s(t):
        x = np.clip(t / m, 0, 1)
        return x * x * (3 - 2 * x)
    return s(u) * s(1 - u) * s(v) * s(1 - v)


def gaussian_phi(atoms, m=0.1):
    """atoms = [(u, v, sigma, amp), ...] -> windowed sum of Gaussians."""
    def phi(u, v):
        out = 0.0
        for (u0, v0, sg, a) in atoms:
            out = out + a * np.exp(-((u - u0) ** 2 + (v - v0) ** 2) / (2 * sg * sg))
        return window(u, v, m) * out
    return phi


def grid_eval(field, G):
    """Field sampled at cell centres: array (24, G, G), axis 1 = u, axis 2 = v."""
    u = (np.arange(G) + 0.5) / G
    U, V = np.meshgrid(u, u, indexing="ij")
    return np.array([field.eval(i, U, V) for i in range(24)])


## ----------------------------------------------------------------- contact tests
class ContactTable:
    """The 2388 raw face contacts with the panel pairs they glue, ready for fast tests."""

    def __init__(self, ident, raw=None):
        self.ident = ident
        self.raw = C.face_contacts() if raw is None else raw
        self.pairs = []                                   # (contact, i, j, transform id)
        self.tid_of = {}
        self.tmats = []
        for ci, pose in enumerate(self.raw):
            for i, j, M, b in ident.shared(pose):
                key = (M, b)
                if key not in self.tid_of:
                    self.tid_of[key] = len(self.tmats)
                    self.tmats.append(key)
                self.pairs.append((ci, i, j, self.tid_of[key]))
        P = np.array(self.pairs)
        self.cid, self.I, self.J, self.T = P[:, 0], P[:, 1], P[:, 2], P[:, 3]
        self._idx = {}

    def _index_arrays(self, G):
        if G not in self._idx:
            u = (np.arange(G) + 0.5) / G
            U, V = np.meshgrid(u, u, indexing="ij")
            A, B = [], []
            for M, b in self.tmats:
                u2 = M[0][0] * U + M[0][1] * V + b[0]
                v2 = M[1][0] * U + M[1][1] * V + b[1]
                A.append(np.rint(u2 * G - 0.5).astype(int))
                B.append(np.rint(v2 * G - 0.5).astype(int))
            self._idx[G] = (np.array(A), np.array(B))
        return self._idx[G]

    def relative_mismatch(self, H):
        """Per raw contact: sum_pairs mean|H_i + H_j(tau)| / sum_pairs (mean|H_i|+mean|H_j|).
        0 = exact complement on every glued panel, ~1 = unrelated."""
        G = H.shape[1]
        IA, IB = self._index_arrays(G)
        Hi = H[self.I]
        Hj = H[self.J[:, None, None], IA[self.T], IB[self.T]]
        num = np.abs(Hi + Hj).mean(axis=(1, 2))
        den = np.abs(Hi).mean(axis=(1, 2)) + np.abs(Hj).mean(axis=(1, 2))
        n = len(self.raw)
        N = np.bincount(self.cid, weights=num, minlength=n)
        D = np.bincount(self.cid, weights=den, minlength=n)
        return N / np.maximum(D, 1e-300)

    def atlas(self, H, tol=1e-9):
        r = self.relative_mismatch(H)
        legal = [self.raw[k] for k in np.flatnonzero(r < tol)]
        illegal = r[r >= tol]
        return legal, (float(illegal.min()) if len(illegal) else float("nan")), r


def slope(H):
    """max |grad H| per unit panel length (panel side = 1)."""
    G = H.shape[1]
    gu, gv = np.gradient(H, 1.0 / G, axis=(1, 2))
    return float(np.sqrt(gu ** 2 + gv ** 2).max())


## --------------------------------------------------------------------- meshing
def smooth_chair_mesh(field, amp=0.06, n=24):
    """Chair with every unit panel replaced by the height field `amp * field` (n x n quads)."""
    ident = field.ident
    verts, index, tris = [], {}, []

    def vid(p):
        k = tuple(np.round(p, 9))
        if k not in index:
            index[k] = len(verts)
            verts.append(p)
        return index[k]

    t = np.linspace(0.0, 1.0, n + 1)
    U, V = np.meshgrid(t, t, indexing="ij")
    for i, (ax, sd, c) in enumerate(ident.panels):
        a, b = tang(ax)
        H = amp * field.eval(i, U, V)
        P = np.zeros((n + 1, n + 1, 3))
        P[..., ax] = float(c[ax]) + sd * H
        P[..., a] = float(c[a]) + (U - 0.5)
        P[..., b] = float(c[b]) + (V - 0.5)
        ea, eb = np.zeros(3), np.zeros(3)
        ea[a], eb[b] = 1, 1
        flip = np.cross(ea, eb)[ax] * sd < 0
        ids = np.array([[vid(P[p, q]) for q in range(n + 1)] for p in range(n + 1)])
        for p in range(n):
            for q in range(n):
                a0, a1, a2, a3 = ids[p, q], ids[p + 1, q], ids[p + 1, q + 1], ids[p, q + 1]
                for tri in ((a0, a1, a2), (a0, a2, a3)):
                    tris.append(tri[::-1] if flip else tri)
    return np.array(verts), np.array(tris, int)


def mesh_volume(V, T):
    a, b, c = V[T[:, 0]], V[T[:, 1]], V[T[:, 2]]
    return float(np.einsum("ij,ij->i", a, np.cross(b, c)).sum() / 6)


def is_watertight(T):
    e = Counter()
    for tri in T:
        for k in range(3):
            e[tuple(sorted((tri[k], tri[(k + 1) % 3])))] += 1
    return all(v == 2 for v in e.values())


## ------------------------------------------------------------------------ checks
def check(verbose=True, G=24):
    log = print if verbose else (lambda *a, **k: None)
    t0 = time.time()
    ident = Identification()
    sizes = Counter(len(o) for o in ident.orbits.values())
    log("contacts used: %d (hierarchy-realised)   panel orbits: sizes %s   sign conflicts: %d" % (
        len(ident.contacts), dict(sizes), ident.conflicts))
    assert ident.conflicts == 0 and set(sizes) == {16}

    # 1. antisymmetry of projected fields across every identification
    rng = np.random.default_rng(0)
    log("panel classes: sizes %s (free-function areas 1 and 1/2)" % [len(c) for c in ident.classes])
    assert sorted(len(c) for c in ident.classes) == [8, 16]
    F = ident.project([gaussian_phi(random_atoms(rng, 5)) for _ in ident.classes])
    worst = 0.0
    P = rng.uniform(0.05, 0.95, (2, 50))
    for i, lst in ident.maps.items():
        for j, M, b in lst:
            u2 = M[0][0] * P[0] + M[0][1] * P[1] + b[0]
            v2 = M[1][0] * P[0] + M[1][1] * P[1] + b[1]
            worst = max(worst, float(np.abs(F.eval(i, P[0], P[1]) + F.eval(j, u2, v2)).max()))
    log("projected field is antisymmetric across all identifications: max |H_i + H_j(tau)| = %.2e" % worst)
    assert worst < 1e-12

    # 2. the projection reproduces the published pyramid decoration
    reps, seen = {}, {}
    for role, (pi, ctr) in enumerate(ident.deco.sites):
        u, v = ident.native_to_chart(pi, ctr)
        for j, M, b, s in ident.orbits[pi]:
            u2 = M[0][0] * u + M[0][1] * v + b[0]
            v2 = M[1][0] * u + M[1][1] * v + b[1]
            seen.setdefault((j, u2, v2), role)
    cls = {}
    for role, (pi, ctr) in enumerate(ident.deco.sites):
        u, v = ident.native_to_chart(pi, ctr)
        cls[role] = frozenset((j, M[0][0] * u + M[0][1] * v + b[0], M[1][0] * u + M[1][1] * v + b[1])
                              for j, M, b, s in ident.orbits[pi])
    classes = {}
    for role, k in cls.items():
        classes.setdefault(k, []).append(role)
    log("site orbits: %d classes of sizes %s" % (len(classes), sorted(Counter(len(v) for v in classes.values()).items())))
    assert len(classes) == 12
    rho, shape = 0.08, "cosine"
    per_panel = [None] * 24
    atoms = defaultdict(list)
    for roles in classes.values():
        r0 = min(roles)
        pi, ctr = ident.deco.sites[r0]
        u0, v0 = (float(x) for x in ident.native_to_chart(pi, ctr))
        atoms[pi].append((u0, v0, float(ident.deco.profile[r0])))
    for pi, lst in atoms.items():
        per_panel[pi] = (lambda lst: (lambda u, v: sum(c * SHAPES[shape]((u - u0) / rho, (v - v0) / rho) for u0, v0, c in lst)))(lst)
    Hproj = grid_eval(ident.project(per_panel), G)
    prof = ident.deco.profile
    Hsite = grid_eval(SiteField(ident, prof, rho, shape), G) * max(abs(float(x)) for x in prof)
    err = float(np.abs(Hproj - Hsite).max())
    log("projection of 12 representative bumps == published pyramid profile: max diff %.2e" % err)
    assert err < 1e-12

    # 3. atlas (exactly complementary contacts) for several family members
    tab = ContactTable(ident)
    log("raw face contacts: %d, glued panel pairs: %d  (table %.1fs)" % (len(tab.raw), len(tab.pairs), time.time() - t0))
    members = {
        "R44 pyramids rho=0.08": grid_eval(SiteField(ident, None, 0.08, "pyramid"), G),
        "R44 smooth bumps rho=0.10": grid_eval(SiteField(ident, None, 0.10, "smooth"), G),
        "R44 cosine bumps rho=0.12": grid_eval(SiteField(ident, None, 0.12, "cosine"), G),
        "random projected Gaussians": grid_eval(F, G),
    }
    rng = np.random.default_rng(5)
    for k in range(3):
        members["random projected #%d" % k] = grid_eval(
            ident.project([gaussian_phi(random_atoms(rng, 4)) for _ in ident.classes]), G)
    for name, H in members.items():
        legal, margin, r = tab.atlas(H)
        same = set(legal) == set(C.ATLAS44)
        log("  %-28s legal contacts: %3d  == published 44: %-5s  weakest wrong contact: %.3f  slope: %.2f" % (
            name, len(legal), same, margin, slope(H / np.abs(H).max())))
        assert same, name
    # 4. realised patch is gapless for a smooth member
    H = members["random projected Gaussians"]
    poses = C.sigma_depth(3)
    cons = C.observed_contacts(poses)
    legal, _, _ = tab.atlas(H)
    assert cons <= set(legal)
    log("all %d contacts realised in sigma_3 are exact complements for the smooth member" % len(cons))
    # 5. mesh: watertight, volume 7
    V, T = smooth_chair_mesh(F, amp=0.06, n=12)
    vol = mesh_volume(V, T)
    log("smooth chair mesh: %d vertices, %d triangles, watertight=%s, volume=%.9f (expect 7)" % (
        len(V), len(T), is_watertight(T), vol))
    assert is_watertight(T) and abs(vol - 7) < 1e-9
    log("OK (%.1fs)" % (time.time() - t0))
    return True


## ------------------------------------------------------------ height-class structure
def placed_roles(deco, pose):
    """{(axis, doubled face centre): [(world site centre, role)]} for a chair in `pose`."""
    out = defaultdict(list)
    f, t = pose
    for pi, (ax, sd, c) in enumerate(deco.panels):
        n = [0, 0, 0]
        n[ax] = sd
        n2 = C.frame_apply(f, n)
        ax2 = next(i for i in range(3) if n2[i])
        key = (ax2, tuple(int(2 * v) for v in C.vadd(C.frame_apply(f, c), t)))
        for role, ctr in deco.by_panel[pi]:
            out[key].append((C.vadd(C.frame_apply(f, ctr), t), role))
    return out


def class_requirements(deco=None, raw=None):
    """For every raw face contact: (structure_ok, required) where structure_ok means every glued
    face has all its pyramid sites matched with opposite signs, and `required` is the set of
    class pairs (a, b) whose magnitudes must be EQUAL for the contact to be an exact
    complement.  A contact is legal for a magnitude labelling m iff structure_ok and
    m[a] == m[b] for all required pairs.  (Class = |profile entry|, 1..12.)"""
    deco = deco or C.Decoration()
    raw = C.face_contacts() if raw is None else raw
    prof = deco.profile
    cls = [abs(int(x)) for x in prof]
    A = placed_roles(deco, C.ROOT_POSE)
    fa = C.exposed_faces(C.ROOT_POSE)
    out = []
    for pose in raw:
        B = placed_roles(deco, pose)
        fb = C.exposed_faces(pose)
        ok, req = True, set()
        for key, sd in fb.items():
            if key not in fa or fa[key] != -sd:
                continue
            pa, pb = dict(A[key]), dict(B[key])
            if set(pa) != set(pb):
                ok = False
                break
            for c, ra in pa.items():
                rb = pb[c]
                if (prof[ra] > 0) == (prof[rb] > 0):
                    ok = False
                    break
                if cls[ra] != cls[rb]:
                    req.add((min(cls[ra], cls[rb]), max(cls[ra], cls[rb])))
            if not ok:
                break
        out.append((ok, frozenset(req)))
    return raw, out


def set_partitions(n, k):
    """Restricted-growth strings of length n with exactly k blocks (as numpy rows)."""
    out = []

    def rec(prefix, mx):
        if len(prefix) == n:
            if mx == k:
                out.append(prefix[:])
            return
        if mx + (n - len(prefix)) < k:
            return
        for v in range(min(mx + 1, k)):
            prefix.append(v)
            rec(prefix, max(mx, v + 1))
            prefix.pop()
    rec([], 0)
    return np.array(out, dtype=np.int8)


def merge_scan(verbose=True, max_k=4):
    """Exhaustive scan of height-class coincidences.  Which labellings of the 12 classes by k
    distinct magnitudes keep the lattice atlas at exactly 44 contacts?"""
    raw, reqs = class_requirements()
    ok = [r for r in reqs if r[0]]
    base = [r for r in ok if not r[1]]
    extra = [r for r in ok if r[1]]
    if verbose:
        print("raw contacts %d; structurally compatible (all faces matched, signs opposite) %d;"
              " legal with 12 distinct magnitudes %d; the other %d need class equalities" % (
                  len(raw), len(ok), len(base), len(extra)))
        print("all magnitudes equal -> %d legal contacts" % len(ok))
    pairs = sorted({p for _, r in extra for p in r})
    pid = {p: i for i, p in enumerate(pairs)}
    PA = np.array([a - 1 for a, b in pairs])
    PB = np.array([b - 1 for a, b in pairs])
    order = [[pid[p] for p in sorted(r)] for _, r in extra]
    flat = np.array([x for lst in order for x in lst])
    starts = np.cumsum([0] + [len(l) for l in order[:-1]])
    results = {}
    for k in range(1, max_k + 1):
        P = set_partitions(12, k)
        good = 0
        examples = []
        for lo in range(0, len(P), 4000):
            L = P[lo:lo + 4000]
            eq = (L[:, PA[flat]] == L[:, PB[flat]])                  # (chunk, total pairs)
            all_eq = np.logical_and.reduceat(eq, starts, axis=1)       # contact legal if all equal
            n_extra = all_eq.sum(axis=1)
            sel = np.flatnonzero(n_extra == 0)
            good += len(sel)
            if len(examples) < 3:
                examples += [L[i].tolist() for i in sel[:3 - len(examples)]]
        results[k] = (len(P), good, examples)
        if verbose:
            print("k=%d magnitudes: %7d labellings of the 12 classes, %7d keep exactly 44 contacts   e.g. %s" % (
                k, len(P), good, examples[:1]))
    return results


## ----------------------------------------------------------------------- search
def random_atoms(rng, k):
    return [(rng.uniform(.15, .85), rng.uniform(.15, .85), rng.uniform(.05, .18), rng.normal()) for _ in range(k)]


def evaluate(ident, tab, atoms, G=16, slope_scale=6.0):
    """atoms = one atom list per panel class."""
    H = grid_eval(ident.project([gaussian_phi(a) for a in atoms]), G)
    top = np.abs(H).max()
    if top < 1e-9:
        return None
    H = H / top
    legal, margin, _ = tab.atlas(H)
    ok = len(legal) == 44 and set(legal) == set(C.ATLAS44)
    sl = slope(H)
    score = (margin / (1 + sl / slope_scale)) if ok else -1.0
    return {"score": score, "margin": margin, "slope": sl, "legal": len(legal), "ok": ok}


def search(iters=60, atoms=4, seed=1, pop=24, keep=6, G=16, verbose=True):
    """(mu+lambda) evolution strategy over windowed-Gaussian fields: `atoms` Gaussians
    (u, v, sigma, amp) for each of the two free functions (panel classes).
    Score = weakest-wrong-contact mismatch / (1 + slope/6): rejects wrong contacts firmly yet
    stays smooth.  Fields must reproduce exactly the 44-contact atlas to count."""
    rng = np.random.default_rng(seed)
    ident = Identification()
    tab = ContactTable(ident)

    def mutate(a, s):
        return [[(float(np.clip(u + rng.normal(0, s), .1, .9)), float(np.clip(v + rng.normal(0, s), .1, .9)),
                  float(np.clip(sg * math.exp(rng.normal(0, s)), .03, .25)), am + rng.normal(0, s * 2))
                 for (u, v, sg, am) in cls] for cls in a]
    popl = []
    while len(popl) < pop:
        a = [random_atoms(rng, atoms) for _ in ident.classes]
        r = evaluate(ident, tab, a, G)
        if r:
            popl.append((r["score"], a, r))
    best_hist = []
    for it in range(iters):
        popl.sort(key=lambda x: -x[0])
        parents = popl[:keep]
        s = 0.15 * (1 - it / iters) + 0.02
        kids = []
        for _ in range(pop - keep):
            p = parents[rng.integers(keep)][1]
            a = mutate(p, s)
            r = evaluate(ident, tab, a, G)
            if r:
                kids.append((r["score"], a, r))
        popl = parents + kids
        best_hist.append(popl[0][0])
        if verbose and (it % 10 == 0 or it == iters - 1):
            b = max(popl, key=lambda x: x[0])
            print("iter %3d  best score %.4f  margin %.3f  slope %.2f  legal %d" % (
                it, b[0], b[2]["margin"], b[2]["slope"], b[2]["legal"]))
    popl.sort(key=lambda x: -x[0])
    return popl[0], best_hist


## --------------------------------------------------------------------------- main
def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--merge-scan", action="store_true")
    ap.add_argument("--search", action="store_true")
    ap.add_argument("--iters", type=int, default=60)
    ap.add_argument("--atoms", type=int, default=4)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--json")
    ap.add_argument("--obj")
    ap.add_argument("--field", default="projected", choices=["r44", "smooth", "projected"])
    ap.add_argument("--amp", type=float, default=0.06)
    ap.add_argument("--depth", type=int, default=0)
    ap.add_argument("--rho", type=float, default=0.08)
    ap.add_argument("--shape", default="cosine", choices=list(SHAPES))
    ap.add_argument("--phi-json")
    ap.add_argument("--mags", help="12 comma-separated class magnitudes for --field r44/smooth, "
                                   "e.g. 1,1,1,1,1,1,1,2,1,1,1,2 (see --merge-scan)")
    a = ap.parse_args(argv)
    if a.check:
        check()
    if a.merge_scan:
        merge_scan()
    if a.search:
        (score, atoms, r), hist = search(a.iters, a.atoms, a.seed)
        print("best:", json.dumps({"score": score, "metrics": r, "atoms": atoms}, default=float))
        if a.json:
            with open(a.json, "w") as fh:
                json.dump({"score": score, "metrics": r, "atoms": atoms}, fh, default=float)
            print("wrote", a.json)
    if a.obj:
        ident = Identification()
        prof = None
        if a.mags:
            mags = [Fr(x) for x in a.mags.split(",")]
            assert len(mags) == 12, "need 12 magnitudes"
            prof = [mags[abs(int(x)) - 1] * (1 if x > 0 else -1) for x in ident.deco.profile]
        if a.field == "r44":
            field = SiteField(ident, prof, 0.01, "pyramid")
        elif a.field == "smooth":
            field = SiteField(ident, prof, a.rho, a.shape)
        else:
            if a.phi_json:
                atoms = json.load(open(a.phi_json))["atoms"]
            else:
                atoms = [[(.3, .35, .12, 1.0), (.68, .6, .1, -.8), (.45, .8, .09, .6), (.8, .25, .1, .5)],
                         [(.35, .3, .12, 1.0), (.7, .7, .1, -.7)]]
            field = normalize(ident.project([gaussian_phi(x) for x in atoms]))
        V, T = smooth_chair_mesh(field, a.amp, n=32)
        W, TT, tid = C.assemble(C.sigma_depth(a.depth), V, T)
        C.write_obj(a.obj, W, TT, tid)
        print("wrote", a.obj, len(W), "vertices", len(TT), "triangles")
    if not (a.check or a.merge_scan or a.search or a.obj):
        ap.print_help()


if __name__ == "__main__":
    main()
