#!/usr/bin/env python3
"""chair44.py - the Chair44 (R44) 3D einstein tile, in the style of spectre.py.

Chair44 is a seven-cube "chair" (2x2x2 block minus one corner) whose 24 exposed
unit panels each carry 8 tiny square pyramids (bumps/dents of height j/10000).
Eight rotated copies form a doubled chair (the supertile), so the tiling is
hierarchical on length scale 2**n and has no translation period.

Port of the Spectre fork brentharts/spectre (chair44.py).  Tier T2, exploratory.
Credit: shape, substitution and 44-contact atlas are from Ioannis Tsiokos,
https://github.com/ioannist/six-birds-tiles  (CC BY 4.0), arXiv:2609.19214 and
arXiv:2609.23783.  This module re-implements the geometry independently and
checks itself against the repository certificate (certificates/candidate_certificate.json).

Conventions
  frame  = (perm, signs)      (g x)_i = signs[i] * x[perm[i]]       (48 frames)
  pose   = (frame, t)         point map  x -> g x + t               (t integer)
  child poses refine as      (G,t) -> (G H, 2 t + G u)
Everything combinatorial is exact (ints / Fractions); floats only for meshes.

CLI
  python3 chair44.py --verify               # reproduce 2388 -> 44 and patch checks
  python3 chair44.py --obj out.obj --depth 2 [--decorated] [--exag 500]
"""
import argparse
import csv
import itertools
import json
import os
import sys
from collections import defaultdict
from fractions import Fraction as Fr

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
DATA = os.path.join(REPO, "solid")          # r44_solid.json, native_panels.csv
CERT = os.path.join(REPO, "certificates", "candidate_certificate.json")

## ---------------------------------------------------------------- frames/poses
CHAIR_CELLS = frozenset(c for c in itertools.product((0, 1), repeat=3) if c != (1, 1, 1))
IDENTITY_FRAME = ((0, 1, 2), (1, 1, 1))
ROOT_POSE = (IDENTITY_FRAME, (0, 0, 0))


def all_frames():
    """The 48 signed permutation frames of the cube group."""
    return [(p, s) for p in itertools.permutations(range(3))
            for s in itertools.product((1, -1), repeat=3)]


def frame_apply(f, v):
    p, s = f
    return tuple(s[i] * v[p[i]] for i in range(3))


def frame_mul(a, b):
    """frame of a(b(x))."""
    p, s = a
    q, t = b
    return (tuple(q[p[i]] for i in range(3)), tuple(s[i] * t[p[i]] for i in range(3)))


def frame_inv(f):
    p, s = f
    ip = tuple(p.index(i) for i in range(3))
    return ip, tuple(s[ip[i]] for i in range(3))


def frame_det(f):
    p, s = f
    inv = sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))
    return (-1 if inv % 2 else 1) * s[0] * s[1] * s[2]


def vadd(a, b):
    return tuple(x + y for x, y in zip(a, b))


def vsub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def vscale(k, a):
    return tuple(k * x for x in a)


def pose_apply(pose, v):
    return vadd(frame_apply(pose[0], v), pose[1])


def pose_mul(a, b):
    return frame_mul(a[0], b[0]), vadd(a[1], frame_apply(a[0], b[1]))


def relative_pose(root, other):
    """`other` expressed in the native coordinates of `root`."""
    inv = frame_inv(root[0])
    return frame_mul(inv, other[0]), frame_apply(inv, vsub(other[1], root[1]))


def parse_pose(j):
    (p, s), t = j
    return (tuple(p), tuple(s)), tuple(t)


def pose_cells(pose):
    """Unit cells (lower corners) of the chair in this pose."""
    f, t = pose
    out = []
    for c in CHAIR_CELLS:
        x = frame_apply(f, c)
        out.append(tuple(x[i] + t[i] - (1 if f[1][i] < 0 else 0) for i in range(3)))
    return frozenset(out)


def exposed_faces(pose):
    """{(axis, doubled face centre): outward sign} for the unit faces on the surface."""
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


## ------------------------------------------------------------------ substitution
def load_atlas():
    with open(CERT) as fh:
        a = json.load(fh)
    children = tuple(parse_pose(c) for c in a["children"])
    legal = frozenset(parse_pose(c) for c in a["legal_contacts"])
    return children, legal, len(a["raw_contacts"])


CHILDREN, ATLAS44, RAW_COUNT = load_atlas()


def refine_pose(pose, children=CHILDREN):
    (G, t) = pose
    return tuple((frame_mul(G, H), vadd(vscale(2, t), frame_apply(G, u))) for H, u in children)


def sigma_depth(depth, children=CHILDREN):
    """Poses of the 8**depth chairs of the depth-th supertile (chair = depth 0)."""
    poses = (ROOT_POSE,)
    for _ in range(depth):
        poses = tuple(c for p in poses for c in refine_pose(p, children))
    return poses


def tile_digits(depth):
    """Base-8 hierarchy address of each tile in sigma_depth(depth) (first digit = top level)."""
    return list(itertools.product(range(8), repeat=depth))


def nested_patch(level):
    """Proof-style nested patch A_n: sigma_{2n} shifted by -c_n (1,1,1), c_n = 2(4^n-1)/3."""
    sh = 2 * (4 ** level - 1) // 3
    return tuple((f, vsub(t, (sh, sh, sh))) for f, t in sigma_depth(2 * level))


## ---------------------------------------------------------------- decorations
class Decoration:
    """24 panels x 8 pyramid sites; `profile[role]` is the signed height in 1/10000 units
    (+ bump, - dent, along the outward normal).  Sites are fixed by the solid; heights are
    the free data, which is what the family explorer varies."""

    def __init__(self, path=None):
        path = path or os.path.join(DATA, "r44_solid.json")
        with open(path) as fh:
            d = json.load(fh)
        self.height_unit = Fr(d["height_unit"])
        self.halfwidth = Fr(d["base_halfwidth"])
        self.panels = []
        with open(os.path.join(DATA, "native_panels.csv")) as fh:
            for r in csv.DictReader(fh):
                c = tuple(Fr(r[k]) for k in ("center_x", "center_y", "center_z"))
                self.panels.append((int(r["normal_axis"]), int(r["outward_sign"]), c))
        self.sites = [None] * 192          # role -> (panel, centre)
        self.profile = [0] * 192
        for p in d["patches"]:
            base = [tuple(Fr(x) for x in b) for b in p["base"]]
            ctr = tuple(sum(b[i] for b in base) / 4 for i in range(3))
            self.sites[int(p["role"])] = (int(p["face"]), ctr)
            self.profile[int(p["role"])] = Fr(p["coefficient"])
        assert all(s is not None for s in self.sites)
        self.by_panel = defaultdict(list)
        for role, (pi, ctr) in enumerate(self.sites):
            self.by_panel[pi].append((role, ctr))
        self._vertices = [tuple(Fr(x) for x in v) for v in d["vertices"]]
        self._triangles = d["triangles"]
        self._apex = {}
        for p in d["patches"]:
            self._apex[int(p["role"])] = tuple(Fr(x) for x in p["apex"])

    def placed(self, pose, profile=None):
        """{(axis, doubled centre): [(world centre, coef), ...]} for the pose."""
        profile = self.profile if profile is None else profile
        out = defaultdict(list)
        f, t = pose
        for pi, (ax, sd, c) in enumerate(self.panels):
            n = [0, 0, 0]
            n[ax] = sd
            n2 = frame_apply(f, n)
            ax2 = next(i for i in range(3) if n2[i])
            c2 = vadd(frame_apply(f, c), t)
            key = (ax2, tuple(int(2 * v) for v in c2))
            for role, ctr in self.by_panel[pi]:
                out[key].append((vadd(frame_apply(f, ctr), t), profile[role]))
        return out


## -------------------------------------------------------------------- contacts
def face_contacts():
    """All relative poses at which a second chair touches the root across unit faces
    without overlapping (rotations and mirror images allowed).  Paper: 2388."""
    root_cells = pose_cells(ROOT_POSE)
    root_faces = exposed_faces(ROOT_POSE)
    out = []
    for f in all_frames():
        for t in itertools.product(range(-4, 5), repeat=3):
            pose = (f, t)
            cells = pose_cells(pose)
            if cells & root_cells:
                continue
            fa = exposed_faces(pose)
            if any(k in root_faces and root_faces[k] == -s for k, s in fa.items()):
                out.append(pose)
    return out


def contact_is_legal(pose, deco, profile=None, exact=True, root_placed=None):
    """Legality of decorated chairs in contact (lattice contacts only).

    On every shared unit face, a root pyramid at the same site as a pyramid of the other
    tile needs cA + cB == 0 (exact complement: a tiling has no voids), or <= 0 when
    exact=False (no overlap, voids allowed).  A pyramid facing a flat region needs c <= 0
    (a dent), and with exact=True any unmatched pyramid is rejected (a dent facing flat
    leaves a void).  Sites are 1/8 apart and pyramids ~1/50 wide, so pyramids either
    coincide or are disjoint."""
    A = root_placed if root_placed is not None else deco.placed(ROOT_POSE, profile)
    B = deco.placed(pose, profile)
    fa = exposed_faces(ROOT_POSE)
    fb = exposed_faces(pose)
    for key, sd in fb.items():
        if key not in fa or fa[key] != -sd:
            continue
        pa = {c: v for c, v in A[key]}
        pb = {c: v for c, v in B[key]}
        for c, v in pa.items():
            if c in pb:
                s = v + pb[c]
                if (s != 0) if exact else (s > 0):
                    return False
            elif (v != 0) if exact else (v > 0):
                return False
        for c, v in pb.items():
            if c not in pa and ((v != 0) if exact else (v > 0)):
                return False
    return True


def legal_contacts(deco, profile=None, exact=True, raw=None):
    raw = face_contacts() if raw is None else raw
    A = deco.placed(ROOT_POSE, profile)
    return [p for p in raw if contact_is_legal(p, deco, profile, exact, A)]


## ----------------------------------------------------------------------- meshes
def pose_matrix(pose):
    (p, s), t = pose
    M = np.zeros((3, 3))
    for i in range(3):
        M[i, p[i]] = s[i]
    return M, np.array(t, float)


def base_chair_mesh():
    """Undecorated chair: 24 unit squares -> (V, tris), outward-facing triangles."""
    verts, index, tris = [], {}, []

    def vid(v):
        if v not in index:
            index[v] = len(verts)
            verts.append(v)
        return index[v]

    for (ax, k), sd in sorted(exposed_faces(ROOT_POSE).items()):
        c = [x / 2 for x in k]
        u, w = [i for i in range(3) if i != ax]
        quad = []
        for du, dw in ((-.5, -.5), (.5, -.5), (.5, .5), (-.5, .5)):
            p = list(c)
            p[u] += du
            p[w] += dw
            quad.append(vid(tuple(p)))
        a, b, cc, d = quad
        n = np.cross(np.subtract(verts[b], verts[a]), np.subtract(verts[cc], verts[a]))
        if n[ax] * sd < 0:
            a, b, cc, d = a, d, cc, b
        tris += [[a, b, cc], [a, cc, d]]
    return np.array(verts, float), np.array(tris, int)


def decorated_mesh(deco, exag=1.0, profile=None):
    """Decorated solid from the 2138-vertex mesh; `exag` scales feature heights (1 = true).
    Pass `profile` to re-height the pyramids."""
    V = np.array([[float(x) for x in v] for v in deco._vertices])
    T = np.array(deco._triangles, int)
    if exag != 1.0 or profile is not None:
        prof = deco.profile if profile is None else profile
        idx = {v: i for i, v in enumerate(deco._vertices)}
        for role, (pi, ctr) in enumerate(deco.sites):
            ax, sd, _ = deco.panels[pi]
            apex = list(ctr)
            apex[ax] += sd * Fr(prof[role]) * deco.height_unit * Fr(exag).limit_denominator(10 ** 6)
            V[idx[deco._apex[role]]] = [float(x) for x in apex]
    return V, T


def assemble(poses, V, T, labels=None):
    """Place copies of the mesh at the poses -> (V, T, tile_id per triangle)."""
    allV, allT, tid, off = [], [], [], 0
    for i, pose in enumerate(poses):
        M, t = pose_matrix(pose)
        W = V @ M.T + t
        TT = T[:, ::-1] if frame_det(pose[0]) < 0 else T
        allV.append(W)
        allT.append(TT + off)
        tid += [i] * len(T)
        off += len(V)
    return np.vstack(allV), np.vstack(allT), np.array(tid)


def write_obj(path, V, T, tile_id=None):
    with open(path, "w") as fh:
        for v in V:
            fh.write("v %.9g %.9g %.9g\n" % tuple(v))
        cur = None
        for i, f in enumerate(T):
            if tile_id is not None and tile_id[i] != cur:
                cur = tile_id[i]
                fh.write("g chair_%d\n" % cur)
            fh.write("f %d %d %d\n" % (f[0] + 1, f[1] + 1, f[2] + 1))


## ----------------------------------------------------------------- verification
def check_patch(poses, legal=ATLAS44):
    """Cells disjoint; every face-adjacent pair is one of the legal contacts."""
    owners = {}
    for i, p in enumerate(poses):
        for c in pose_cells(p):
            assert c not in owners, "cell shared by tiles %d and %d" % (owners[c], i)
            owners[c] = i
    fo = defaultdict(list)
    for i, p in enumerate(poses):
        for k, s in exposed_faces(p).items():
            fo[k].append((i, s))
    pairs = set()
    for k, rec in fo.items():
        assert len(rec) <= 2
        if len(rec) == 2:
            (a, sa), (b, sb) = rec
            assert sa == -sb
            pairs.add((min(a, b), max(a, b)))
    for a, b in pairs:
        assert relative_pose(poses[a], poses[b]) in legal, "illegal contact %d,%d" % (a, b)
    return {"tiles": len(poses), "cells": len(owners), "adjacent_pairs": len(pairs)}


def patch_surface_stats(poses):
    """Unit-face bookkeeping of a patch: total / shared / surface faces and adjacent pairs."""
    fo = defaultdict(list)
    for i, p in enumerate(poses):
        for k, s in exposed_faces(p).items():
            fo[k].append(i)
    shared = sum(1 for v in fo.values() if len(v) == 2)
    surface = sum(1 for v in fo.values() if len(v) == 1)
    return {"tiles": len(poses), "total_faces": sum(len(v) for v in fo.values()),
            "shared_faces": shared, "surface_faces": surface}


def observed_contacts(poses):
    """Set of ordered relative poses of face-adjacent tile pairs actually present in a patch."""
    fo = defaultdict(list)
    for i, p in enumerate(poses):
        for k, s in exposed_faces(p).items():
            fo[k].append(i)
    pairs = {tuple(sorted(v)) for v in fo.values() if len(v) == 2}
    out = set()
    for a, b in pairs:
        out.add(relative_pose(poses[a], poses[b]))
        out.add(relative_pose(poses[b], poses[a]))
    return out


def verify(verbose=True):
    log = print if verbose else (lambda *a, **k: None)
    raw = face_contacts()
    log("undecorated face contacts:", len(raw), "(paper: 2388)")
    assert len(raw) == RAW_COUNT == 2388
    deco = Decoration()
    leg_gap = legal_contacts(deco, exact=False, raw=raw)
    leg = legal_contacts(deco, exact=True, raw=raw)
    log("no-overlap contacts (voids allowed):", len(leg_gap),
        "| exact-complement contacts:", len(leg), "(paper: 44)")
    assert set(leg) == set(ATLAS44) and len(leg) == 44, "does not match the published atlas"
    log("independent 44 == published atlas: OK")
    for d in (1, 2, 3):
        r = check_patch(sigma_depth(d))
        log("sigma_%d" % d, r)
        assert r["tiles"] == 8 ** d and r["cells"] == 7 * 8 ** d
    target = {tuple(2 * x[i] + b[i] for i in range(3)) for x in CHAIR_CELLS
              for b in itertools.product((0, 1), repeat=3)}
    cells = set().union(*[pose_cells(p) for p in sigma_depth(1)])
    assert cells == target, "depth-1 supertile is not the doubled chair"
    log("depth-1 supertile == chair scaled by 2: OK")
    for lv in (1, 2):
        a, b = set(nested_patch(lv)), set(nested_patch(lv + 1))
        assert a <= b
    log("nested patches A_1 < A_2 < A_3: OK")
    # every placed face of the decorated solid must have matching key sets
    for p in sigma_depth(1):
        keys = set(deco.placed(p))
        assert keys == set(exposed_faces(p)), "panel keys disagree with cell faces"
    log("decoration panels agree with cell faces: OK")
    return True


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--obj")
    ap.add_argument("--depth", type=int, default=1)
    ap.add_argument("--decorated", action="store_true")
    ap.add_argument("--exag", type=float, default=1.0)
    a = ap.parse_args(argv)
    if a.verify:
        verify()
    if a.obj:
        if a.decorated:
            V, T = decorated_mesh(Decoration(), a.exag)
        else:
            V, T = base_chair_mesh()
        W, TT, tid = assemble(sigma_depth(a.depth), V, T)
        write_obj(a.obj, W, TT, tid)
        print("wrote", a.obj, len(W), "vertices", len(TT), "triangles")
    if not (a.verify or a.obj):
        ap.print_help()


if __name__ == "__main__":
    main()
