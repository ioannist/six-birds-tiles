#!/usr/bin/env python3
"""Brute-force periodicity search for the R44 solid (no theorems).

Two SAT searches over grid-registered copies of the solid in solid/r44_solid.json:

  torus   For every full-rank sublattice L of Z^3 with index <= --index, ask a SAT solver
          whether the torus R^3/L can be tiled by copies of Q.  A satisfying assignment lifts
          to a tiling of R^3 with period lattice L.  UNSAT for every L up to the bound means:
          no tiling by registered copies has a full-rank period lattice of index <= --index.
  corona  Heesch-style growth: for k = 1..--coronas, ask whether the seed copy can be
          surrounded so that every cell within Chebyshev distance k of it is covered exactly
          once by pairwise compatible copies.  Shows that patches keep growing.

What "copy" and "compatible" mean here (this is the whole model; no proof is cited):
  * A copy is the solid moved by one of the 48 signed coordinate permutations (24 if
    --proper-only) and an integer translation.  Copies are therefore aligned with the unit
    grid; the seven unit cubes of the chair carrier land on grid cells.
  * Two copies are compatible iff their carrier cells are disjoint and, on every unit panel
    they share (a cell of one facing a cell of the other across a unit square), the eight
    pyramidal features on the two sides are exact opposites: same marker points, heights
    of opposite sign (a bump of height h meets a dent of depth h).  Heights and marker points
    are read from the solid file and transformed exactly (fractions), never rounded.
  * A tiling of the torus / of the region is an assignment of copies covering every required
    cell exactly once with all pairs compatible.
Restricting to grid-registered copies is an assumption of this search.  The bound is
evidence, never a proof: an UNSAT sweep up to N says nothing about index > N or about
tilings with only one or two independent periods.

Requires python-sat (pip install python-sat).  Stdlib otherwise.

    python3 simulations/periodicity_search.py --index 32 --coronas 4
    python3 simulations/periodicity_search.py --controls        # unit cube and featureless chair
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
import sys
import time
from fractions import Fraction
from pathlib import Path

try:
    from pysat.card import CardEnc, EncType
    from pysat.solvers import Solver
except ImportError:  # pragma: no cover
    sys.stderr.write("python-sat is required: pip install python-sat "
                     "(or: python3 -m venv .venv && .venv/bin/pip install python-sat)\n")
    raise

ROOT = Path(__file__).resolve().parents[1]
SOLID = ROOT / "solid" / "r44_solid.json"
DIRS = [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1)]


# ----------------------------------------------------------------------------- geometry

def frac3(v):
    return tuple(Fraction(c) for c in v)


class Tile:
    """cells: integer min-corners of unit cubes; panels: {(cell, dir): [(marker, h), ...]}
    where marker is the marker point RELATIVE to the cell's min corner and h the signed
    height along the outward normal (h > 0 bump, h < 0 dent, h == 0 flat)."""

    def __init__(self, name, cells, panels):
        self.name = name
        self.cells = sorted(set(cells))
        self.panels = panels

    @staticmethod
    def from_solid(path=SOLID, ignore_features=False):
        s = json.loads(Path(path).read_text())
        cells = [tuple(int(c) for c in cell) for cell in s["base_unit_cubes"]]
        cellset = set(cells)
        unit = Fraction(s["height_unit"])
        panels = {}
        # every exposed panel exists even if it carries no feature
        for c in cells:
            for d in DIRS:
                nb = (c[0] + d[0], c[1] + d[1], c[2] + d[2])
                if nb not in cellset:
                    panels[(c, d)] = []
        for p in s["patches"]:
            base = [frac3(q) for q in p["base"]]
            apex = frac3(p["apex"])
            axis = next(i for i in range(3) if len({q[i] for q in base}) == 1)
            plane = base[0][axis]
            centre = tuple(sum(q[i] for q in base) / 4 for i in range(3))
            coef = int(p["coefficient"])
            apex_side = 1 if apex[axis] > plane else -1
            outward = apex_side * (1 if coef > 0 else -1)
            d = [0, 0, 0]
            d[axis] = outward
            d = tuple(d)
            cell = [int(centre[i]) if i != axis else 0 for i in range(3)]
            cell[axis] = int(plane) - 1 if outward > 0 else int(plane)
            cell = tuple(cell)
            if cell not in cellset:
                raise ValueError(f"patch role {p['role']} does not sit on a carrier cell")
            marker = tuple(centre[i] - cell[i] for i in range(3))
            h = Fraction(0) if ignore_features else coef * unit
            panels[(cell, d)].append((marker, h))
        for key, feats in panels.items():
            feats.sort()
        return Tile(s["name"] + ("-featureless" if ignore_features else ""), cells, panels)

    @staticmethod
    def unit_cube():
        c = (0, 0, 0)
        return Tile("unit-cube", [c], {(c, d): [] for d in DIRS})

    def sha256(self):
        blob = json.dumps({"cells": self.cells,
                           "panels": sorted((list(k[0]), list(k[1]),
                                             [[str(x) for x in m] + [str(h)] for m, h in v])
                                            for k, v in self.panels.items())},
                          sort_keys=True).encode()
        return hashlib.sha256(blob).hexdigest()


def frames(proper_only):
    out = []
    for perm in itertools.permutations(range(3)):
        for signs in itertools.product((1, -1), repeat=3):
            # matrix M with M[i][perm[i]] = signs[i]; det = sign(perm) * prod(signs)
            parity = sum(1 for i in range(3) for j in range(i) if perm[j] > perm[i]) % 2
            det = (-1) ** parity * signs[0] * signs[1] * signs[2]
            if proper_only and det < 0:
                continue
            out.append((perm, signs))
    return out


def apply_frame(fr, v):
    perm, signs = fr
    return tuple(signs[i] * v[perm[i]] for i in range(3))


def apply_frame_int(fr, v):
    return tuple(int(x) for x in apply_frame(fr, v))


class FramedTile:
    """The tile moved by one frame (shift 0): cells and, per panel, a shift-invariant
    signature of its features relative to the unit square it lies on, plus the negated
    signature (what a compatible facing panel must carry)."""

    __slots__ = ("frame", "cells", "panels")

    def __init__(self, tile, fr):
        self.frame = fr
        self.cells = [self._cell_image(fr, c) for c in tile.cells]
        self.panels = {}
        for (c, d), feats in tile.panels.items():
            cw = self._cell_image(fr, c)
            dw = apply_frame_int(fr, d)
            origin = tuple(cw[i] + (dw[i] if dw[i] > 0 else 0) for i in range(3))
            sig = []
            for m, h in feats:
                w = apply_frame(fr, (c[0] + m[0], c[1] + m[1], c[2] + m[2]))
                sig.append((tuple(w[i] - origin[i] for i in range(3)), h))
            sig.sort()
            neg = tuple((m, -h) for m, h in sig)
            self.panels[(cw, dw)] = (tuple(sig), neg)

    @staticmethod
    def _cell_image(fr, c):
        corners = [apply_frame_int(fr, (c[0] + a, c[1] + b, c[2] + e))
                   for a in (0, 1) for b in (0, 1) for e in (0, 1)]
        return tuple(min(k[i] for k in corners) for i in range(3))


class Placed:
    """A copy = framed tile + integer shift.  cells: world min corners;
    panels: {(cell, dir): (sig, negsig)} with signatures relative to the shared square."""

    __slots__ = ("frame", "shift", "cells", "panels")

    def __init__(self, ft, shift):
        self.frame = ft.frame
        self.shift = shift
        self.cells = [(c[0] + shift[0], c[1] + shift[1], c[2] + shift[2]) for c in ft.cells]
        self.panels = {((c[0] + shift[0], c[1] + shift[1], c[2] + shift[2]), d): sigs
                       for (c, d), sigs in ft.panels.items()}


# ----------------------------------------------------------------------------- lattices

def hnf_lattices(index):
    """All full-rank sublattices of Z^3 of the given index, as lower-triangular HNF rows
    r1=(a,0,0), r2=(d,b,0), r3=(e,f,c) with abc=index, 0<=d,e<a, 0<=f<b."""
    for a in range(1, index + 1):
        if index % a:
            continue
        for b in range(1, index // a + 1):
            if (index // a) % b:
                continue
            c = index // (a * b)
            for d in range(a):
                for e in range(a):
                    for f in range(b):
                        yield ((a, 0, 0), (d, b, 0), (e, f, c))


def reduce_mod(v, L):
    (a, _, _), (d, b, _), (e, f, c) = L
    x, y, z = v
    k = z // c
    x, y, z = x - k * e, y - k * f, z - k * c
    k = y // b
    x, y = x - k * d, y - k * b
    x = x % a
    return (x, y, z)


# ----------------------------------------------------------------------------- SAT models

class Progress:
    def __init__(self, quiet):
        self.quiet = quiet
        self.t0 = time.time()
        self.last = 0.0

    def line(self, msg, force=False):
        if self.quiet:
            return
        now = time.time()
        if force or now - self.last > 0.2:
            sys.stdout.write("\r" + msg[:180].ljust(180))
            sys.stdout.flush()
            self.last = now

    def done(self, msg):
        if self.quiet:
            return
        sys.stdout.write("\r" + msg.ljust(180) + "\n")
        sys.stdout.flush()


def build_placements(tile, frs, shifts, cell_key):
    """Placements for the given shifts; cell_key maps world cells to canonical keys
    (identity for regions, reduce_mod for tori).  Drops self-overlapping copies."""
    out = []
    for fr in frs:
        ft = FramedTile(tile, fr)
        for t in shifts:
            p = Placed(ft, t)
            keys = [cell_key(c) for c in p.cells]
            if len(set(keys)) != len(keys):
                continue
            out.append((p, keys))
    return out


def compatibility_pairwise(placements, cell_key, var, top):
    """Transparent encoding: one binary clause per incompatible pair of facing panels (and a
    unit clause when a copy's own panels face each other incompatibly).  Two facing panels
    are compatible iff one's signature equals the other's negated signature.  Quadratic in
    the number of copies per square; kept for cross-checking (--encoding pairwise)."""
    by_panel = {}
    for idx, (p, _) in enumerate(placements):
        for (cw, dw), (sig, neg) in p.panels.items():
            by_panel.setdefault((cell_key(cw), dw), []).append((idx, sig, neg))
    clauses = set()
    for (ck, d), lst in by_panel.items():
        nb = cell_key((ck[0] + d[0], ck[1] + d[1], ck[2] + d[2]))
        facing = by_panel.get((nb, (-d[0], -d[1], -d[2])), [])
        for ia, sa, _ in lst:
            for ib, _, nb_neg in facing:
                if sa == nb_neg:
                    continue
                clauses.add((-var(ia),) if ia == ib else (-var(min(ia, ib)), -var(max(ia, ib))))
    return [list(c) for c in clauses], top


def compatibility_slots(placements, cell_key, var, top):
    """Compact encoding.  For every unit square s of the grid and each side (+/-) introduce
    c[s,side] = "a copy presents a panel on that side" and y[s,side,p,h] = "that panel has a
    feature of height h at marker point p".  Each copy implies its c and y literals, each c/y
    literal implies the disjunction of the copies that present it (so nothing is asserted
    without a copy), and for every y[s,side,p,h]:  y ∧ c[s,-side] → y[s,-side,p,-h].
    Hence two facing panels must carry exactly opposite features at every marker point,
    which is the same compatibility relation as the pairwise encoding."""
    nxt = [top]

    def fresh():
        nxt[0] += 1
        return nxt[0]

    c_var, y_var = {}, {}
    c_src, y_src = {}, {}
    clauses = []
    for idx, (p, _) in enumerate(placements):
        x = var(idx)
        for (cw, dw), (sig, _) in p.panels.items():
            axis = next(i for i in range(3) if dw[i])
            side = dw[axis]
            origin = tuple(cw[i] + (dw[i] if dw[i] > 0 else 0) for i in range(3))
            sq = (cell_key(origin), axis)
            ck = (sq, side)
            if ck not in c_var:
                c_var[ck] = fresh()
            clauses.append([-x, c_var[ck]])
            c_src.setdefault(ck, []).append(x)
            for m, h in sig:
                yk = (sq, side, m, h)
                if yk not in y_var:
                    y_var[yk] = fresh()
                clauses.append([-x, y_var[yk]])
                y_src.setdefault(yk, []).append(x)
    for ck, lits in c_src.items():
        clauses.append([-c_var[ck]] + lits)
    for yk, lits in y_src.items():
        clauses.append([-y_var[yk]] + lits)
    for (sq, side, m, h), y in y_var.items():
        other = (sq, -side)
        if other not in c_var:
            continue  # the facing side is never covered by a panel in this instance
        opp = (sq, -side, m, -h)
        if opp in y_var:
            clauses.append([-y, -c_var[other], y_var[opp]])
        else:
            clauses.append([-y, -c_var[other]])  # no copy can supply the opposite feature
    return clauses, nxt[0]


ENCODINGS = {"slots": compatibility_slots, "pairwise": compatibility_pairwise}


def solve_torus(tile, frs, L, solver_name, encoding="slots"):
    (a, _, _), (d, b, _), (e, f, c) = L
    shifts = [(x, y, z) for x in range(a) for y in range(b) for z in range(c)]
    key = lambda v: reduce_mod(v, L)
    placements = build_placements(tile, frs, shifts, key)
    var = lambda i: i + 1
    top = len(placements)
    covers = {}
    for idx, (_, keys) in enumerate(placements):
        for k in keys:
            covers.setdefault(k, []).append(var(idx))
    cells = [key((x, y, z)) for x in range(a) for y in range(b) for z in range(c)]
    clauses, top = ENCODINGS[encoding](placements, key, var, top)
    nclauses = len(clauses)
    with Solver(name=solver_name) as s:
        for cl in clauses:
            s.add_clause(cl)
        for k in cells:
            lits = covers.get(k, [])
            if not lits:
                return False, None, len(placements), {"variables": top, "clauses": nclauses}
            enc = CardEnc.equals(lits=lits, bound=1, top_id=top, encoding=EncType.seqcounter)
            top = max(top, enc.nv)
            nclauses += len(enc.clauses)
            for cl in enc.clauses:
                s.add_clause(cl)
        sat = s.solve()
        witness = None
        if sat:
            model = set(l for l in s.get_model() if l > 0)
            witness = [{"frame": [list(p.frame[0]), list(p.frame[1])], "shift": list(p.shift)}
                       for idx, (p, _) in enumerate(placements) if var(idx) in model]
        return sat, witness, len(placements), {"variables": top, "clauses": nclauses}


def solve_corona(tile, frs, k, solver_name, encoding="slots"):
    seed = Placed(FramedTile(tile, ((0, 1, 2), (1, 1, 1))), (0, 0, 0))
    lo = [min(c[i] for c in seed.cells) for i in range(3)]
    hi = [max(c[i] for c in seed.cells) for i in range(3)]
    # cells within Chebyshev distance k of SOME seed cell (not the seed's bounding box)
    inner = {(s[0] + dx, s[1] + dy, s[2] + dz) for s in seed.cells
             for dx in range(-k, k + 1) for dy in range(-k, k + 1) for dz in range(-k, k + 1)}
    ext = 2  # a copy touching an inner cell lies within 2 of it (chair extent)
    shifts = [(x, y, z) for x in range(lo[0] - k - ext - 2, hi[0] + k + ext + 3)
              for y in range(lo[1] - k - ext - 2, hi[1] + k + ext + 3)
              for z in range(lo[2] - k - ext - 2, hi[2] + k + ext + 3)]
    key = lambda v: v
    placements = build_placements(tile, frs, shifts, key)
    # keep only copies that cover at least one inner cell (others are irrelevant)
    placements = [(p, keys) for p, keys in placements if any(c in inner for c in keys)]
    var = lambda i: i + 1
    top = len(placements)
    seed_idx = next(i for i, (p, _) in enumerate(placements)
                    if p.frame == seed.frame and p.shift == (0, 0, 0))
    covers = {}
    for idx, (_, keys) in enumerate(placements):
        for c in keys:
            covers.setdefault(c, []).append(var(idx))
    clauses, top = ENCODINGS[encoding](placements, key, var, top)
    nclauses = len(clauses) + 1
    with Solver(name=solver_name) as s:
        for cl in clauses:
            s.add_clause(cl)
        s.add_clause([var(seed_idx)])
        for c, lits in covers.items():
            if c in inner:
                enc = CardEnc.equals(lits=lits, bound=1, top_id=top, encoding=EncType.seqcounter)
            else:
                enc = CardEnc.atmost(lits=lits, bound=1, top_id=top, encoding=EncType.seqcounter)
            top = max(top, enc.nv)
            nclauses += len(enc.clauses)
            for cl in enc.clauses:
                s.add_clause(cl)
        sat = s.solve()
        count = None
        if sat:
            model = set(l for l in s.get_model() if l > 0)
            count = sum(1 for idx in range(len(placements)) if var(idx) in model)
        return sat, count, len(placements), {"variables": top, "clauses": nclauses}


# ----------------------------------------------------------------------------- drivers

def run_torus(tile, frs, max_index, solver_name, prog, verbose, encoding="slots", checkpoint=None):
    results = {"max_index": max_index, "per_index": [], "sat_witness": None, "complete": False}
    total = sum(1 for n in range(1, max_index + 1) for _ in hnf_lattices(n))
    seen = 0
    t0 = time.time()
    for n in range(1, max_index + 1):
        lattices = list(hnf_lattices(n))
        unsat = 0
        tn = time.time()
        agg = {"placements_max": 0, "variables_max": 0, "clauses_max": 0,
               "variables_total": 0, "clauses_total": 0}
        for i, L in enumerate(lattices):
            sat, witness, nplace, stats = solve_torus(tile, frs, L, solver_name, encoding)
            agg["placements_max"] = max(agg["placements_max"], nplace)
            agg["variables_max"] = max(agg["variables_max"], stats["variables"])
            agg["clauses_max"] = max(agg["clauses_max"], stats["clauses"])
            agg["variables_total"] += stats["variables"]
            agg["clauses_total"] += stats["clauses"]
            seen += 1
            el = time.time() - t0
            eta = el / seen * (total - seen) if seen else 0
            prog.line(f"[torus] index {n}: lattice {i + 1}/{len(lattices)}  "
                      f"unsat {unsat}  placements {nplace}  formula {stats['variables']} vars / "
                      f"{stats['clauses']} clauses  elapsed {el:6.0f}s  eta {eta:6.0f}s")
            if verbose:
                prog.done(f"[torus] index {n} L={L} -> {'SAT' if sat else 'UNSAT'} "
                          f"({nplace} placements; {stats['variables']} vars, {stats['clauses']} clauses)")
            if sat:
                results["sat_witness"] = {"index": n, "lattice": [list(r) for r in L],
                                          "copies": witness, "placements": nplace,
                                          "formula": stats}
                results["per_index"].append({"index": n, "lattices": len(lattices),
                                             "unsat": unsat, "sat_at": [list(r) for r in L],
                                             "formula_aggregates": agg})
                prog.done(f"[torus] index {n}: PERIODIC TILING FOUND with lattice rows {L}")
                results["complete"] = True
                if checkpoint:
                    checkpoint("torus", results)
                return results
            unsat += 1
        results["per_index"].append({"index": n, "lattices": len(lattices), "unsat": unsat,
                                     "seconds": round(time.time() - tn, 2),
                                     "formula_aggregates": agg})
        prog.done(f"[torus] index {n}: {len(lattices)} lattices, all UNSAT "
                  f"({time.time() - tn:.1f}s)")
        if checkpoint:
            checkpoint("torus", results)
    results["complete"] = True
    if checkpoint:
        checkpoint("torus", results)
    return results


def run_corona(tile, frs, max_k, solver_name, prog, encoding="slots", checkpoint=None):
    results = {"max_coronas": max_k, "per_k": [], "largest_sat": 0, "complete": False}
    for k in range(1, max_k + 1):
        tk = time.time()
        prog.line(f"[corona] k={k}: building and solving ...")
        sat, count, nplace, stats = solve_corona(tile, frs, k, solver_name, encoding)
        results["per_k"].append({"k": k, "sat": sat, "copies_used": count,
                                 "placements": nplace, "formula": stats,
                                 "seconds": round(time.time() - tk, 2)})
        prog.done(f"[corona] k={k}: {'SAT' if sat else 'UNSAT'}"
                  f"{f' ({count} copies)' if sat else ''}  "
                  f"{nplace} placements; {stats['variables']} vars, {stats['clauses']} clauses, "
                  f"{time.time() - tk:.1f}s")
        if sat:
            results["largest_sat"] = k
        if checkpoint:
            checkpoint("corona", results)
        if not sat:
            break
    results["complete"] = True
    if checkpoint:
        checkpoint("corona", results)
    return results


def run_selftest(tile, frs, solver_name, prog, max_index=4, max_k=1):
    """Both encodings must give identical verdicts on every small instance: R44 tori up to
    max_index (all expected UNSAT), the featureless chair up to index 7 (SAT appears at 7, so
    the two encodings are also compared on satisfiable instances), and the k=1 corona."""
    mismatches = []
    checked = 0
    sat_seen = 0
    chair = Tile.from_solid(ignore_features=True)
    for name, t, top_index in ((tile.name, tile, max_index), (chair.name, chair, 7)):
        for n in range(1, top_index + 1):
            for L in hnf_lattices(n):
                a = solve_torus(t, frs, L, solver_name, "slots")[0]
                b = solve_torus(t, frs, L, solver_name, "pairwise")[0]
                checked += 1
                sat_seen += int(a and b)
                if a != b:
                    mismatches.append({"tile": name, "lattice": [list(r) for r in L],
                                       "slots": a, "pairwise": b})
                prog.line(f"[selftest] {name} index {n} L={L}: slots={a} pairwise={b}")
    for k in range(1, max_k + 1):
        a = solve_corona(tile, frs, k, solver_name, "slots")[0]
        b = solve_corona(tile, frs, k, solver_name, "pairwise")[0]
        checked += 1
        sat_seen += int(a and b)
        if a != b:
            mismatches.append({"corona": k, "slots": a, "pairwise": b})
        prog.done(f"[selftest] corona k={k}: slots={a} pairwise={b}")
    prog.done(f"[selftest] {checked} instances ({sat_seen} satisfiable), {len(mismatches)} mismatches")
    return {"instances": checked, "satisfiable": sat_seen, "mismatches": mismatches}


def write_receipt(path, report):
    """Atomic replace: write a sibling temp file, then rename over the receipt."""
    path = Path(path)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(json.dumps(report, indent=1))
    os.replace(tmp, path)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--index", type=int, default=16, help="max lattice index for the torus search")
    ap.add_argument("--coronas", type=int, default=3, help="max corona radius k (0 to skip)")
    ap.add_argument("--proper-only", action="store_true", help="exclude reflected copies")
    ap.add_argument("--solver", default="cadical153")
    ap.add_argument("--encoding", choices=sorted(ENCODINGS), default="slots",
                    help="compatibility encoding (slots: compact; pairwise: one clause per bad pair)")
    ap.add_argument("--selftest", action="store_true",
                    help="run both encodings on small instances of R44 and require identical verdicts")
    ap.add_argument("--controls", action="store_true",
                    help="run the positive controls (unit cube, featureless chair) instead of R44")
    ap.add_argument("--control-index", type=int, default=8)
    ap.add_argument("--out", default=str(ROOT / "simulations" / "periodicity_search_report.json"))
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--verbose", action="store_true", help="one line per lattice")
    args = ap.parse_args()
    prog = Progress(args.quiet)
    frs = frames(args.proper_only)
    report = {"script": "simulations/periodicity_search.py", "solver": args.solver,
              "frames": len(frs), "proper_only": args.proper_only,
              "model": "grid-registered copies; compatibility = disjoint cells and exactly "
                       "opposite features on every shared unit panel (exact rationals)",
              "caveat": "evidence, not proof: registered copies only; full-rank period lattices "
                        "up to the stated index only", "runs": []}
    started = time.time()
    report["encoding"] = args.encoding
    if args.selftest:
        tile = Tile.from_solid()
        r = run_selftest(tile, frs, args.solver, prog)
        report["runs"].append({"tile": tile.name, "sha256": tile.sha256(), "selftest": r})
        report["seconds"] = round(time.time() - started, 1)
        write_receipt(args.out, report)
        ok = not r["mismatches"]
        print("RESULT selftest:", "PASS" if ok else "FAIL")
        sys.exit(0 if ok else 1)
    if args.controls:
        for tile, idx in ((Tile.unit_cube(), 2),
                          (Tile.from_solid(ignore_features=True), args.control_index)):
            prog.done(f"== control: {tile.name}  (torus search up to index {idx}; a periodic "
                      f"tiling MUST be found for the search to count as capable)")
            r = run_torus(tile, frs, idx, args.solver, prog, args.verbose, args.encoding)
            found = r["sat_witness"] is not None
            prog.done(f"== control {tile.name}: {'FOUND periodic tiling' if found else 'NOT found'}")
            report["runs"].append({"tile": tile.name, "sha256": tile.sha256(), "torus": r,
                                   "control_expectation": "periodic tiling found",
                                   "control_passed": found})
    else:
        tile = Tile.from_solid()
        prog.done(f"== {tile.name}: {len(tile.cells)} cells, {len(tile.panels)} panels, "
                  f"{sum(len(v) for v in tile.panels.values())} features, {len(frs)} frames")
        run = {"tile": tile.name, "sha256": tile.sha256(),
               "solid_sha256": hashlib.sha256(SOLID.read_bytes()).hexdigest()}
        report["runs"].append(run)

        def checkpoint(kind, partial):
            # the receipt is rewritten after every index and every corona radius, so a long
            # run that is interrupted still leaves a receipt of everything it established
            run[kind] = partial
            report["seconds"] = round(time.time() - started, 1)
            report["status"] = "in progress"
            write_receipt(args.out, report)

        if args.index > 0:
            run["torus"] = run_torus(tile, frs, args.index, args.solver, prog, args.verbose,
                                     args.encoding, checkpoint)
        if args.coronas > 0:
            run["corona"] = run_corona(tile, frs, args.coronas, args.solver, prog, args.encoding,
                                       checkpoint)
        report["status"] = "complete"
    report["seconds"] = round(time.time() - started, 1)
    write_receipt(args.out, report)
    prog.done(f"report written to {args.out} ({report['seconds']}s)")
    if not args.controls:
        run = report["runs"][0]
        scope = ("registered copies, 24 proper frames only" if args.proper_only
                 else "registered copies, all 48 frames incl. reflections")
        if "torus" in run:
            w = run["torus"]["sat_witness"]
            print("RESULT torus:", f"periodic tiling found at index {w['index']} ({scope})" if w else
                  f"no full-rank period lattice of index <= {args.index} ({scope})")
        if "corona" in run:
            tried = len(run["corona"]["per_k"])
            print("RESULT corona:", f"largest surrounded radius k = {run['corona']['largest_sat']}"
                  f" of {tried} tried (requested {args.coronas}; {scope})")
    else:
        ok = all(r["control_passed"] for r in report["runs"])
        print("RESULT controls:", "PASS" if ok else "FAIL")
        sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
