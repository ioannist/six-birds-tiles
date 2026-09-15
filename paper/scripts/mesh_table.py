#!/usr/bin/env python3
"""Table 5 (FIGURES.md): mesh facts of Q, computed from solid/r44_solid.json with exact
arithmetic and cross-checked against the file's own counts. Not verification (the
checks are `boundary_sphere`, `mesh_angle_audit`, verify/boundary_sphere.py); a table."""
import argparse
import json
import os
from fractions import Fraction

from _texutil import ROOT, common_args, finish, num, write_rows


def main():
    ap = common_args(argparse.ArgumentParser(description=__doc__), lean=False)
    args = ap.parse_args()
    d = json.load(open(os.path.join(ROOT, "solid", "r44_solid.json"), encoding="utf-8"))
    verts = [tuple(Fraction(x) for x in v) for v in d["vertices"]]
    tris = d["triangles"]
    V, F = len(verts), len(tris)
    edges = set()
    for a, b, c in tris:
        for u, w in ((a, b), (b, c), (c, a)):
            edges.add((min(u, w), max(u, w)))
    E = len(edges)
    chi = V - E + F
    # exact signed volume by the divergence formula over the oriented triangles
    vol6 = Fraction(0)
    for a, b, c in tris:
        p, q, r = verts[a], verts[b], verts[c]
        vol6 += (p[0] * (q[1] * r[2] - q[2] * r[1]) - p[1] * (q[0] * r[2] - q[2] * r[0])
                 + p[2] * (q[0] * r[1] - q[1] * r[0]))
    vol = abs(vol6) / 6
    patches = d["patches"]
    feature_edges = 8 * len(patches)
    classes = {}
    for p in patches:
        mag, sign = abs(int(p["coefficient"])), (1 if int(p["coefficient"]) > 0 else -1)
        classes[(mag, "base", sign)] = classes.get((mag, "base", sign), 0) + 4
        classes[(mag, "ridge", sign)] = classes.get((mag, "ridge", sign), 0) + 4
    per_class = sorted(set(classes.values()))
    ok = (V == d["vertex_count"] and E == d["edge_count"] and F == d["triangle_count"]
          and vol == Fraction(d["exact_volume"]) and chi == 2 and len(patches) == 192
          and len(classes) == 48 and per_class == [32])
    rows = [
        ["vertices $V$", f"${num(V)}$"],
        ["edges $E$", f"${num(E)}$"],
        ["triangles $F$", f"${num(F)}$"],
        ["$V-E+F$", f"${chi}$"],
        ["volume (exact, divergence formula)", f"${vol}$"],
        ["features (square pyramids)", f"${len(patches)}$"],
        ["feature edges; classes (magnitude, base/ridge, sign) $\\times$ edges per class",
         f"${num(feature_edges)}$; $48\\times{per_class[0]}$"],
        ["base half-width $\\eta$; height unit", f"${Fraction(d['base_halfwidth'])}$; ${Fraction(d['height_unit'])}$"],
    ]
    write_rows(args.out, "mesh_table", rows,
               "from solid/r44_solid.json, exact arithmetic, cross-checked against its counts",
               colspec="L{0.66\\linewidth} r", header=["quantity", "value"])
    finish(ok, "mesh counts or volume disagree with the solid file")


if __name__ == "__main__":
    main()
