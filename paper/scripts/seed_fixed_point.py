#!/usr/bin/env python3
"""SUPERSEDED (2026-09-09) by seed_language_closure.py: this level-3 search finds 24 of the 27 fixed
seeds (external review B1). Kept for the record of the earlier count.

Two-sided fixed point of the R44 cell substitution (DECISIONS.md Q-B, ledger L3).

Reads only certificates/candidate_certificate.json and reconstructs the 168-label
substitution phi(label, delta) exactly as verify/substitution_modular_coincidence.py does.
A fixed point of the substitution on all of Z^3 is determined by a 2x2x2 seed block around
the origin: the cell -delta (delta in {0,1}^3) has parent floor(-delta/2) = -delta and
residue delta, so its label j must satisfy phi(j, delta) = j; the block must be legal
(occur in the level-k image of a single cell). Then the union of the iterated images is a
labelling of Z^3 fixed by the substitution whose every finite patch is legal.
Standard library only.
"""
import itertools, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "verify"))
import substitution_modular_coincidence as m  # noqa: E402

cert = json.loads(m.CERTIFICATE.read_text())
frames = tuple(m.frame_from_json(r) for r in cert["orientation_group"])
children = tuple((m.frame_from_json(r[0]), tuple(r[1])) for r in cert["children"])
labels = [(f, c) for f in frames for c in m.CHAIR_CELLS]
index = {l: i for i, l in enumerate(labels)}
phi = {}
for frame in frames:
    owners = {}
    for cf, co in m.child_poses(frame, children):
        for cell in m.CHAIR_CELLS:
            owners.setdefault(m.cell_lower(cf, co, cell), []).append((cf, cell))
    for cell in m.CHAIR_CELLS:
        src = m.cell_lower(frame, m.ORIGIN, cell)
        for d in m.BITS:
            (tl,) = owners[m.add(m.scale(2, src), d)]
            phi[index[(frame, cell)], d] = index[tl]
assert len(phi) == 168 * 8

fixed = {d: sorted(j for j in range(168) if phi[j, d] == j) for d in m.BITS}
print("labels fixed at residue delta (phi(j,delta)=j):", {d: len(v) for d, v in fixed.items()})

def level_patch(j, k):
    """cells of the level-k image of one cell with label j, at positions in [0,2^k)^3."""
    patch = {(0, 0, 0): j}
    for _ in range(k):
        nxt = {}
        for pos, lab in patch.items():
            for d in m.BITS:
                nxt[m.add(m.scale(2, pos), d)] = phi[lab, d]
        patch = nxt
    return patch

K = 3
seeds = set()
for j in range(168):
    patch = level_patch(j, K)
    n = 2 ** K
    for c0 in itertools.product(range(n - 1), repeat=3):
        ok = True
        block = []
        for e in m.BITS:
            delta = tuple(1 - x for x in e)          # cell c0+e plays the role of -delta
            lab = patch[m.add(c0, e)]
            if phi[lab, delta] != lab:
                ok = False; break
            block.append((e, lab))
        if ok:
            seeds.add(tuple(block))
print(f"legal 2x2x2 seed blocks found inside level-{K} patches:", len(seeds))
if seeds:
    blk = sorted(seeds)[0]
    print("one seed block (cell offset e from lower corner (-1,-1,-1) -> label):")
    for e, lab in blk:
        f, c = labels[lab]
        print("  ", e, "-> label", lab, "frame", frames.index(f), "cell", c)
    # sanity: iterate the seed twice and check invariance in place on Z^3 near the origin
    world = {tuple(x - 1 for x in e): lab for e, lab in blk}
    for _ in range(2):
        nxt = {}
        for pos, lab in world.items():
            for d in m.BITS:
                nxt[m.add(m.scale(2, pos), d)] = phi[lab, d]
        for pos, lab in world.items():
            assert nxt[pos] == lab, "seed block not invariant in place"
        world = nxt
    print("in-place invariance of the seed under two iterations: OK; cells now:", len(world))
    print("STATUS: PASS" )
else:
    print("STATUS: NO LEGAL SEED FOUND at level", K)
