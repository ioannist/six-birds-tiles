#!/usr/bin/env python3
"""How fast the R44 modular coincidence sets in (exact, standard library only).

Tier: T2, finite and replayed.  The substitution on the 168 labelled unit cells, its primitivity
and its least modular-coincidence depth (3, at address (0,0,2)) are already checked upstream
(``verify/substitution_modular_coincidence.py``; T1n in Lean).  The Lee-Moody / Schlottmann
step from there to pure-point diffraction and limit-periodicity is a cited T3 import and is not
touched here.  This script rebuilds the cell substitution independently from the child poses
and adds a RATE the existing checks do not state.

Read the digits of a cell's address from the top.  After M digits the set of labels still
possible is the image of the full label set under M of the eight maps A -> {sigma(j)[b]}.  Only
209 label sets are reachable, 41 with more than one label.  The number of digit words of length
M whose label set is still not a single label is

    c(M) = 1, 8, 64, 176, 400, 848, 1744, ...      c(M+1) = 2 c(M) + 48  for M >= 3,

so c(M) = 28 * 2**M - 48, the undetermined fraction is c(M)/8**M ~ 28 * 4**(-M), and the transfer
matrix on the non-singleton sets has spectral radius exactly 2.  The set of addresses not yet
determined (where window boundaries sit) therefore has box dimension log2(2) = 1 in the 2-adic
internal space Z_2^3 of dimension 3.

    python3 simulations/coincidence_rate.py
"""

from __future__ import annotations

import itertools
from collections import Counter

from r44 import CHAIR_CELLS, frame_apply, frame_determinant, load_json, parse_pose

BITS = list(itertools.product((0, 1), repeat=3))
CELLS = sorted(CHAIR_CELLS)


def rotations():
    return [(p, s) for p in itertools.permutations(range(3))
            for s in itertools.product((1, -1), repeat=3)
            if frame_determinant((p, s)) == 1]


def frame_mul(left, right):
    p, s = left
    q, t = right
    return tuple(q[p[i]] for i in range(3)), tuple(s[i] * t[p[i]] for i in range(3))


def cell_of(frame, t, cell):
    x = frame_apply(frame, cell)
    return tuple(x[i] + t[i] - (1 if frame[1][i] < 0 else 0) for i in range(3))


def cell_substitution():
    certificate = load_json("certificates/candidate_certificate.json")
    children = [parse_pose(p) for p in certificate["children"]]
    frames = rotations()
    labels = [(f, k) for f in frames for k in range(7)]
    index = {l: i for i, l in enumerate(labels)}
    sigma = [[None] * 8 for _ in labels]
    for f in frames:
        owner = {}
        for H, u in children:
            G, t = frame_mul(f, H), frame_apply(f, u)
            for k, c in enumerate(CELLS):
                owner[cell_of(G, t, c)] = (G, k)
        assert len(owner) == 56
        for kk, c in enumerate(CELLS):
            p = cell_of(f, (0, 0, 0), c)
            for b, a in enumerate(BITS):
                sigma[index[(f, kk)]][b] = index[owner[tuple(2 * p[i] + a[i] for i in range(3))]]
    return labels, sigma


def primitive_exponent(sigma, limit=8):
    n = len(sigma)
    step = [set(r) for r in sigma]
    cur = [set(s) for s in step]
    for power in range(1, limit + 1):
        if all(len(c) == n for c in cur):
            return power
        cur = [set().union(*(step[j] for j in c)) for c in cur]


def subset_automaton(sigma):
    full = frozenset(range(len(sigma)))
    state, order, trans = {full: 0}, [full], []
    i = 0
    while i < len(order):
        row = []
        for b in range(8):
            B = frozenset(sigma[j][b] for j in order[i])
            if B not in state:
                state[B] = len(order)
                order.append(B)
            row.append(state[B])
        trans.append(row)
        i += 1
    return order, trans


def counts(sigma, depth=14):
    order, trans = subset_automaton(sigma)
    vec = {0: 1}
    out = []
    for _ in range(depth + 1):
        out.append(sum(vec.values()))
        nxt = Counter()
        for s, n in vec.items():
            for b in range(8):
                d = trans[s][b]
                if len(order[d]) > 1:
                    nxt[d] += n
        vec = nxt
    return out, Counter(len(A) for A in order)


def coincidence_depth(sigma):
    order, trans = subset_automaton(sigma)
    frontier = {(): 0}
    for M in range(1, 8):
        frontier = {w + (b,): trans[s][b] for w, s in frontier.items() for b in range(8)}
        hits = [w for w, s in frontier.items() if len(order[s]) == 1]
        if hits:
            addr = {tuple(sum(BITS[d][ax] << (M - 1 - k) for k, d in enumerate(w)) for ax in range(3))
                    for w in hits}
            return M, addr, len(frontier)


def check():
    labels, sigma = cell_substitution()
    assert len(labels) == 168
    cols = Counter(j for row in sigma for j in row)
    assert set(cols.values()) == {8} and len(cols) == 168
    assert primitive_exponent(sigma) == 3
    M, addr, total = coincidence_depth(sigma)
    assert M == 3 and (0, 0, 2) in addr and len(addr) == 336 and total == 512
    c, sizes = counts(sigma)
    assert c[:7] == [1, 8, 64, 176, 400, 848, 1744]
    assert all(c[m + 1] == 2 * c[m] + 48 for m in range(3, len(c) - 1))
    assert all(c[m] == 28 * 2 ** m - 48 for m in range(3, len(c)))
    assert sum(sizes.values()) == 209 and sum(v for k, v in sizes.items() if k > 1) == 41
    return c, sizes, (M, len(addr), total)


def main():
    c, sizes, (M, n, total) = check()
    print("cell substitution on 168 labels, column sums 8, primitive at power 3")
    print("least modular-coincidence depth %d: %d of %d addresses coincide, (0,0,2) among them" % (M, n, total))
    print("reachable label sets by size:", dict(sorted(sizes.items())))
    print("non-coincident words c(M):", c)
    print("c(M) = 28*2^M - 48 for M >= 3; undetermined fraction ~ 28 * 4^(-M); box dimension 1 in Z_2^3")


if __name__ == "__main__":
    main()
