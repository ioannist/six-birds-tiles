#!/usr/bin/env python3
"""Fixed seeds of the R44 cell substitution by exact closure of the 2x2x2 block language
(external review 2026-09-09, finding B1; supersedes seed_fixed_point.py's level-3 search).

Reconstructs the 168-label substitution phi from certificates/candidate_certificate.json through
the repository's own module (verify/substitution_modular_coincidence.py), then:
1. closes the language of 2x2x2 blocks occurring in some iterate of a single label: start from the
   168 first-level blocks, substitute every known block into a 4x4x4 block and adjoin its 27 windows,
   repeat to closure (a 2-block of sigma^n(i), n >= 2, lies in a window of the substitution of a legal
   2-block of sigma^(n-1)(i), so the closure is the whole language);
2. counts the seeds, i.e. blocks on {-1,0}^3 whose eight labels are fixed by their residue maps, and
   checks that each seed reproduces itself in place under iteration (sigma^n(w) extends sigma^(n-1)(w));
3. splits the seeds into orbits under the 24 proper frames and records each seed's stabilizer;
4. checks that the substitution commutes with the 24 frames, on labelled cell configurations
   (sigma(R.l) = R.sigma(l)) and on child poses, so that Sym(T_w) is the stabilizer of the seed w
   (Section 8.2); checks the reviewer's generators r, s of the order-8 stabilizer;
5. lists the whole native poses of the order-8 seeds and of the seed w0 of the external report,
   with their persistence roles (which child of itself each root is).
Standard library only; prints STATUS: PASS with the numbers, or FAIL.
"""
import itertools
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "verify"))
import substitution_modular_coincidence as m  # noqa: E402

BITS = tuple(itertools.product((0, 1), repeat=3))
POS = tuple(itertools.product((-1, 0), repeat=3))          # the seed cube {-1,0}^3
cert = json.loads(m.CERTIFICATE.read_text())
frames = tuple(m.frame_from_json(r) for r in cert["orientation_group"])
children = tuple((m.frame_from_json(r[0]), tuple(r[1])) for r in cert["children"])
labels = [(f, c) for f in frames for c in m.CHAIR_CELLS]
index = {l: i for i, l in enumerate(labels)}
assert len(labels) == 168
UNIT = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]


def neg(v):
    return m.scale(-1, v)


def lower(frame, x):
    """Lower corner of the unit cube R([x, x+1]^3): the action of the frame on cells."""
    return m.cell_lower(frame, m.ORIGIN, x)


phi = {}
for frame in frames:
    owners = {}
    for cf, co in m.child_poses(frame, children):
        for cell in m.CHAIR_CELLS:
            owners.setdefault(m.cell_lower(cf, co, cell), []).append((cf, cell))
    for cell in m.CHAIR_CELLS:
        src = m.cell_lower(frame, m.ORIGIN, cell)
        for d in BITS:
            (tl,) = owners[m.add(m.scale(2, src), d)]
            phi[index[(frame, cell)], d] = index[tl]
assert len(phi) == 168 * 8


def block_of(label):
    return tuple(phi[label, d] for d in BITS)


# windows: a 2-block with lower corner o in {0,1,2}^3 of the 4-block sigma(block); position b of the
# window sits at parent cell (o+b)//2 with residue (o+b)%2
windows = []
for o in itertools.product(range(3), repeat=3):
    windows.append(tuple((BITS.index(tuple((o[k] + b[k]) // 2 for k in range(3))),
                          tuple((o[k] + b[k]) % 2 for k in range(3))) for b in BITS))

language = {block_of(j) for j in range(168)}
sizes = [len(language)]
frontier = set(language)
while frontier:
    new = set()
    for blk in frontier:
        for win in windows:
            t = tuple(phi[blk[i], d] for i, d in win)
            if t not in language and t not in new:
                new.add(t)
    language |= new
    frontier = new
    sizes.append(len(language))
    assert len(sizes) < 20
closed = all(tuple(phi[blk[i], d] for i, d in win) in language for blk in language for win in windows)

# seeds: cell -delta (delta in {0,1}^3) has parent -delta and residue delta
residue = tuple(tuple(x % 2 for x in p) for p in POS)
seeds = sorted(blk for blk in language if all(phi[blk[i], residue[i]] == blk[i] for i in range(8)))


def substitute(conf):
    """sigma on a labelled cell configuration {cell: label}."""
    return {m.add(m.scale(2, x), d): phi[lab, d] for x, lab in conf.items() for d in BITS}


def seed_conf(seed):
    return dict(zip(POS, seed))


def nested_in_place(seed, depth=3):
    conf = seed_conf(seed)
    for _ in range(depth):
        nxt = substitute(conf)
        if any(nxt[x] != lab for x, lab in conf.items()):
            return False
        conf = nxt
    return True


nesting_ok = all(nested_in_place(s) for s in seeds)


# frame action on labelled configurations: cell x -> lower(R, x), label (f, c) -> (R f, c)
def act_conf(R, conf):
    return {lower(R, x): index[(m.compose(R, labels[lab][0]), labels[lab][1])] for x, lab in conf.items()}


def act(R, seed):
    conf = act_conf(R, seed_conf(seed))
    return tuple(conf[p] for p in POS)


# covariance on labelled configurations: sigma(R.l) = R.sigma(l) for one-cell configurations
conf_cov = 0
for R in frames:
    for j in range(168):
        for x in ((0, 0, 0), (-1, 0, 0), (2, -3, 1)):
            one = {x: j}
            if substitute(act_conf(R, one)) != act_conf(R, substitute(one)):
                raise SystemExit("covariance failure")
            conf_cov += 1
# covariance on child poses: children of the rotated pose are the rotated children
pose_cov = 0
for R in frames:
    for f in frames:
        left = sorted(m.child_poses(m.compose(R, f), children))
        right = sorted((m.compose(R, cf), m.act(R, co)) for cf, co in m.child_poses(f, children))
        assert left == right
        pose_cov += 1

remaining = set(seeds)
orbits = []
while remaining:
    root = min(remaining)
    orb = {act(R, root) for R in frames}
    assert orb <= set(seeds)
    orbits.append(sorted(orb))
    remaining -= orb
stab = {s: [R for R in frames if act(R, s) == s] for s in seeds}
hist = {}
for s in seeds:
    hist[len(stab[s])] = hist.get(len(stab[s]), 0) + 1


def poses_of(seed):
    out = set()
    for p, lab in zip(POS, seed):
        f, c = labels[lab]
        out.add((f, m.add(p, neg(lower(f, c)))))
    return sorted(out)


def self_roles(pose):
    f, t = pose
    return [k for k, (cf, co) in enumerate(m.child_poses(f, children))
            if cf == f and m.add(m.scale(2, t), co) == t]


def frame_of_map(fn):
    """The frame among the 24 acting as the given linear map on points."""
    return [R for R in frames if all(m.act(R, p) == fn(p) for p in UNIT)]


order8 = [s for s in seeds if len(stab[s]) == 8]
first8 = min(order8)
r_frame = frame_of_map(lambda p: (p[2], p[1], -p[0]))
s_frame = frame_of_map(lambda p: (-p[0], -p[1], p[2]))
gens_ok = len(r_frame) == 1 and len(s_frame) == 1 and r_frame[0] in stab[first8] and s_frame[0] in stab[first8]
if gens_ok:
    identity = frame_of_map(lambda p: p)[0]
    grp = {identity}
    changed = True
    while changed:
        changed = False
        for a in list(grp):
            for g in (r_frame[0], s_frame[0]):
                c = m.compose(a, g)
                if c not in grp:
                    grp.add(c)
                    changed = True
    gens_ok = len(grp) == 8 and grp == set(stab[first8])

w0 = (6, 0, 4, 5, 2, 3, 0, 1)
print("language closure:", sizes, "closed:", closed)
print("fixed seeds:", len(seeds), "orbit sizes:", sorted(len(o) for o in orbits), "stabilizer histogram:", hist)
print("in-place nesting of every seed to depth 3:", nesting_ok)
print("covariance checks: configurations", conf_cov, "child poses", pose_cov)
print("order-8 seeds:")
for s in order8:
    ps = poses_of(s)
    print("  ", s, "whole poses:", len(ps), "frames", [frames.index(f) for f, _ in ps],
          "origins", sorted({t for _, t in ps}), "self-roles", [self_roles(p) for p in ps])
print("reviewer generators r=(z,y,-x), s=(-x,-y,z) generate the stabilizer of", first8, ":", gens_ok)
print("w0 =", w0, "is a seed:", w0 in seeds, "stabilizer order:", len(stab[w0]) if w0 in seeds else None)
if w0 in seeds:
    for p in poses_of(w0):
        print("   pose frame", p[0], "origin", p[1], "self-roles", self_roles(p))
ok = (closed and len(seeds) == 27 and sorted(len(o) for o in orbits) == [3, 24] and hist == {1: 24, 8: 3}
      and nesting_ok and gens_ok and w0 in seeds and len(stab[w0]) == 1
      and all(len(poses_of(s)) == 8 for s in order8) and len(poses_of(w0)) == 2)
print("STATUS:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
