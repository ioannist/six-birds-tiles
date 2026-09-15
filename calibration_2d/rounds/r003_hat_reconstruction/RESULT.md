# R003 — the bare hat and its forced contextual roles

Known-reference reconstruction, opened after R001/R002. The returned polygon
has the following vertices in the Euclidean basis e1=(1,0),
e2=(1/2,sqrt(3)/2), in boundary order:

    (0,0),(-1,-1),(0,-2),(2,-2),(2,-1),(4,-2),(5,-1),
    (4,0),(3,0),(2,2),(0,3),(0,2),(-1,2).

geometry.py reconstructs this simple boundary from eight closed kites, cancels
the internal edges, checks nonadjacent boundary edges do not intersect, checks
area 8sqrt(3), and verifies the twelve grid isometries exactly. The shape is a
compact connected topological disk with nonempty interior. It has no physical
marks or matching-rule decorations. Reflections are admitted.

## Finite proof replay

The author source is pinned in ../../sources/. independent_neighbours.py uses
integer polygon geometry without importing the author's halo, contact-search,
or connectivity algorithms. It finds all 58 grid-aligned touching placements
without interior overlap. Four enclose a hole; check_holes.py independently
reconstructs the complement cell graph and finds exactly one empty kite in
each hole. An eight-kite hat cannot fill it. The remaining 54 placements agree
exactly with the author's legal-neighbour list.

The source surround.py was run to completion: 2,380 two-coronas, of which 188
extend to a third corona. check_recognition.py compares canonical patch sets
with the supplied 188, replays the full author matcher with asserted results,
and separately implements the classification and matching tables with tuple
arithmetic. It checks 1,391 local role assignments, 516 between-cluster
conditions, all within-cluster obligations, and rotated/reflected frame tests.
All checks PASS. The enumeration's search/completeness argument is an imported
part of Section 4; a source replay is not an independent proof of every pruning
rule. The separate hole test only certifies the four two-tile exclusions.

## Why the local output descends

Each tile's label is determined by presence of specified relative neighbours,
with the priority order of Figure 4.2. H roles assemble into four-hat clusters;
T is a single hat; P and F are two-hat clusters. P and F have the **same physical
two-hat shape**, but their surrounding context distinguishes their roles.
Labels are outputs of geometric recognition, not extra rules imposed on the
bare tiler. Relative-coordinate definitions commute with global isometries.

Local consistency has three parts: every tile gets a role; the roles partition
tiles into compatible clusters; intercluster boundaries obey the next-level
rules. Theorem 4.1 supplies this universal conclusion. The 188 locally extendable
patches are a conservative cover; they need not all occur in a whole-plane
tiling. Their excess is harmless because every case passes the same checks.

## Essential imported bridges

Smith–Myers–Kaplan–Goodman-Strauss, *An aperiodic monotile*, v3 (2024),
https://arxiv.org/html/2303.10798v3:

- Lemma A.6: every bare hat tiling, with unrestricted rigid placements, aligns
  to an underlying [3.4.6.4] Laves grid. This is stronger than existence of some
  aligned tiling. It closes the continuous-placement gap in a grid search.
- Theorem 4.1 and its finite-case completeness: every such tiling clusters as
  H/T/P/F, with the matching rules and the same symmetries.

The alignment proof uses the absence of infinite straight boundary rays and
excludes bounded convex aligned components by their possible corners. The
actual hat angles are 90,120,120,270,120,90,120,270,120,90,240,90,240 degrees
when geometry.json's boundary starts at (-1,-1). Four corners are reflex;
seven other corners touch a reflex corner; the last two cut off unfillable
regions as in Figure A.10. This is a read and imported geometric proof, not
a claim that the Python search covers arbitrary continuous placements unaided.

R003 establishes the base readout using those established imports. R004–R005
handle the all-scale endpoint and concrete geometric growth. Infinite existence
and universal recursive closure must still be supplied in the final assembly.
