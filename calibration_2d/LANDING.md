# 2D calibration landing: the known hat, with explicit proof dependencies

2026-09-06. The controlled reconstruction reaches the charter's 2D target.
This is **not an independent discovery of a new Einstein**. The hat and its
recognition/construction grammar are due to Smith, Myers, Kaplan and
Goodman-Strauss. Their published geometric theorems are established imports;
the exact local replay, growth derivation, controls and SBT adapters are the
local calibration work. The 3D monotile problem remains open in this repository.

## Explicit returned object and exact target

Let P be the closed polygon with consecutive vertices

    (0,0),(-1,-1),(0,-2),(2,-2),(2,-1),(4,-2),(5,-1),
    (4,0),(3,0),(2,2),(0,3),(0,2),(-1,2),

where (x,y) denotes the Euclidean point (x+y/2, sqrt(3)y/2). It is the closure
of its nonempty interior, a connected compact topological disk of area 8sqrt(3).
Copies may be translated, rotated or reflected. No colour, label, marked edge
or additional matching restriction is part of P.

**Conclusion.** P tiles the whole Euclidean plane. For every tiling T by
congruent copies of P and every vector v, T+v=T implies v=0.

## Proof, with the bridges visible

1. **Bare geometry.** The eight-kite union and its simple 13-vertex boundary
   are reconstructed and exactly checked in R003. This proves the stated
   connected, unmarked shape properties directly.

2. **Nonempty tiling space.** Import Theorem 2.1 of the hat paper, with the
   Section 2/5 construction: compatible growing patches of these very hats
   extend to a full-plane tiling. The hypotheses refer to P above. R005
   implements the construction with exact coordinates and checks finite
   physical patches through 7,921 hats. These finite patches corroborate the
   construction; the infinite extension uses the published compatibility and
   existence proof, not an extrapolation from five samples.

3. **All placements reach the finite geometric domain.** Import Lemma A.6:
   every tiling by the bare hat aligns to one underlying Laves grid, after a
   global Euclidean change of frame. In particular this covers reflected copies
   and arbitrary initially allowed placement angles, not just grid-generated
   tilings. This implication has the universal quantifier needed here.

4. **Geometry determines legal contextual structure.** Import Theorem 4.1:
   every hat tiling clusters into H/T/P/F macrotiles with the stated edge rules
   and preserved symmetries. R003 regenerates the author's complete finite
   atlas and independently replays its local arithmetic and rule tables.
   The proof's enumeration completeness and alignment reduction remain source
   imports. The labels are recovered from the tiling; they are not constraints
   added to the target. A reflected global frame is handled by reflection.

5. **Coarsening can continue indefinitely.** Import Theorem 5.1 for tilings
   obeying those derived macro rules. It supplies symmetry-preserving grouping
   into larger combinatorially equivalent supertiles. Its proof checks both
   edge matching and the vertex-angle sum, so the same argument repeats at
   every level. Its final geometric argument supplies inballs with radii
   tending to infinity. Alternative straight outlines used in the visualization
   require the paper's boundary correspondence; they are not silently equated
   with its bisected decorated polygons. R005 additionally derives the bound
   (13/5)^n/100 in that straight-outline realization.

6. **Return to the bare target.** Suppose T+v=T with v nonzero. Symmetry
   preservation in steps 4–5 carries this same period into each coarse tiling.
   At any level, take a bounded coarse tile Q containing an open ball of radius
   r_n. Q+v is a different coarse tile: a nonempty bounded set cannot equal
   its nonzero translate. Their disjoint interiors imply |v| >= 2r_n.
   Since r_n is unbounded this is impossible. This is R004's derived SBT tower
   endpoint. Together with step 2 it proves the nonvacuous target. QED.

The argument uses ordinary established geometric imports. No new closure axiom
is needed, and no unresolved geometric recognition input is being supplied by
an unnamed closure premise.

## What has and has not been mechanized

| Component | Evidence |
| --- | --- |
| Chair control and frozen-map certificate | Exact search plus separate certificate verifiers |
| Hat shape and grid contacts | Exact integer/rational reconstruction; separate contact enumeration and small-hole check |
| Base local rules | Full author enumeration replay; exact match of 188-patch sets; separate rule-table arithmetic |
| Large physical patches | Exact rational port with congruence, common grid, nonoverlap and covered-disk checks |
| Straight macroshape growth | Symbolic family closure; exact recurrence; rational Bernstein positivity certificates over a full interval |
| Period transport endpoint | Written geometric proof; abstract dependent-level theorem checked in Lean 4.28 |
| Alignment, atlas completeness, all-level recognition, infinite compatibility | Read and explicitly imported published proofs, not locally Lean-formalized |
| Finite-ambiguity extension | Written proof and periodic/dimensional controls in R006; not required for the hat landing |

The Lean result is a substantive abstract implication over supplied spacing and
coarsening hypotheses. It is **not** a Lean proof of the complete hat theorem.
Review was a distinct mathematical self-review, not an independent referee.
See SELF_REVIEW.md and the replay receipt for the exact coverage and corrections.

## Source and reusable output

Primary mathematical source: Smith, Myers, Kaplan and Goodman-Strauss,
[*An aperiodic monotile*, v3](https://arxiv.org/html/2303.10798v3), Sections 2,
4 and 5, Lemma A.6. Pinned code: [hatviz](https://github.com/isohedral/hatviz),
commit 4bb9d01999e4e84accc2a78d0fa279ef20b47263; source checksums in sources/.
The source proof was read in full for these bridges. sources/hat_paper.lines
is only an earlier truncated Paperclip overview; use sources/hat_v3.txt or PDF
for the full paper.

Read LESSONS_FOR_3D.md for the construction consequences. The successful 2D
return depends on actual geometric recognition and existence. The SBT framework
helps identify, repair and compose those obligations; it does not supply a
missing 3D solid merely from the desired anti-periodicity endpoint.
