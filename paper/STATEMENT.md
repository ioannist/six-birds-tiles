# STATEMENT.md — what the paper will state, verbatim, with its evidence

WRITING_PLAN.md step 3. Every sentence here is either a quotation with its source line, a
theorem statement tied to a Lean name or a written-proof label with its tier, or an explicit
non-claim. Tiers: T1 kernel-checked Lean proof using only standard axioms;
T1n kernel-checked Lean proof with recorded native compiler hooks
(`lean/R44/AXIOMS.md`); T2 finite computation replayed in Python; T3 written proof. The
hypothesis count and the tiers below are synced to the commit d90313a717 (2026-09-10; `Hypotheses` empty, `r44_einstein` unconditional; re-pinned once from dd2735d9bd per DECISIONS.md Q-K). Lean results are cited by declaration name (line numbers change between syncs).

## 1. The opening quotations (ledger rows Q1, Q2)

Socolar and Taylor, *Forcing nonperiodicity with a single tile*, Math. Intelligencer 34 (2012),
`1009.1419 L88`:

> "It is still interesting, however, to search for a single, simply connected 2D or 3D
> prototile that forces maximal nonperiodicity by shape alone, or one that does not permit any
> weakly nonperiodic tilings."

Kaplan, *The path to aperiodic monotiles*, Eureka 67 (2025), `2509.12216 L246–L254`:

> "A shape called the Schmitt-Conway-Danzer biprism is both an existence proof and a cautionary
> tale about the definition of aperiodicity in 3D space. It tiles space without ever permitting
> translational symmetries, but it admits tilings that contain a "screw motion" (a rotation
> about a axis composed with a translation parallel to that axis), which can be repeated any
> number of times. Some people regard this screw motion as uncomfortably close to translation,
> and demand a strongly aperiodic 3D monotile, one that admits tilings whose symmetries never
> include an infinite cyclic subgroup of any kind. Many of the ideas and algorithms we used to
> prove the hat's aperiodicity could be adapted to work in 3D space, but personally I am
> daunted by the prospect of deducing the behaviour of any candidate shapes that might be
> discovered there."

The paper's first paragraph quotes the Socolar–Taylor sentence and the two Kaplan sentences
beginning "Some people regard" and "Many of the ideas", then states Theorem 1.1.

## 2. The headline theorems

**Theorem 1.1** (hat form, `2303.10798 L43` pattern). *The solid Q of Figure 1.1 is a strongly
aperiodic monotile of R³: Q admits tilings of R³ by congruent copies, and no such tiling has a
symmetry of infinite order.*

**Theorem 1.2** (Spectre form, `2305.17743 L45` pattern; the statement of THEOREM.md). *Let Q be
the rational polyhedral solid of `solid/r44_solid.json`. Then (1) there is a tiling of R³ by
isometric copies of Q; (2) for every tiling T by isometric copies of Q, Per(T) = {0} and
|Sym(T)| ≤ 24; (3) every tiling T is homochiral; (4) in every tiling T each tile lies in a
unique infinite hierarchy of 2ⁿ-scaled chair supertiles in registered poses, nested through the
eight child poses. Isometries include reflections. No face-to-face, lattice, common-orientation,
connected-contact-graph or local-finiteness hypothesis is imposed.*

Evidence and tier, clause by clause:

| Clause | Evidence | Tier |
|---|---|---|
| (1) existence | `r44_einstein`, first conjunct `Nonempty (Tiling Q)` (`R44/LogicalSpine.lean`); existence comes from the substitution and the small-collar realization (R§8–9, ERRATA E2, E6) | T1n, unconditional (`existence`) |
| (2) Per(T) = {0}, \|Sym(T)\| ≤ 24 | `r44_einstein`, second conjunct: `∀ T : Tiling Q, Per T = {0} ∧ (Set.univ : Set (Sym T)).encard ≤ 24` | T1n, unconditional (`r44_einstein`); the terminal arithmetic lemma `no_period` and conditional symmetry-bound lemma `sym_card_le_24` are T1 |
| strongly aperiodic (Mozes / hat sense) | from (2): a finite symmetry group has no element of infinite order; the hat's definitions `2303.10798 L64` | derived; the implication "finite ⇒ no infinite-order element" is trivial and is stated |
| (3) homochiral | `tiling_homochiral (H) (T) : ∀ g h ∈ T.placements, handedness g = handedness h`; `tiling_chirality_corollary`: all +1 or all −1, and no mixed pair | T1n, unconditional |
| (4) unique hierarchy | `carrier_hierarchy (H) (T)`: level 0 = the registered carrier tiling; every level-n pose registered; `CarrierHierarchyNested`; `∀ K K' : CarrierHierarchy H T, K = K'` (`carrier_hierarchy_unique`) | T1n, unconditional; uniqueness among arbitrary geometrically nested registered families is `geometric_hierarchy_unique` via `geometric_hierarchy_canonical` (ledger M9 closed); NO exhaustion clause (non-exhausting hierarchies occur, ledger L10) |
| "isometries include reflections" | `Tiling Q` is over `RigidMotion` with `handedness` ±1 | definition |
| "no local finiteness assumed" | `local_finiteness (h : CompactRegularClosedBall Q) : EveryPackingLocallyFinite Q` (`R44/LogicalSpineFoundation.lean`), A-L2.1 | T1 |

The record `Hypotheses` is EMPTY at the pinned commit; its 16 former fields at dd2735d9bd were: `per_tube_homeomorphisms`, `feature_tube_maps_glue`, `feature_tube_map_carries_carrier`, `cone_sector_budgets`, `complete_dihedral_list`, `generic_feature_partner`, `feature_circular_cone_containment`, `connected_feature_companion`, `feature_containment_rigidity`, `companion_pose_discrete`, `only_registered_mates`, `baseline_component_covers_grid`, `component_solids_cover`, `unrestricted_alignment`, `planar_area_carrier_recovery`, `small_collar_realization`. Each quotes one written lemma (A§1, A-L2.2, A-L3.1, A-L3.2, A-L4.1, A-T4.2, A-L4.3, A-C4.4, A-L5.3, A-L6.1, A-L6.2, A-T6.3, R§6/E5, R§8–9/E2/E6). All 19 written lemmas (these 16 and the three discharged before dd2735d9bd) are theorems in `lean/R44/R44/Proved/` at the pin (ledger T12, Table 5). The honest sentence: the finite checks, the nineteen former hypothesis statements, and the logical assembly of the four tiling clauses are Lean theorems, kernel-checked modulo the named compiler hooks. Appendix C records the empty hypothesis structure and the dependencies; the written proofs remain as exposition.

## 3. Definitions block (sources in COMMUNITY_PAPER_PROFILE.md §4)

- Tile, tiling, admits, monohedral, locally finite: Grünbaum–Shephard as in the hat's §1.3
  (`2303.10798 L57–L58`), with "closed topological disk" replaced by "closed topological 3-ball".
- Symmetry group; weakly / strongly periodic; weakly / strongly aperiodic: verbatim from
  `2303.10798 L64`: "The symmetry group of a tiling is the group of those isometries that act
  as a permutation on the tiles of the tiling. A tiling is weakly periodic if its symmetry
  group has an element of infinite order … A tiling is strongly periodic if the symmetry group
  has a discrete subgroup with cocompact action on the space tiled … A set of tiles (or a
  single tile) is weakly aperiodic if it admits a tiling but does not admit a strongly periodic
  tiling, and strongly aperiodic if it admits a tiling but does not admit a weakly periodic
  tiling." And `L34`: "Following Mozes [Moz97], we say a set of tiles is strongly aperiodic if
  it admits tilings but none with any infinite cyclic symmetry."
- The disambiguation sentence (mandatory, §1 and terminology): "In the finer taxonomy of
  Coulbois, Gajardo, Guillon and Lutfalla [CGGL24, §2.1] a tile all of whose tilings have finite
  symmetry group is *mildly* aperiodic, and *strongly* aperiodic is reserved for trivial
  stabilizers; in their terms Q is mildly aperiodic but not strongly aperiodic: Proposition 8.2
  supplies a tiling whose symmetry group has order 8." Source `2409.15880 L43–L45, L234`.
- Monotile, einstein: restate the hat's `L25` for closed 3-balls: a closed topological 3-ball
  that tiles R³ aperiodically purely by virtue of its geometry, with no matching rules.
- Homochiral tiling; strictly chiral aperiodic monotile: verbatim `2305.17743 L22`; then: "By
  this definition Q is a strictly chiral aperiodic monotile of R³: reflections are permitted,
  and every tiling admitted by Q is homochiral and non-periodic."
- Hierarchical, unique hierarchy: verbatim `2305.17743 L43`; supertile of level n: a 2ⁿ-scaled
  chair in a registered pose.
- Fault line: `2303.10798 L253`.
- Registered, registration, the 44-contact atlas, features, panels, carrier: our own, defined
  in §2–§3 of the paper from `solid/r44_solid.json` and `certificates/`.

## 4. The object (ledger rows O1–O9)

Q: the seven-cube chair carrier P (2×2×2 minus one corner), 24 exposed unit panels, eight
square-pyramid features per panel of height ±j/10000 (j = 1..12) and base half-width 1/100;
rational coordinates; volume 7; 2,138 vertices, 6,408 edges, 4,272 triangles. Evidence:
`solid/r44_solid.json` (sha256 f320d7a0…), `solid_mesh_exact`, `mesh_angle_audit` (T1n),
`boundary_sphere` (T1n, `R44/Theorems.lean`). No self-isometry, a three-component boundary at the pinned commit: an arbitrary self-isometry of Q preserves the carrier P by `planar_area_carrier_recovery_holds` (T1; formal proof by diameter endpoints, the planar-area argument is the written proof, ERRATA E5); a carrier-preserving motion is reduced to a feature-table frame by `carrier_feature_frame_reduction_holds` (T1n: hooks `profile_canonical`, `transported_role_geometry`); among the 48 signed frames only the identity preserves the feature table, `no_native_symmetry` (T1). The assembled statement is `native_asymmetry_reduction`; the whole is T1n at the pin.

Closed 3-ball: `boundary_sphere` gives every edge in two triangles, connected triangle graph,
single-cycle vertex links, V − E + F = 2 (T1n) and `verify/boundary_sphere.py` (T2). Two
imports at T3, stated exactly: (i) classification of closed surfaces: a connected closed
triangulated surface with Euler characteristic 2 is homeomorphic to S² (orientable genus g has
χ = 2 − 2g, non-orientable with k crosscaps has χ = 2 − k, so χ = 2 forces the sphere)
[Moise, GTM 47, the classification chapter; locator to be verified, BIB_UNVERIFIED]; (ii) PL
Schoenflies in dimension 3 (Alexander): a polyhedral 2-sphere in R³ bounds a PL 3-ball, i.e. the
closure of its bounded complementary domain is a PL 3-ball [Moise, GTM 47, the PL Schoenflies
chapter; Rourke–Sanderson; locators to be verified]. The mesh is a polyhedral surface embedded
in R³ by its rational vertex coordinates, and Q is the closure of the bounded domain it bounds.

Tube construction (A§1): `per_tube_homeomorphisms_holds`, `feature_tube_maps_glue_holds`, `feature_tube_map_carries_carrier_holds` (T1n at the pinned commit; disjointness of the 192 tube supports and the boundary identity are Lean theorems, T1); A-L4.1's geometric half is `feature_circular_cone_containment_holds` (T1n), its arithmetic half `circular_cone_solid_angle_holds` (T1).

## 5. The limit-periodic corollary (ledger rows L1–L6; wording per DECISIONS.md Q-A)

Finite fact: `substitution_modular_coincidence` (T1n, `R44/Theorems.lean`): the 168-label
lattice substitution (labels = registered frame × cell of the chair; inflation 2 on Z³) is
total, its 168×168 matrix has constant column sum 8, least primitive exponent N = 3, least
modular-coincidence depth M = 3 with witness a = (0,0,2) and label i = 78; replayed by
`verify/substitution_modular_coincidence.py` (T2). Fixed point: a legal two-sided fixed point exists, determined by a 2×2×2 seed block around the origin whose eight labels are each fixed by their residue map; 24 such legal blocks occur inside level-3 patches (`paper/scripts/seed_fixed_point.py`, T2; DECISIONS Q-B).
Import (T3, cited): Lee–Moody 2001 Theorem 3, (iv) ⇒ (ii), with its hypotheses stated
(primitive; PF eigenvalue 8 = |det 2I|; the label classes of a fixed point partition Z³);
Schlottmann's theorem via Lee–Moody–Solomyak 2003 Theorem 5.11/5.12; the term "limit-periodic"
from Baake–Moody–Schlottmann 1998 and Baake–Grimm 2010. Level of the statement: fixed point
(Q-A OPEN). N = 3 and M = 3 are independent integers.

## 6. Explicit non-claims (ledger rows N1–N8)

1. Not claimed: that every tiling by Q lies in the substitution hull (fault lines; hat `L253`).
2. Not claimed: local derivability of the hierarchy from the unlabelled chair tiling (R7).
3. Tilings with symmetry groups of orders 1 and 8 exist (Proposition 8.2, ledger L9); attainment of the bound 24 and the remaining possible symmetry groups are open (Q-C).
4. Not claimed: minimality in faces, vertices or features. Q is not convex (witness: the mesh vertices (2,2,1) and (2,1,2) lie in Q and their midpoint (2,3/2,3/2) does not, exact ray-parity test with controls, `paper/scripts/nonconvex_witness.py`, T2; ledger O10); no convexity claim of any kind is made.
5. Not claimed: decidability results.
6. Not claimed: stability of the theorem under arbitrary perturbation; only the 12-parameter
   family of R§11 with the proof unchanged.
7. Not claimed: a second, computer-free proof.
8. Not claimed: mathlib coverage; the Lean development is ours, the comparator is Myers's
   in-progress staging repository.

Public qualifier: "proof submission" (README wording); at the pin every written lemma is formalized, the theorem is kernel-checked modulo the 21 named hooks, and the third external review round is pending.
