# THEOREM.md — statement, dependency graph, trust tiers

Sources: `proof/PROOFS_registered.md` (packet 5, cited as R§n) and
`proof/ALIGNMENT_PROOF.md` (packet 6, cited as A§n). Where both treat the same
step, A supersedes R (it was written to close R's alignment sketch).

## Statement

The solid is publicly nicknamed **Chair44 (R44)**. The mathematical development
retains **R44** as its project identifier and Q as the solid's formal symbol.

Let Q be the solid in `solid/r44_solid.json` (sha256 f320d7a0…). Then

1. Ω(Q) ≠ ∅: there is a tiling of R³ by isometric copies of Q.
2. For every tiling T ∈ Ω(Q): Per(T) = {0} and |Sym(T)| ≤ 24.

Isometries include reflections. No face-to-face, lattice, common-orientation
or connected-contact-graph hypothesis is imposed.

Tiers: T1 = Lean, kernel `decide`, standard axioms only. T1n = Lean `native_decide`
(kernel-checked modulo the per-theorem compiler trust hook Lean generates for it;
listed in `lean/R44/AXIOMS.md`). T2 = finite computation replayed by
`verify/replay.py` (Python stdlib, two independent implementations for the
companion census). T3 = written proof. Lean phase 1 (`lean/R44/`, packet L1)
moved every T2 row below to T1 or T1n; the Python replay remains as a second
implementation.

## Object (R§1, A§1)

| Item | Tier |
|---|---|
| P = seven-cube chair; 8 child poses partition 2P as integer cell sets | T1 `children_partition_2P` |
| The generated child poses induce a total constant-length lattice substitution on 24×7 = 168 registered cell labels; its 168×168 matrix has column sum 8 and least positive power N = 3; its least modular-coincidence depth is M = 3, at a = (0,0,2) with label i = 78 | T1n `substitution_modular_coincidence` (+ independent T2 `verify/substitution_modular_coincidence.py`) |
| Exact closure of the legal 2×2×2 label-block language has sizes 168 → 600 → 1,278 → 1,398 → 1,410 and is then stable; exactly 27 fixed seeds form proper-frame orbits of sizes 24 and 3, with origin-stabilizer histogram {1 ↦ 24, 8 ↦ 3}; every seed reproduces in place and the substitution commutes with all 24 proper frames | T1n `seed_language_closure` (+ independent T2 `verify/seed_language_closure.py`) |
| Lee–Moody 2001 Thm 3 (iv)⇒(ii) and Schlottmann: a primitive lattice substitution with a modular coincidence has regular model sets as its fixed point's label classes (2-adic internal space), hence pure point diffraction; limit-periodic | T3 cited import |
| 24 panels × 8 marker centres in (1/8)Z³; profile from 372 sign equations, 12 balanced components | T1n `contact_closure_30`, `profile_canonical` |
| Mesh matches construction triangle-by-triangle; volume 7; 6,408 edges classified | T1n `solid_mesh_exact`, `mesh_angle_audit` |
| Boundary mesh is a closed connected triangulated surface, every vertex link is one circle, and χ = 2 from V/E/F = 2,138/6,408/4,272 | T1n `boundary_sphere` (+ independent T2 `verify/boundary_sphere.py`) |
| Q is a closed topological 3-ball | T3: classification of closed surfaces plus PL Schoenflies/Alexander (Moise; Rourke–Sanderson); independently, the tube homeomorphism from P |
| Each native tube map is a homeomorphism; the 192 maps glue; the glued ambient homeomorphism carries P exactly to Q | T1n `per_tube_homeomorphisms_holds`, `feature_tube_maps_glue_holds`, `feature_tube_map_carries_carrier_holds` (exchange 3; native profile hook only) |

## Part A — every tiling is grid-registered (A§2–6)

```
A-L2.1 local finiteness ............................ T1 `local_finiteness` (from H1)
A-L2.2 cone / sector budgets ....................... T1n `cone_sector_budgets_holds`
A-L3.1 complete dihedral list, 24 deviations distinct
        (10000 i² = 20000 j² + j⁴ unsolvable) ...... T1n `complete_dihedral_list_holds`
        (arithmetic part T1 `deviations_distinct`; named R8/R10 finite hooks)
A-L3.2 generic feature-edge point has exactly one
        complementary feature partner .............. T1n `generic_feature_partner_holds`
                                                        ← needs L2.2, L3.1
A-L4.1 circular-cone formula at L = 3/25 ........... T1 `circular_cone_solid_angle_holds`
        concrete feature-chart containment and hence
        solid angle > 4π/3 on the feature graph ..... T1n `feature_circular_cone_containment_holds`
                                                        (native profile hook only)
A-T4.2 one tile accompanies the whole feature graph
        (finite disjoint closed cover, connected) .. T1n `connected_feature_companion_holds`
        using the discharged open circular-cone inclusion ← L2.1, L3.2, L4.1
A-L4.3 containment ⇒ equal features (compactness) .. T1n `feature_containment_rigidity_holds`
        by compact isometric containment f(K) ⊆ K ⇒ f(K) = K ← T4.2, L3.2
A-C4.4 companion pose ∈ signed permutations × (1/8)Z³ T1n
        `companion_pose_discrete_holds`; fixed record metadata is the named
        R8 certificate `mate_records_roles_nonempty` ← L4.3
A-L5.1 eighth-grid baseline overlap ⇒ core overlap
        (box side ≥ 21/200) ........................ T1 `retained_core_overlap_holds`
A-FS5.2 6,862 mates → 5,317 isolated → 44 survivors;
        299,975 companion collisions ............... T1n `mates_census` (+ two Python implementations)
A-L5.3 only the 44 registered mates occur ........... T1 `only_registered_mates_holds`
        ← T4.2, L4.3, 5.1, 5.2
A-L6.1 a feature component's baseline cells = Z³ .... T1n `baseline_component_covers_grid_holds`
                                                        ← L5.3
A-L6.2 the component's physical tiles cover R³ ...... T1 `component_solids_cover_holds`
        ← L6.1 + the carried interior ball
A-T6.3 unrestricted alignment ....................... T1n `unrestricted_alignment_holds`
                                                        ← L6.2
```

The physical-coverage proof clamps each carrier point to an interior point
with squared distance at most `3/2500 < 1/100`, uses the carried `1/4`-ball,
and invokes packing disjointness. This is an alternative to assembly-wide tube
gluing. It presupposes an existing tiling and is not used to prove existence.

## Part B — the registered theorem (R§6–10)

```
R§6  2,388 shell poses → 44 legal contacts; 19 rotations generate the
     24-element proper cubic group ......................... T1n `atlas_44`, `orientation_group_24`
     Q has no self-isometry: finite comparison over all 48 signed
     permutations T1 `no_native_symmetry`; carrier-preserving motion to
     feature-table frame T1n `carrier_feature_frame_reduction_holds`;
     carrier recovery T1 `planar_area_carrier_recovery_holds` (ERRATA E5),
     discharged by the alternative diameter-endpoint proof of the unchanged
     proposition in `proof/external_lean/F2_exchange3/`, not by the written
     planar-area calculation
R§6/C2 every tiling is homochiral: all placement linear parts have the same
     determinant; hence the tiling is wholly in the +1 or -1 sector and a
     reflected/unreflected pair cannot co-occur ................ T1 spine
     `tiling_homochiral`, `tiling_chirality_corollary`, using the discharged
     endpoint theorems consumed by `registration_of_tiling`
R§7  33 first shells; 14 completable / 18 impossible outer roots;
     28 parent conflicts → unique parent (T7.1) .............. T1n censuses; local-to-global
     PROVED in Lean (`registered_first_shells`, `certified_shells_complete_parents`,
     `complete_parent_conflicts`, `parent_local_to_global`) from the alignment fields
R§8  697 → 116 → 44 parent contacts, all even; halved = fine atlas;
     admissibility-preserving coarsening D (T8.1) ............ T1n `parent_atlas_eq_fine`; admissibility,
     common parity, the halved baseline tiling, and the small-collar realization
     (`small_collar_realization_holds`) are PROVED in Lean
R§8–9/C3 every tiling has one literal carrier hierarchy: at level n each
     registered cell is assigned to a registered pose of a 2^n-scaled chair;
     level 0 is the carrier tiling, and intrinsically each level-(n+1) fiber is
     exactly the union of its eight geometric child-pose fibers .... T1 spine
     `carrier_hierarchy_exists`, `carrier_hierarchy_unique`, `carrier_hierarchy`;
     `GeometricHierarchy` removes the `LevelSupertilePose.mem` constraint, and
     `geometric_hierarchy_canonical`, `geometric_hierarchy_unique`,
     `carrierHierarchy_geometric` formalize the levelwise T7.1 induction for
     arbitrary registered geometrically nested partitions; all endpoint
     dependencies are discharged; no exhaustion-from-a-fixed-cell or
     local-derivability claim
R§9  same-frame grandchild (I,(2,2,2)); nested patches A_n exhaust R³ T1n controls; the all-n
     induction, exhaustion, cell disjointness, contact language and baseline assembly PROVED
     in Lean; realization uses the proved small-collar step
R§10 period halving p/2ⁿ ∈ Z³ ⇒ p = 0; |Sym| ≤ 24 ........... T1n `r44_einstein`
                                                               ← T6.3, T7.1, T8.1, R§6
```

The assembly-collar proof identifies duplicate tube sites by their centre,
proves the corresponding conjugated maps agree, and establishes the membership
equivalence for every tile, including unrelated tiles. Its support separation
is `21/200 > 1/16`.

## What would break what

- A failure in A-L3.2 / A-T4.2 / A-L4.3 restricts the theorem to registered
  tilings (Part B stands as a theorem about grid-registered placements).
- A failure in A-L6.1 / A-L6.2 leaves companion rigidity but loses global
  registration; same restriction.
- A failure in any finite item is a checker or certificate bug and is caught by
  `lake build` in `lean/R44` and by `verify/replay.py`; the negative controls
  on both sides show the checks are load-bearing.
- Part B's finite items are the same data as A-FS5.2's survivor set; the
  alignment proof checks set equality, not cardinality.

## Parameter family (R§11)

Heights c_j/10000 with distinct nonzero |c_j|, 1+t_i² ≠ (1+t_j²)², t_j < 1,
(1+t_j²)² < 2, 63·max t_j² < 1: the proof is unchanged. Open 12-parameter
family inside this architecture; not stability under arbitrary perturbation.

## Lean spine (phase 2, packet L2)

`lean/R44/R44/LogicalSpine.lean` defines Q concretely from the canonical panel
data, tilings of ℝ³ by affine-isometric copies (reflections allowed; local
finiteness NOT assumed), Per, Sym, registration, geometric parent partitions,
handedness as the basis-independent determinant of a placement's linear part,
and a coarsening derived from the unique partition. Theorem `tiling_homochiral`
and its paper-facing `tiling_chirality_corollary` are kernel-checked from
`registration_of_tiling`: after one common ambient isometry all placements are
among the literal 24 proper frames, whose determinants are checked directly.
Theorem `carrier_hierarchy` is likewise kernel-checked:
it iterates the proved coarsening, exposes each level as a concrete
cell-to-supertile-pose function, and proves the intrinsic eight-child fiber
union. `CarrierHierarchy` is canonical at the type level because
`LevelSupertilePose.mem` places its values in `D^n(T)`. The separate raw-pose
structure `GeometricHierarchy` has no such constraint;
`geometric_hierarchy_canonical` proves the missing membership by induction from
T7.1, and `geometric_hierarchy_unique` then proves any two raw geometric
hierarchies equal. Uniqueness is not encoded as a canonical recurrence field.
It does not assert fixed-cell exhaustion or local derivability. Target C3(c), the finite modular-coincidence check and its
T3 Lee--Moody/Schlottmann import, is now `substitution_modular_coincidence`:
the generated 168-label substitution is total, has constant column sum eight,
least primitive exponent three, and least modular-coincidence depth three.
Theorem `r44_einstein` is unconditional and kernel-checked modulo the named
compiler hooks: Lean proves Nonempty (Tiling Q),
Per T = {0} and |Sym T| ≤ 24 for every T. Proved outright in Lean: the
period-halving tower, the Archimedean no-period argument, the 24-frame
symmetry injection, local finiteness (A-L2.1), compactness / regular
closure / nonempty interior of Q from one ambient-homeomorphism premise, and
native asymmetry from the planar-area reduction plus the 48-frame finite
fact, the strict cone ⊆ hypograph tangent cone and Ω(L) > 4π/3 ⟺ 8L² < 1,
pairwise disjointness of the 192 feature tubes and the boundary identity of
the tube map. C3(c) and P1 add two finite theorems, so the phase-1
finite-theorem count is now 23. Axioms: standard plus the named native hooks
listed in `lean/R44/AXIOMS.md`. `R44.Hypotheses` is empty; the historical
conditional form remains available as `r44_einstein_of_hypotheses`. No
separate set-equality theorem between the defined Q and the exported mesh is
asserted or needed by the spine.

## Review status

Authors' ledger: `proof/CLAIM_LEDGER_alignment.md`. Adversarial review
targets: `proof/REVIEW_PROMPT.md`. Reviews: `proof/review/` — round 1
(2026-09-06): two independent cross-family reviewers (codex, grok), both
HOLDS-AS-STATED, minor exposition items in `proof/ERRATA.md`. External
adversarial review (independent agent, `proof/review/external_2026-09-08*/`): round 1 FAILS
(inconsistent Lean hypothesis record, repaired as L5X), round 2 HOLDS-AS-STATED with one minor
documentation item; the reviewer could not run Lean, so the formal spine's build and axiom line
rest on the authors' gate record. Proof submission status: kernel-checked
modulo the named compiler hooks; written proofs remain as exposition.
