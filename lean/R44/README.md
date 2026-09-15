# R44 finite core and logical spine in Lean 4

This project contains the completed phases 1–3 of the R44 formalization roadmap. Phase
1 replays the finite R44 core. Phase 2 defines congruent tilings in
`EuclideanSpace ℝ (Fin 3)` and the logical assembly. Phase F has now
discharged every continuous/infinite-space field, so `Hypotheses` is empty
and `r44_einstein` is unconditional. Phase 3a
proves the literal carrier's compactness, regular closure, and nonempty
interior, and reduces the Object field to an ambient tube-gluing
homeomorphism, which Phase F exchange 3 now proves. Phase 3 also proves local
finiteness from that Object interface and factors native asymmetry into
carrier reconstruction and the proved 48-frame comparison; exchange 3 now
proves carrier reconstruction by a diameter-endpoint argument. Phase 3b removes the conclusion-shaped
uniform-solid-angle field: Lean proves the abstract Lipschitz/hypograph cone
inclusion, the exact arithmetic threshold, orthogonal invariance, and
monotonicity; Phase F proves both the cone-volume evaluation and the concrete
feature-chart instantiation. The L4 continuation also factors R§6 at carrier
recovery and advances the Object construction through literal tube-support
disjointness and boundary compatibility; Phase F exchange 3 completes the
tube homeomorphism and carrier recovery.
Phase 3c factors the three registered-hierarchy endpoints into their actual
geometric and all-n sublemmas. Lean now constructs and proves uniqueness of
the parent-pose partition from complete-parent existence and conflicts, uses
one common atlas-baseline realization interface for coarsening and existence,
and defines the entire nested pose union rather than only its first two levels.

The toolchain is `leanprover/lean4:v4.31.0`. Mathlib is pinned at tag
`v4.31.0` (commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`).

## Build and provenance

From this directory:

```sh
scripts/controls.sh
python3 gen/extract.py --check
```

`scripts/controls.sh` is the single Lean-side gate. It first requires
`lake build` to pass; a build failure exits 2 with
`POSITIVE BUILD FAILED; must-fail results are meaningless` and no negative
file is run. It then runs every file under `negative/`, requiring both a
nonzero exit and the exact diagnostic substring declared by that file's
`-- EXPECT:` header, and explicitly compiles the positive
`R44/ScopeRegressions.lean` examples. Missing tools, bad imports, missing
headers, unexpected success, and wrong diagnostics all fail the gate. A final
one-line `CONTROLS: PASS` summary is printed only when every check passes.

## Phase F proofs and Discharge library

All 19 former endpoints and their 48 delivery helpers are promoted to the
core library under `R44/Proved/` (67 files total). `R44/Discharge/` contains
no Lean modules and there are zero executable admissions. The Lean-side
controls enforce those counts and verify the complete delivery diff ledger.
The manager-side `.codex` forbidden-token scan excludes `R44/Discharge/`; the
dedicated discharge audit is the admission gate for this external library.
`lake build` builds the core `R44` library. `scripts/controls.sh` also builds
the historical `R44Discharge` target (now a promoted-root regression target),
checks every integrated source against its latest archived delivery with
`scripts/discharge_diff_audit.sh`, and runs the zero-admission audit.

Compile-fix provenance uses one convention throughout `R44/Proved/` (and the
historical delivery paths formerly under `R44/Discharge/`):
single-line edits carry `-- [compile-fix]` on that line; rewritten blocks of
two or more consecutive lines are enclosed by
`-- [compile-fix begin: <reason>]` and `-- [compile-fix end]`, and every line
inside such a block is understood to be a compile-fix change.

| Core file | Proved theorem or role | Admission status |
|---|---|---|
| `NativeGeometry.lean` | Shared native set/chart geometry | No admission |
| `CarrierSymmetries.lean` | Shared carrier-isometry reduction | No admission |
| `RetainedCoreOverlap.lean` | `retained_core_overlap_holds` | No admission |
| `CarrierFeatureFrameReduction.lean` | `carrier_feature_frame_reduction_holds` | No admission |
| `CircularConeSolidAngle.lean` | `circular_cone_solid_angle_holds` | No admission |
| `TubeCalculus.lean` | Shared scalar tube-map calculus | No admission |
| `PerTubeHomeomorphisms.lean` | `per_tube_homeomorphisms_holds` | No admission |
| `FeatureTubeMapsGlue.lean` | `feature_tube_maps_glue_holds` | No admission |
| `FeatureTubeMapCarriesCarrier.lean` | `feature_tube_map_carries_carrier_holds` | No admission |
| `FeatureLocalCharts.lean` | Shared open native chart geometry | No admission |
| `FeatureCircularConeContainment.lean` | `feature_circular_cone_containment_holds` | No admission |
| `MetricCarrierRecovery.lean` | Shared diameter-endpoint carrier recovery | No admission |
| `PlanarAreaCarrierRecovery.lean` | `planar_area_carrier_recovery_holds` | No admission; alternative diameter-endpoint proof of the unchanged proposition |
| `CompactCongruent.lean` | Shared compact-isometry containment lemma | No admission |
| `FeatureGraphTopology.lean` | Shared feature-graph topology | No admission |
| `PyramidGeometry.lean` | Shared intrinsic pyramid rigidity | No admission; compactness argument replaces the written graph-length step |
| `PolyhedralGerms.lean` | Shared exact polyhedral tangent germs | No admission |
| `ConeSectorBudgets.lean` | `cone_sector_budgets_holds` | No admission |
| `ConnectedFeatureCompanion.lean` | `connected_feature_companion_holds` | No admission; uses the discharged open-cone inclusion |
| `FeatureContainmentRigidity.lean` | `feature_containment_rigidity_holds` | No admission |
| `CubicFrameAlgebra.lean` | Shared real/literal cubic-frame algebra | No admission |
| `NativeMateGeometry.lean` | Shared whole-feature mate geometry | No admission |
| `HashListSemantics.lean` | Shared extensional hash-list semantics | No admission |
| `MateCensusSemantics.lean` | Shared census semantics and named R8 metadata certificate | No admission; one named `native_decide` hook |
| `CompanionPoseDiscrete.lean` | `companion_pose_discrete_holds` | No admission |
| `CompanionCollisionSemantics.lean` | Shared companion-collision semantics | No admission |
| `RetainedBoxGeometry.lean` | Shared retained-box geometry | No admission |
| `CarrierCoreCover.lean` | Shared carrier-core coverage | No admission |
| `OnlyRegisteredMates.lean` | `only_registered_mates_holds` | No admission |
| `ComponentSolidsCover.lean` | `component_solids_cover_holds` | No admission |
| `PanelIncidence.lean` | Shared registered panel incidence | No admission |
| `PairedCollarMaps.lean` | Shared paired collar maps | No admission |
| `AssemblyCollarIncidence.lean` | Shared assembly collar incidence | No admission |
| `AssemblyCollarData.lean` | Admission-free registered assembly collar data | No admission |
| `TubeSiteGeometry.lean` | Shared tube-site geometry | No admission |
| `RegisteredCellGeometry.lean` | Shared registered-cell geometry | No admission |
| `RegisteredComponentGeometry.lean` | Shared registered-component geometry | No admission |
| `SeparatedHomeomorphismGluing.lean` | Shared separated gluing construction | No admission |
| `SmallCollarRealization.lean` | `small_collar_realization_holds` | No admission |

| Exchange-7-promoted core file | Field or role | Trust status |
|---|---|---|
| `NativeDihedralSectors.lean` | `native_oriented_wedge_charts` bridge | No admission; named finite hooks only |
| `CarrierCoordinateStates.lean` | 125-state coordinate classifier | No admission; named R10 hook `carrier_coordinate_states_table` |
| `MeshChartIncidence.lean` | 6,408-edge incidence table | No admission; named R8 hook `native_mesh_incidence_trace` |
| `AngularMeridianCore.lean`, `ElementarySectorGeometry.lean`, `NativeFeatureMeridians.lean`, `OrdinaryMeridians.lean`, `CarrierBoundaryStrata.lean`, `NativeBoundaryLocal.lean`, `CanonicalTentStrata.lean`, `MeshChartInterpretation.lean` | Exchange-7 bridge helpers | No admission |
| `NativeExceptionalVertices.lean` | Finite exceptional-vertex classification | No admission; three named native hooks |
| `NativeBoundaryStrata.lean` | `native_boundary_strata` bridge | No admission; named finite hooks only |
| `CompleteDihedralList.lean` | `complete_dihedral_list_holds` | No admission |
| `GenericFeaturePartner.lean` | `generic_feature_partner_holds` | No admission |
| `BaselineComponentCoversGrid.lean` | `baseline_component_covers_grid_holds` | No admission |
| `UnrestrictedAlignment.lean` | `unrestricted_alignment_holds` | No admission |

The stdlib replay also runs `verify/tube_formula_controls.py`: 4,800 exact
rational cases check both inverse identities, hypograph transport, and the
two incident owners' opposite-normal descriptions of the native tube formula.
The check is wired into `python3 verify/replay.py`; it is a finite formula
control and does not replace the continuous inverse/gluing proof.

The checked-in `lake-manifest.json` has the same package revisions as
`gen/mathlib_lake-manifest.reference.json`. The intended offline checkout has
those packages already present and built under `.lake/packages`; the measured
build below neither downloaded packages nor rebuilt Mathlib.

Lake 5.0 (shipped with Lean 4.31) no longer accepts a Lake-level `-j` option.
The root package therefore sets `moreLeanArgs := #["-j", "4"]`; every generated
R44 module trace records `Module.leanArgs: #[-j, 4]`. Thus the documented
`lake build` command applies the required four-thread cap to every Lean
compiler process.

`lake build` also elaborates `R44/Axioms.lean`, whose metaprogram writes the
same dependency lists as its `#print axioms` commands to `build_axioms.log`.
The measured capped-build time is recorded below.

`gen/extract.py` reads only these canonical inputs:

- `../../solid/native_panels.csv`
- `../../solid/r44_solid.json`
- `../../certificates/candidate_certificate.json`
- `../../certificates/companion_collision_certificate.json`

It writes `R44/Generated/CoreData.lean` and
`R44/Generated/MateData.lean`.  Large tables are compact comma-separated
numeric string literals, decoded by total Lean functions; smaller tables are
constructor literals.  No file is read at theorem-evaluation time.
`gen/GENERATED.sha256` records every canonical input hash and both generated
Lean-source hashes.  `python3 gen/extract.py --check` regenerates in memory and
fails if any literal source or receipt differs.

## Checked theorems

`R44/Theorems.lean` exports exactly **23** top-level finite theorems; the
table below lists all 23.

| Lean theorem | Decision method | Exact correspondence in `THEOREM.md` |
|---|---|---|
| `children_partition_2P` | `decide` | Object: eight child poses partition `2P`, all proper |
| `contact_closure_30` | `native_decide` | Object/R§1.2: refinement closure 21 → 30 → fixed |
| `profile_canonical` | `native_decide` | Object/R§1.2: 372 distinct derived equations, twelve balanced components ordered and positively rooted by least role, canonical 192-profile |
| `atlas_44` | `native_decide` | R§6: 2,388 shell poses → exact 44-contact atlas |
| `first_shells_33` | `native_decide` | R§7 finite first-shell lemma, including all 44 recomputed whole-body conflict masks |
| `central_completion` | `native_decide` | R§7 central-completion lemma (14/18, no wrong centre) |
| `parent_conflicts_28` | `native_decide` | R§7: all 28 parent pairs through a root conflict |
| `parent_atlas_eq_fine` | `native_decide` | R§8: 697 → 116 → 44, even and halved atlas equality |
| `mates_census` | `native_decide` | A-FS5.2 and finite boxes in A-L5.1: 6,862 → 5,317 → 44; 5,273 universal witnesses/299,975 options; retained sides at least 21/200 |
| `deviations_distinct` | `decide` | Arithmetic portions of A-L3.1 and A-L4.1 |
| `no_native_symmetry` | `decide` | R§6/ERRATA E5: exact feature-table comparison over all 48 signed permutations |
| `native_features_length` | `decide` | Object/A§1 auxiliary: the geometric role index covers exactly the 192 literal rows |
| `native_feature_centers_nodup` | `decide` | Object/A§1 auxiliary: the 192 eighth-grid tube centres are distinct |
| `native_feature_normal_axis` | `decide` | Object/A§1 auxiliary: every selected literal panel normal is a signed unit coordinate vector |
| `solid_mesh_exact` | `native_decide` | Object: mesh equals the panel construction triangle-by-triangle; 2,138/6,408/4,272; volume 7 |
| `boundary_sphere` | `native_decide` | Object: every boundary edge has two incident triangles, the triangle graph is connected, every vertex link is one cycle, and the computed V/E/F counts have Euler characteristic 2; surface classification and PL Schoenflies/Alexander are the cited T3 bridge to a closed 3-ball |
| `nested_substitution_controls` | `native_decide` | R§9 finite `n ≤ 2` nested-patch controls and same-frame grandchild |
| `hierarchy_cell_controls` | `native_decide` | R§9 finite root double-refinement cover (448 cells) and 48-frame action on the 64 four-block offsets |
| `registered_shell_cell_controls` | `native_decide` | R§7 finite cell bridge: 44 distinct legal contacts, all 192 roles map onto the 22 shell cells, every legal contact meets the shell and uses one of 48 frames, exact mates own their far cell, and touching legal neighbours have a relative far-cell witness |
| `orientation_group_24` | `native_decide` | R§6: 19 contact rotations generate the proper group of order 24 |
| `substitution_modular_coincidence` | `native_decide` | C3(c)/R7: total 168-label constant-length substitution; 168×168 matrix with column sum 8 and least primitive exponent N=3; least modular coincidence M=3 at a=(0,0,2), label i=78; independently checked by `verify/substitution_modular_coincidence.py` |
| `seed_language_closure` | `native_decide` | P1: exact legal 2×2×2 block-language closure 168→600→1,278→1,398→1,410→stable; 27 fixed seeds in proper-frame orbits 24 and 3, stabilizer histogram {1↦24, 8↦3}, in-place reproduction and frame commutation; independently checked by `verify/seed_language_closure.py` |
| `mesh_angle_audit` | `native_decide` | Object/A-L3.1 finite mesh-angle audit: all 6,408 edges and 1,536 feature-edge classes |

The definitions in `R44/FiniteModel.lean` follow the cell-set, signed-frame,
contact, shell, parent, mate and baseline-overlap statements in
`PROOFS_registered.md` §1 and §§6–8 and `ALIGNMENT_PROOF.md` §5.  They do
not import or execute packet Python.  The certificate tables are used as
literal expected sets; Lean independently reconstructs the enumerated sets
and compares them extensionally.

## Phase-2 theorem

`R44/LogicalSpine.lean` defines:

- the seven-cube carrier `P` from `chairCells`; the 192 centers, outward
  normals, and signed coefficients from the 24 literal panel rows; and the
  resulting square-tent solid `Q` with `eta = 1/100` and heights `a/10000`;
- for every role, its four triangular faces, four closed base edges, four
  closed ridges, and their relative-interior generic strata;
- `Tiling Q`: a set of affine-isometric placements of the closed set `Q`,
  with pairwise disjoint interiors and pointwise union equal to all of R³;
- `RegisteredPose` and `Registration`: one ambient isometry after which every
  placement has a proper cubic frame and integer translation;
- `handedness`: the basis-independent determinant of a rigid motion's linear
  part, together with the fact that every registered frame has determinant `1`;
- `Per T`: translation stabilizers, and `Sym T`: the full affine-isometry
  stabilizer of the unlabelled family of tile subsets;
- complete-feature center/normal equations and their extensional relation to
  the 6,862-pose census;
- geometric parent partitions as sets of macro-poses whose disjoint fibers
  are exactly the eight literal child poses (index 7 is the designated central
  child); and
- translation of tilings and the derived coarsening whose placements are the
  unique parent poses with origins halved;
- commonly registered baseline `P`-tilings and genuine relatively open
  planar-patch face adjacency; and
- the recursive hierarchy levels `A_n`, their centered pose union, flattened
  cell supports, and documented bounding boxes.

There is no independent geometric constant in this construction. In
particular, `Q` and all feature strata are definitions. They use the canonical
panel/profile literals also used to generate `solid/r44_solid.json`.
`solid_mesh_exact` checks the exported mesh against that construction at the
finite triangle-table level. This round does not prove a separate Mathlib set
equality between `Q` and the union of the exported mesh tetrahedra; no such
mesh-to-definition equality is needed by the logical spine.

The final checked statement is:

```lean
theorem r44_einstein : Nonempty (Tiling Q) ∧ ∀ T : Tiling Q,
    Per T = {0} ∧ (Set.univ : Set (Sym T)).encard ≤ 24
```

The empty-record historical interface still checks:

```lean
theorem tiling_homochiral (H : Hypotheses) (T : Tiling Q) :
    ∀ g h : RigidMotion, g ∈ T.placements → h ∈ T.placements →
      handedness g = handedness h
```

`tiling_orientation_normalization` supplies the one common ambient isometry,
`tiling_handedness_dichotomy` gives the all-`+1`/all-`-1` alternative, and
`tiling_chirality_corollary` additionally excludes a reflected and unreflected
placement in one tiling.

Packet C3(a), under ruling R7, also checks:

```lean
structure GeometricHierarchy (H : Hypotheses) (T : Tiling Q) where
  partition : ∀ n : Nat, CarrierCell T → RigidMotion
  level_zero : ∀ c : CarrierCell T, partition 0 c = c.1
  registered : ∀ n : Nat, ∃ A : RigidMotion, ∀ c : CarrierCell T,
    Nonempty (RegisteredPose (A * partition n c))
  nested : GeometricHierarchyNested partition

structure CarrierHierarchy (H : Hypotheses) (T : Tiling Q) where
  partition : ∀ n : Nat, CarrierCell T → LevelSupertilePose H T n
  level_zero : ∀ c : CarrierCell T, (partition 0 c).pose = c.1
  nested : IntrinsicCarrierHierarchyNested partition

theorem carrier_hierarchy_exists (H : Hypotheses) (T : Tiling Q) :
    Nonempty (CarrierHierarchy H T)

theorem carrier_hierarchy_unique (H : Hypotheses) (T : Tiling Q)
    (K K' : CarrierHierarchy H T) : K = K'

theorem geometric_hierarchy_canonical (H : Hypotheses) (T : Tiling Q)
    (K : GeometricHierarchy H T) : ∀ (n : Nat) (c : CarrierCell T),
    K.partition n c ∈ (coarseningIterate H n T).placements

theorem geometric_hierarchy_unique (H : Hypotheses) (T : Tiling Q)
    (K K' : GeometricHierarchy H T) : K = K'

theorem carrierHierarchy_geometric (H : Hypotheses) (T : Tiling Q) :
    Nonempty (GeometricHierarchy H T)

theorem carrier_hierarchy (H : Hypotheses) (T : Tiling Q) :
    (∀ c : CarrierCell T, (carrierHierarchy H T).partition 0 c =
      @LevelSupertilePose.ofCell H T 0 c) ∧
    (∀ (n : Nat) (c : CarrierCell T),
      Nonempty (RegisteredPose ((carrierLevelRegistration H T n).ambient *
        ((carrierHierarchy H T).partition n c).pose))) ∧
    CarrierHierarchyNested (carrierHierarchy H T) ∧
    ∀ K K' : CarrierHierarchy H T, K = K'
```

For `CarrierHierarchy`, `partition n` lands in `LevelSupertilePose`, whose `mem`
field requires membership in `D^n(T)`; `LevelSupertilePose.support` is the
corresponding `2^n`-scaled chair. Its `nested` field is geometric but its range
is therefore canonical. `GeometricHierarchy.partition` instead lands directly
in `RigidMotion` and its nesting predicate mentions no coarsening. The theorem
`geometric_hierarchy_canonical` is the written T7.1 induction that forces every
raw pose into `D^n(T)`; the conversions in both directions and
`geometric_hierarchy_unique` show that the notions coincide. There is
deliberately no fixed-cell exhaustion clause and no local-derivability theorem.

Packet C3(c) adds the independent finite theorem:

```lean
theorem substitution_modular_coincidence :
    substitutionTotalWellDefinedCheck = true ∧
    substitutionMatrixDimensionsCheck = true ∧
    substitutionConstantColumnSumCheck = true ∧
    leastPrimitiveExponent = some 3 ∧
    leastModularCoincidenceDepth = some 3 ∧
    substitutionLabels.idxOf (substitutionLabelAt 11 1) = 78 ∧
    modularCoincidenceWitness 3 =
      some (v 0 0 2, substitutionLabelAt 11 1)
```

Its 168 labels, transition matrix, powers, and address sets are computed from
the generated 24 frames and eight child poses. Lee--Moody Theorem 3 and
Schlottmann are cited T3 imports for the model-set/pure-point/limit-periodic
classification of the substitution hull, not Lean conclusions about all Q
tilings. The fault-line question remains open.

The `encard` inequality is the faithful instance-free form of
`Fintype.card (Sym T) ≤ 24`: because the right side is finite, it asserts both
that `Sym T` is finite and that its cardinal is at most 24.

| Lean theorem | Correspondence in `THEOREM.md` | Proof source |
|---|---|---|
| `registration_of_tiling` | A-T6.3, using the A§2–6 chain | discharged endpoint theorems plus mesh/profile, mate, atlas, and 24-frame finite theorems |
| `tiling_homochiral` / `tiling_chirality_corollary` | R§6/C2, proper registered frames have one handedness | kernel determinant calculation from `registration_of_tiling`; no residual field |
| `parent_local_to_global` / `unique_parent` | R§7 / Theorem 7.1 | proved registered-shell and central-completion bridges, the remaining conflict readout, and kernel construction/uniqueness of the geometric parent set |
| `coarsening_realization` / `coarsening_is_tiling` | R§8 / Theorem 8.1 realization | macro-baseline partition, `parent_atlas_eq_fine`, and the shared small-collar realization |
| `coarsening_translation_equivariant` | R§8, `D(T+v)=D(T)+v/2` | kernel proof from translation of geometric parent sets and their uniqueness |
| `carrier_hierarchy_exists` / `carrier_hierarchy_unique` / `carrier_hierarchy`; `geometric_hierarchy_canonical` / `geometric_hierarchy_unique` / `carrierHierarchy_geometric` | R§8–9/C3(a), canonical and arbitrary geometric nested carrier partitions | iterated coarsening supplies the canonical witness; the formalized levelwise T7.1 induction forces each raw geometric pose into `D^n(T)`, after which canonical uniqueness applies; no residual field |
| `period_halving` | R§8 covariance / R§10 | kernel consequence of full translation equivariance |
| `period_iterate` | R§10, p/2ⁿ remains a period | kernel induction |
| `no_period` | R§10, integer dyadic tower implies p=0 | kernel Archimedean/norm proof |
| `sym_card_le_24` | R§10, full symmetry group has order at most 24 | native asymmetry, registration, kernel group argument |
| `nested_exhaustion` / `existence` | R§9 | concrete all-n patch nesting, proved cell disjointness, box containment/exhaustion, contact closure, and the shared small-collar realization |
| `r44_einstein` | Proposed Theorem 10.1 | all preceding rows |

The exact field-to-row ledger and phase-3 discharge order are in
`HYPOTHESES.md`. There are exactly 0 fields. A-L2.1 and all three R§7
registered-shell, central-completion, and parent-conflict bridges are no
longer fields.
Packet L4 splits each of three former endpoints: A-L4.1 into two analytic/chart
remainders, R§6 into carrier recovery plus native-frame readout, and the Object
tube homeomorphism into per-tube, gluing, and image-equality remainders. The
corresponding endpoint propositions are now Lean theorems. There is no extra
hypothesis for the phase-1 facts or the proved R§10 spine.

Packet L5 likewise removes the three Group D endpoint fields. Theorems
`hasUniqueParent_of_completeParents`, `parent_local_to_global`,
`coarsening_realization`, and `nested_exhaustion` reconstruct them from the
smaller written-proof sublemmas. `closedContacts_subset_legal` reads the
inclusion already asserted by `atlasCheck` in a kernel proof and adds no native
evaluation hook. L5 continuation 1 further proves `hierarchy_patch_nesting`
for every level and `hierarchy_boxes_exhaust`; neither remains a field.
L5 continuation 2 proves `cells_refine`, `cells_two_refine`, and
`hierarchy_box_containment`; the support bound is no longer a field.
L5 continuation 3 proves `formula_mate_owns_far_cell`,
`body_cellCenter_mem_interior`, `component_cell_owner_unique`, and
`role_companion_owns_far_cell`. Continuation 4 adopts R§7's cell-wise Group D
interface: `CertifiedFirstShells` records the unique component owner of every
literal shell cell, and baseline atlas/closed-contact adjacency uses
`LatticeFaceAdjacent`. `SharesPlanarPatch` is no longer used by Group D. The
structural theorems `perm_lt_three`, `frameActReal_mul`,
`frameActReal_transpose`, and `realizesPose_relative` now prove equivariance of
realized poses without a 48-by-48 frame split. Continuation 6 closes the
remaining first-shell work: `realizedShellCover` is the duplicate-free list of
actual component-owner indices, `realizedShellCover_exact` and
`realizedShellCover_compatible` establish the search preconditions, and
`enumerateShells_complete` proves the generic accumulator invariant. The
continuation-7 theorem `certified_shells_complete_parents` then transports
those literal rows through actual component owners, applies the 14/18 central
completion census, and constructs the complete eight-child parent fibre.
Continuation 8 proves `complete_parent_conflicts`: candidate poses are
transported to actual complete-parent children, while retained-core overlap
and whole-feature companions prove that actual registered placements satisfy
the finite `compatible` predicate. The 28-of-28 census therefore rules out
distinct parent roles through one tile.
Continuation 9 proves `hierarchy_cells_disjoint` for every level. It derives
the one-refinement packing invariant from `children_partition_2P`, separates
the doubled blocks of distinct parents by their unique coarse cells, applies
the result twice through `twoRefinements`, and proves both pose deduplication
and the common centering translation preserve the flattened-cell invariant.
Continuation 10 proves `nested_contact_language` for the whole nested union.
The proof normalizes face contact to relative root coordinates, transports
refinement through signed frames, separates sibling from cross-parent
contacts, and applies the literal equality
`closureStep closedContacts = closedContacts`. Thus the R§9 contact-language
induction is no longer a hypothesis field.
Continuation 11 proves `nested_baseline_assembly`: canonical affine
isometries realize all literal hierarchy poses, their images of `P` are
exactly their finite integer-cell unions, disjoint cell lists give disjoint
interiors, the documented boxes give coverage, and the recursive frames stay
in the literal 24-frame orientation group. The R§9 baseline-assembly field is
therefore gone. `nested_atlas_baseline_assembly` packages this tiling with
`nested_contact_language` and `atlas_44`, so the complete baseline object
already has atlas-related lattice face adjacencies.

## Phase-3 Object and local-finiteness discharge

`P` is exactly the finite union of the seven unit cubes whose lower corners are
the literal `chairCells` list. Theorems `unitCube_compact`,
`unitCube_regularClosed`, and `unitCube_interior_nonempty` establish the box
facts through the finite-product homeomorphism. Finite-union induction gives
`P_compact` and `P_regularClosed`; the centre of the `(0,0,0)` cube gives
`P_interior_nonempty`.

The Object endpoint is:

```lean
def HasTubeHomeomorphism : Prop :=
  ∃ F : E3 ≃ₜ E3, F '' P = Q
```

and it is no longer a field. `tubeCutoff` and `featureTubeMap` define the exact
formula of A§1. Lean proves `featureTubeMap_fixed_on_boundary` and, from the
literal 192-row table, `featureTubeSupports_pairwiseDisjoint`. Exchange 3
proves `PerTubeHomeomorphisms`, `FeatureTubeMapsGlue`, and
`FeatureTubeMapCarriesCarrier`; `hasTubeHomeomorphism_of_tube_construction`
and `tube_homeomorphism` assemble them without a hypothesis field.

From it, `Q_compact_of_tube_homeomorphism`,
`Q_regularClosed_of_tube_homeomorphism`, and
`Q_interior_nonempty_of_tube_homeomorphism` prove the first three Object
conjuncts, while `P_homeomorphic_Q_of_tube_homeomorphism` gives the requested
subspace homeomorphism `Nonempty (P ≃ₜ Q)`.
`compactRegularClosedBall_of_tube_homeomorphism` and `tube_ball` reconstruct
the exact phase-2 interface used downstream.

The theorem

```lean
theorem local_finiteness (h : CompactRegularClosedBall Q) :
    EveryPackingLocallyFinite Q
```

discharges A-L2.1. It selects an open ball in `interior Q`; the images of its
center for placements meeting a compact set lie in the compact
`Metric.diam Q`-thickening of that set. Disjoint tile interiors make the
centers uniformly separated, and total boundedness supplies a finite cover.

For R§6, `PlanarAreaCarrierRecovery` isolates the area-classification step
`g '' Q = Q → g '' P = P`; `CarrierFeatureFrameReduction` is the subsequent
origin/frame/feature-table readout. `planar_area_native_reduction` composes
them, and `native_asymmetry_reduction` combines the result with
`no_native_symmetry` to prove `NativeAsymmetric Q`.

## Phase-3b solid-angle reductions

The generic theorem

```lean
theorem strictDownwardCone_subset_tangentCone_hypograph
    (hf : LipschitzWith K f) (u : V) :
    strictDownwardCone K ⊆ interior (tangentCone (hypograph f) (u, f u))
```

proves the documented tangent-cone inclusion at every graph point. Lean also
proves

```lean
theorem coneAngle_gt_four_pi_div_three_iff (hL : 0 ≤ L) :
    coneAngle L > 4 * Real.pi / 3 ↔ 8 * L ^ 2 < 1
```

and `r44_cone_angle_bound`, which obtains the `L=3/25` instance from the
phase-1 `lipschitzBoundsCheck`. `solidAngle_linearIsometry_image` proves
orthogonal invariance using Mathlib's volume-preserving linear isometries, and
`solidAngle_mono` proves monotonicity.

The former `Hypotheses.uniform_solid_angle` endpoint is gone. The cone-volume
half is proved as `circular_cone_solid_angle_holds`, and exchange 3 proves the
concrete local-chart half as `feature_circular_cone_containment_holds`. The
exported theorem `uniform_solid_angle` reconstructs `UniformFeatureSolidAngle
Q` from those proofs and the phase-1 bound.

## Phase-3c registered hierarchy

`RealizesPose` is now proved functional (`realizesPose_unique`), so a fixed
parent and literal child index determine at most one placement
(`childOfParent_unique`). `CompleteParent`,
`EveryPlacementHasCompleteParent`, and `CompleteParentsDisjoint` state the
two geometric outputs of the R§7 local census. From those outputs,
`hasUniqueParent_of_completeParents` constructs the parent set
`{π | CompleteParent T π}` and proves its exact-cover laws and
`Subsingleton (ParentPartition T)`. Parent existence and uniqueness are
therefore no longer assumed as an endpoint.

For R§8, `RegisteredBaselineTiling A` contains an actual `Tiling P` with
placements exactly `A` and one common ambient registration.
`LatticeFaceAdjacent` is the Group D adjacency relation: two registered
literal chair bodies have an `allFrames` relative pose whose finite `touch`
predicate detects a face contact. `AtlasBaselineTiling A` requires each such lattice adjacency to
satisfy `AtlasRelated`. `SharesPlanarPatch` remains defined for later
continuous-geometric interfaces but is not used by Group D.
`coarsening_realization` composes the macro-baseline partition, the
parent-atlas readout, and the shared `SmallCollarRealization` statement. That
last field is explicitly conditional on the assembled A§1 ambient tube
homeomorphism.

For R§9, `hierarchyPoseLevel`, `hierarchyCenterShift`, and `hierarchyPatch`
define the exact `A_n`. The center shift is defined by
`c_0=0`, `c_(n+1)=4c_n+2`; Lean proves the equivalent identity
`3c_n+2=2·4^n`. `hierarchyPatch_one` and `hierarchyPatch_two` are
definitional equalities with the phase-1 finite patches. The theorem
`hierarchy_patch_nesting` proves `A_n ⊆ A_(n+1)` for all `n` from the
same-frame grandchild and refinement-translation equivariance. The theorem
`hierarchy_boxes_exhaust` proves that the documented centered cubes exhaust
`E3`. Because a signed coordinate reversal sends the lower corner `a` to
`-a-1`, `cells_refine` states equivariance with `cellLower`, not the false
plain point-vector formula. `cells_two_refine` applies it twice, and the
finite `hierarchy_cell_controls` theorem supplies the root 448-cell cover and
the 48-frame offset action. Euclidean division by four then proves
`hierarchy_box_containment` for every level. The theorem
`hierarchy_cells_disjoint` proves the flattened cell list is duplicate-free
at every level, including through `hashDedup` and the common centering
translation. The set
`hierarchyPlacements` is the extensional union of motions realizing a pose in
some `A_n`. The theorem `nested_baseline_assembly` constructs its
`RegisteredBaselineTiling`: exact cubical images and density of open cell
cores supply disjoint interiors, `hierarchy_boxes_exhaust` and
`hierarchy_box_containment` supply coverage, and recursive
orientation-group closure supplies registration.
`nested_contact_language` proves the contact-closure half directly.
`nested_atlas_baseline_assembly` applies
`HierarchyBaselineTiling.toAtlas` using
`closedContacts_subset_legal atlas_44`, then feeds the same small-collar
realization used by coarsening.

## What is not proved here

The tube inverse, gluing, image equality, circular-cone evaluation, concrete
feature-chart containment, retained-core overlap, carrier recovery, and
carrier-to-frame readout are all proved. Carrier recovery is the exchange-3
diameter-endpoint proof of the unchanged proposition; it does not formalize
the written planar-area calculation.

No fields remain hypotheses for phase 3. The complete dihedral list, generic
feature partners, baseline component coverage, unrestricted alignment,
cone-sector budgets, the connected whole-graph companion theorem, containment
rigidity, companion-pose discretization, registered mates, physical solid
coverage, and small-collar realization are proved. Both the
macro-baseline coarsening assembly and the all-n hierarchy baseline assembly
and its contact-language induction are proved.
Their statements, dependencies, and geometric proofs are mechanized.

For packet L5 target 1, the cell-wise first-shell theorem, central completion,
and geometric readout of all 28 parent conflicts are now proved. Group D's
R§7 branch has no remaining hypothesis field.

For packet L5 target 2, continuation 15 proves `parent_common_parity`: actual feature-adjacent
children put distinct parents through the structural macro filter chain, and
induction over the single grid-covering feature component propagates evenness
to every parent pair. Continuation 16 proves `halved_parent_baseline_tiling`:
the component baseline cover and exact 56-cell parent fibres yield coverage;
macro-body disjointness yields disjoint interiors after halving; and the common
even phase supplies one proper-frame integer registration. The R§8
macro-baseline field is removed. Parent-atlas face admissibility is proved;
only the shared small-collar realization remains.

For packet L5 continuation 13, `halfPose_realizes_doubledPose` recovers the
unhalved relative macro pose from a halved registered contact, and
`actual_parent_crossContacts_legal` proves that every induced contact between
the two actual eight-child fibres lies in `legalContacts`. Continuation 14
closes `parent_atlas_admissibility`: exact refinement constructs a touching
child pair across every macro face, its explicit triple enters
`computedMacroCandidates`, geometric cell disjointness enters
`macroNonoverlap`, and universal child-contact legality enters
`computedMacroLegal`. This is a structural kernel proof, not a new phase-3
native computation.

For the registered-shell theorem, feature companions provide owners for all 22
far-side cells, disjoint retained cores give uniqueness, and
`realizesPose_relative` supplies the coordinate change needed for the finite
touching-neighbour control. Lean packages those owners as a duplicate-free,
pairwise-compatible exact legal-index cover. The general theorem
`enumerateShells_complete` proves that every such cover is returned by the
recursion, and `first_shells_33` identifies it with one of the 33 certificate
rows.

For packet L5 target 3, patch nesting, the support bound, Archimedean
exhaustion, cell disjointness, baseline assembly, and the contact-language
induction are now theorems. The finite `n=1,2` controls are not used as a
surrogate for an infinite induction.

The finite core is imported unchanged rather than restated. There is no
`sorry`, project `axiom`, `opaque`, `unsafe`, `extern`, or `implemented_by`
declaration in the Lean sources.

## Controls runner

`negative/NegativeControl.lean` contains two deliberately false copies: it
flips the first sign of the profile and removes the first rejection witness.
Each false example invokes the same parameterized Boolean used by the
corresponding production theorem (`profile_canonical` or `mates_census`).  The
file is deliberately not imported by the library.

The former `negative/HypothesesContradiction.lean` diagonal attack was retired
when Phase F closed: the now-empty `Hypotheses` record is intentionally
inhabited by `⟨⟩`. The repaired distinct-tile signatures remain exercised by
the positive scope checks, while the four other must-fail controls continue to
attack certificate corruption, mixed handedness, and hierarchy uniqueness.

Each file declares the required error text in a leading `-- EXPECT:` comment.
Run the positive build, every diagnostic-checked negative control, and the
positive scope regressions with one command:

```sh
scripts/controls.sh
```

The four negative compilations must exit nonzero for the declared reasons. The
historical full diagnostics are recorded in `negative_control.log`.
`R44/ScopeRegressions.lean` compiles thirty-three positive examples:
self-mate exclusion, irreflexive adjacency, reflexive component membership,
reflexive raw containment, containment rigidity with an explicit distinctness
witness, equality of handedness for two placements in a registered tiling,
carrier-hierarchy nesting/existence/uniqueness, nineteen endpoint checks that
install every discharged proof at its former field boundary, and the
unconditional `r44_einstein` elaborating with no argument.
It is a library-root regression module, not one of the finite theorems in
`R44/Theorems.lean`. Packets C2 and C3(a) add only spine theorems; C3(c) adds
one T1n theorem, so the finite count above is exactly 22.

## Performance

For Phase F exchange 7 and final discharge, `scripts/controls.sh` passed in
**8 minutes 48.48 seconds** wall time with **9,769,136 KB** peak resident
memory (`admissions=0`, four diagnostic-checked negative controls, and the
positive scope regression). The subsequent cache-warm full incremental
`lake build` under Lean 4.31.0 took **4.75 seconds** wall time and
**904,656 KB** peak resident memory, replaying all 8,638 jobs. The promoted
`R44Discharge` target rebuild took **10 minutes 37.42 seconds** and
**8,412,724 KB** peak resident memory. No clean build was used.

For packet F3 exchange 4 after discharge, `scripts/controls.sh` passed in
**71.02 seconds** wall time with **6,595,096 KB** peak resident memory. The
subsequent cache-warm full incremental `lake build` under Lean 4.31.0 took
**4.65 seconds** wall time and **904,192 KB** peak resident memory. It rebuilt
or replayed all 8,593 jobs; no clean build was used.

For packet C3 turn 4, the freshly changed `R44.LogicalSpine` target compiled in
**5 minutes 25 seconds**. The subsequent complete incremental `lake build`
under Lean 4.31.0 took **14.13 seconds** wall time and **6,729,832 KB** peak
resident memory, rebuilding the axiom audit, scope regressions, and root module.
No clean build was used.

For packet C3(c), the complete incremental `lake build` under Lean 4.31.0,
including the generated 168-label substitution computation, refreshed axiom
audit, scope regressions, and root module, took **5 minutes 46.67 seconds** wall
time and **11,287,480 KB** peak resident memory. No clean build was used.

For packet C3(a), the complete incremental `lake build` under Lean 4.31.0,
including the rebuilt `R44.LogicalSpine`, refreshed axiom audit, scope
regressions, and root module, took **5 minutes 39.06 seconds** wall time and
**11,321,632 KB** peak resident memory. No clean build was used.

For packet C2, the final cache-warm full incremental `lake build` under Lean
4.31.0 took **4.76 seconds** wall time and **940,656 KB** peak resident memory.
The earlier target refresh rebuilt `R44.LogicalSpine` in 319 seconds; the final
reported full build followed the controls build and therefore reused that
object. No clean build was used.

For packet L5X, the complete incremental `lake build` under Lean 4.31.0,
including `R44.LogicalSpine`, the refreshed axiom audit, and the root module,
took **5 minutes 42.23 seconds** wall time and **10,309,436 KB** peak resident
memory. Four Lean threads per compiler process were enforced by
`moreLeanArgs`; no clean build was used and `.lake/packages` was not touched.
