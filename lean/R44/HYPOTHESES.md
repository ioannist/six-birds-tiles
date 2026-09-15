# Phase-3c hypothesis ledger

`R44.Hypotheses` is now empty: all 19 continuous or infinite-space fields have
been discharged. The former
`tube_ball` field was first reduced to `tube_homeomorphism`; packet L4 then
split that remainder into the explicit per-tube homeomorphism, finite gluing,
and image-equality sub-lemmas. Compactness, regular closure, and nonempty
interior are Lean theorems. The former `local_finiteness` field has been removed completely;
`R44.local_finiteness` proves A-L2.1 from compactness and a nonempty interior.
The native-asymmetry endpoint is split into carrier recovery and the
subsequent native-frame/feature-table readout;
the theorem `R44.planar_area_native_reduction` reassembles them, and
`R44.native_asymmetry_reduction` combines the result with the imported
48-frame theorem `no_native_symmetry`. In phase 3b the conclusion-shaped
`uniform_solid_angle` field was removed and split into the exact two remaining
sub-lemmas `circular_cone_solid_angle` and
`feature_circular_cone_containment`; the exported theorem
`R44.uniform_solid_angle` reconstructs A-L4.1. The
geometric set `Q`, its 192 feature surfaces and graphs, the geometric
parent-partition type, translation of tilings, and coarsening remain
definitions. Every Boolean premise below is discharged by an imported phase-1
theorem.

Phase F packet F1-discharge removes `retained_core_overlap`,
`carrier_feature_frame_reduction`, and `circular_cone_solid_angle` from the
record. Their sorry-free exchange-2 proofs now live in `R44/Proved/` and are
imported by `R44.LogicalSpine`.

Phase F packet F2-exchange3-discharge removes `per_tube_homeomorphisms`,
`feature_tube_maps_glue`, `feature_tube_map_carries_carrier`,
`feature_circular_cone_containment`, and `planar_area_carrier_recovery` from
the record. Their sorry-free exchange-3 proofs and the three sorry-free
helpers they require now live in `R44/Proved/`. Carrier recovery uses the
delivery's alternative diameter-endpoint proof of the unchanged
`PlanarAreaCarrierRecovery` proposition, not the written planar-area
calculation.

Phase F packet F3-exchange4-discharge removes `cone_sector_budgets`,
`connected_feature_companion`, `feature_containment_rigidity`, and
`companion_pose_discrete`. Their sorry-free exchange-4 proofs and eight
required helpers now live in `R44/Proved/`. Containment rigidity uses compact
isometric containment of its feature graph, while the connected-companion
proof uses the discharged open circular-cone inclusion. Ruling R8 replaces
the delivered nonreducing metadata `rfl` by the named finite theorem
`R44.mate_records_roles_nonempty`, without changing its proposition.
The summary of `cone_sector_budgets` is: incident tangent cones cover every
direction; their interiors are pairwise disjoint. This is the formal predicate
and the order of the two claims in A-L2.2.

Phase F packet F4-exchange5-discharge removes `only_registered_mates` and
`component_solids_cover`. Their admission-free exchange-5 proofs and five
required helpers now live in `R44/Proved/`. The physical-coverage endpoint
uses the clamping argument recorded in `THEOREM.md`, not assembly-wide tube
gluing.

Phase F packet F5-exchange6-discharge removes `small_collar_realization`.
Its admission-free assembly-collar proof and eight required helpers now live
in `R44/Proved/`; the duplicate-site and separation argument is recorded in
`THEOREM.md`.

Phase F packet F6-exchange7-discharge removes `complete_dihedral_list`,
`generic_feature_partner`, `baseline_component_covers_grid`, and
`unrestricted_alignment`. Their admission-free proofs and the complete
exchange-7 helper closure now live in `R44/Proved/`. Rulings R8 and R10 name
the two large finite compiler checks `native_mesh_incidence_trace` and
`carrier_coordinate_states_table`; neither changes the delivered
proposition. `R44/Discharge/` is empty and `R44.r44_einstein` is unconditional.

Packet L5 removes the three conclusion-shaped Group D fields.  Their
replacements expose the actual registered-shell, macro-baseline, hierarchy,
and shared realization bridges. Lean now proves the parent-pose-set assembly,
the inclusion of the closed 30-state hierarchy language in the 44 atlas, and
the reconstruction of both R§8 and R§9 from one `SmallCollarRealization`
field. Packet L5 continuation 1 additionally discharges the all-level patch
nesting induction and the Archimedean box-exhaustion remainder. Continuation 2
discharges the all-level box-containment induction from a new phase-1 finite
root control and signed-frame lower-corner equivariance.
Continuation 3 closes the feature-formula half of the active first-shell
bridge: `registered_shell_cell_controls`, `formula_mate_owns_far_cell`,
`body_cellCenter_mem_interior`, and `component_cell_owner_unique` connect
features to unique integral-cell owners. Continuation 4 reformulates Group D
cell-wise as in R§7. `CertifiedFirstShells` now quantifies over the 22 literal
shell cells and their unique component owners, while `AtlasBaselineTiling` and
the nested closed-contact language use `LatticeFaceAdjacent`; the analytic
`SharesPlanarPatch` predicate no longer occurs in Group D.
Continuation 6 discharges the cell-wise first-shell bridge itself.  Lean forms
the duplicate-free list of actually realized owner indices, proves exact
coverage and pairwise compatibility, proves the accumulator invariant for
`enumerateShells`, and uses `first_shells_33` to identify the result with a
literal row of `Generated.shellSolutions`.
Continuation 7 discharges `certified_shells_complete_parents`.  The proof
transports the root and central certified-shell rows to actual component
placements, proves the actual centre row belongs to `centralViable`, uses the
14/18 `central_completion` census to force the unique central row 0, and then
constructs the parent motion and all eight literal child fibres.
Continuation 8 discharges `complete_parent_conflicts`.  Lean extracts every
pairwise conflict from the 28-of-28 aggregate certificate, transports each
candidate-parent pose to an actual child placement, and proves that actual
registered placements always satisfy the finite compatibility predicate.
Continuation 9 discharges `hierarchy_cells_disjoint`. Lean preserves the
duplicate-free flattened cell list through each one-step refinement using the
transported eight-child partition, applies this twice to `twoRefinements`,
proves `hashDedup` preserves the packing, and finally transports the invariant
through the common centering translation defining `hierarchyPatch`.
Continuation 10 discharges `nested_contact_language`. Lean proves contact
equivariance for arbitrary registered signed frames, shows a fine-cell
contact either lies inside one parent or forces a coarse parent contact,
applies the 30-state closure fixed point through both refinements, and then
passes through pose deduplication, centering, and the nested union.
Continuation 11 discharges `nested_baseline_assembly`. Lean realizes every
literal signed pose as an affine isometry, proves that its image of `P` is
exactly the union of its listed integer cells, derives disjoint interiors by
density of the open unit-cell cores, obtains coverage from the exhaustive
contained boxes, and proves that every hierarchy frame lies in the literal
24-element orientation group. `nested_atlas_baseline_assembly` then combines
that result with `nested_contact_language` and `atlas_44`.
Continuation 12 proves that affine origin-halving respects composition, and
that an even registered macro pose realizes the literal `halvePose`; it also
extracts the even-shift clause propositionally from `parent_atlas_eq_fine`.
Continuation 15 closes the common-parity bridge.  The structural theorem
`parent_common_parity` proves that all parent origins lie in one parity class:
an actual feature edge supplies a macro candidate, parent-fibre disjointness
puts it in `macroNonoverlap`, actual cross-contact legality puts it in
`computedMacroLegal`, and `SameFeatureComponent` induction propagates the
certified even shift.  Grid coverage plus retained-core disjointness proves
that every placement belongs to that one feature component. Continuation 16
closes the remaining set-level cubical packaging: `halved_parent_baseline_tiling`
transports the exact eight-child dissection through each parent, divides the
common even phase by two, proves coverage and disjoint interiors for the
halved seven-cube bodies, and supplies one common `Registration`.
Continuation 13 proves `halfPose_realizes_doubledPose` and
`actual_parent_crossContacts_legal`: every cross-child contact induced by two
distinct actual parent fibres is in the literal 44-contact list.  The
continuation-14 theorem `parent_atlas_admissibility` closes the remaining
finite-list bridge structurally: exact refinement supplies an explicit child
contact, that contact supplies a witness triple in the `8 × 44 × 8`
enumeration, disjoint actual parent bodies imply membership in
`macroNonoverlap`, and universal child-contact legality enters the final
filter. No phase-3 `native_decide` hook is added.

## Archived diagonal audit (packet L5X)

The following audit distinguishes a genuinely binary tile/feature assertion
from a unary assertion or a harmless diagonal merely written with several
parameters.  “Admitted?” means admitted by the repaired formal statement. Raw
geometric relations are listed after the historical 7-field audit because they
are part of the same public interface. The table is archived now that the
record is empty; the frozen companion premises remain part of the promoted
field propositions. The former `HypothesesContradiction.lean` negative control
was retired at closure because it attacked inhabitability of a record that is
now intentionally inhabited by `⟨⟩`; the four remaining signature and
uniqueness attacks remain active.

| `Hypotheses` field | Diagonal admitted? | Written scope | Change made |
|---|---:|---|---|
| `complete_dihedral_list` | Yes, harmless | A-L3.1: unary classification of every role and mesh edge, plus `Function.Injective featureDeviation` | None; the injectivity clause admits equal indices, where its conclusion is reflexive equality. |
| `generic_feature_partner` | No for the partner | A-L3.2: the unique *other* incident tile at a generic edge point | None; `HasUniqueGenericPartner` already requires `hs.1 ≠ g`. The root may occur in its final incident-tile disjunction, as intended. |
| `only_registered_mates` | **No (was yes)** | A-L5.3: two distinct companion tiles | Added `g ≠ h`. |
| `baseline_component_covers_grid` | Yes where reflexivity is required | A-L6.1: the root belongs to its own feature component | None; the pairwise disjointness conclusion already assumes `h ≠ k`. |
| `component_solids_cover` | Yes | A-L6.2: the covering witness may be the root tile | None; excluding it would incorrectly weaken coverage. |
| `unrestricted_alignment` | N/A | A-T6.3: one whole tiling | None. |
| `small_collar_realization` | N/A directly | A§1 / A-L6.2, R§8–9 / ERRATA E2, E6: realize a complete registered baseline tiling | None; its underlying `AtlasBaselineTiling.atlas_faces` clause already assumes distinct poses. |

Line numbers below are as of this commit.

| Auxiliary relational predicate | Diagonal admitted? | Written scope | Change made |
|---|---:|---|---|
| `CompleteFeatureMate g r h s` | Syntactically yes | `CompleteFeatureMate` in `R44/LogicalSpineFoundation.lean:759`; A-L4.3 / A-C4.4 / A-L5.3: raw equality/formula for two complete features | Kept raw. The kernel theorem `no_self_mate` proves `profileCoefficient r ≠ 0 → ¬ CompleteFeatureMate g r g r`; all companion-tile consumers now carry distinctness. |
| `FeatureContained` / `FeatureCoveredByTile` | Yes | `FeatureContained` and `FeatureCoveredByTile` in `R44/LogicalSpineFoundation.lean:754, 1355`; A-T4.2 / A-L4.3: raw set containment used by the companion and rigidity lemmas | Kept raw; `WholeFeatureCompanions` and repaired rigidity supply the distinct-tile premise. |
| `FeatureAdjacent` | **No (was conditionally yes)** | `FeatureAdjacent` in `R44/LogicalSpine.lean:29`; A-L6.1: an edge between two distinct tiles in the feature-component graph | Added `g ≠ h`; symmetry and construction sites now transport that witness. |
| `SameFeatureComponent` | Yes | `SameFeatureComponent` in `R44/LogicalSpine.lean:35`; A-L6.1 / A-L6.2: reflexive-transitive feature-component membership | Kept intentionally reflexive. |
| `AtlasRelated` | Syntactically possible | `AtlasRelated` in `R44/LogicalSpineFoundation.lean:909`; A-L5.3 / R§7–9: raw membership in the literal legal-contact list | Kept raw; distinctness is imposed by tiling/graph consumers. |
| `LatticeFaceAdjacent` | Syntactically possible | `LatticeFaceAdjacent` in `R44/LogicalSpine.lean:404`; R§7–9: raw integer-cell face-contact predicate | Kept raw; `AtlasBaselineTiling.atlas_faces` and `ClosedContactFaceLanguage` already assume distinct poses. |
| `Packing` / `Tiling` pairwise-disjoint clauses | No | `Packing` and `Tiling` in `R44/LogicalSpineFoundation.lean:475, 483`; A-L2.1 / A-L2.2: distinct placed copies | None; both already require unequal placements. |

Thus every field whose written lemma says “other tile”, “companion tile”, or
otherwise assumes distinct placed copies now exposes that premise.  Relations
whose diagonal is mathematically meaningful (component reflexivity, raw set
containment, or the trivial equal-pose overlap implication) remain unchanged.

| L4 change | Before | After |
|---|---|---|
| A-L4.1 | `uniform_solid_angle : deviationsDistinctCheck = true → lipschitzBoundsCheck = true → UniformFeatureSolidAngle Q` | `circular_cone_solid_angle : R44ConeSolidAngleFormula` and `feature_circular_cone_containment : FeatureCircularConeContainment Q`; `uniform_solid_angle` is now a theorem |
| R§6 native reduction | `native_asymmetry_planar_reduction : PlanarAreaNativeReduction` | `planar_area_carrier_recovery : PlanarAreaCarrierRecovery` and `carrier_feature_frame_reduction : CarrierFeatureFrameReduction`; `native_asymmetry_planar_reduction` is now a theorem |
| Object tube construction | `tube_homeomorphism : HasTubeHomeomorphism` | `per_tube_homeomorphisms`, `feature_tube_maps_glue`, and `feature_tube_map_carries_carrier`; `tube_homeomorphism` is now a theorem, and tube-support disjointness/boundary identity are proved |
| Other obligations | 14 fields | The same 14 fields |
| Total | 17 fields | 21 fields |

| L5 Group D change | Before | After |
|---|---|---|
| R§7 | `parent_local_to_global` | No remaining field; `registered_first_shells`, `certified_shells_complete_parents`, `complete_parent_conflicts`, and `parent_local_to_global` are theorems |
| R§8 | `coarsening_realization` | Only the shared `small_collar_realization`; `halved_parent_baseline_tiling`, `parent_atlas_admissibility`, and `coarsening_realization` are theorems |
| R§9 | `nested_exhaustion` | Only the shared `small_collar_realization`; `nested_baseline_assembly`, `hierarchy_patch_nesting`, `hierarchy_cells_disjoint`, `hierarchy_box_containment`, `hierarchy_boxes_exhaust`, and `nested_contact_language` are theorems |
| Total after L5 factoring | 21 fields | 30 fields |
| L5 continuation 1 | `hierarchy_patch_nesting`, `hierarchy_boxes_exhaust` | Both are Lean theorems; 28 fields remain |
| L5 continuation 2 | `hierarchy_box_containment` | `cells_refine` and `cells_two_refine` transport the root dissection; `hierarchy_box_containment` is a theorem; 27 fields remain |
| L5 continuation 6 | `registered_first_shells` | The actual component-owner cover and generic `enumerateShells_complete` invariant are theorems; 26 fields remain |
| L5 continuation 7 | `certified_shells_complete_parents` | Central-shell transport and the literal completion census are assembled by a Lean theorem; 25 fields remain |
| L5 continuation 8 | `complete_parent_conflicts` | The 28-of-28 finite conflict census and geometric compatibility contradiction are assembled by a Lean theorem; 24 fields remain |
| L5 continuation 9 | `hierarchy_cells_disjoint` | The child partition, doubled-cell block separation, two-step refinement, pose deduplication, and centering translation are assembled by a Lean theorem; 23 fields remain |
| L5 continuation 10 | `nested_contact_language` | Structural contact equivariance and the literal 30-state refinement fixed point are assembled by a Lean theorem; 22 fields remain |
| L5 continuation 11 | `nested_baseline_assembly` / `nested_atlas_baseline_assembly` | Canonical affine pose realization, exact cubical images, disjoint interiors, coverage, 24-frame registration, and atlas-related faces are assembled by Lean theorems; 21 fields remain |
| L5 continuation 14 | `parent_atlas_admissibility` | The candidate/nonoverlap/legal filter chain and its exact-refinement contact witness are kernel theorems; 20 fields remain |
| L5 continuation 15 | common parity inside `halved_parent_baseline_tiling` | `evenPose_transform`, `evenPose_relative_trans`, and `parent_common_parity` are kernel theorems; the residual field is narrowed to cubical tiling/registration packaging; 20 fields remain |
| L5 continuation 16 | `halved_parent_baseline_tiling` | Exact macro-cell refinement, component baseline coverage, common parity, halving, disjoint interiors, and registration are assembled by a kernel theorem; 19 fields remained at that checkpoint |

## Discharged

| Former `Hypotheses` field | Theorem | Delivery |
|---|---|---|
| `retained_core_overlap` | `R44.retained_core_overlap_holds` | exchange 2, 2026-09-08 |
| `carrier_feature_frame_reduction` | `R44.carrier_feature_frame_reduction_holds` | exchange 2, 2026-09-08 |
| `circular_cone_solid_angle` | `R44.circular_cone_solid_angle_holds` | exchange 2, 2026-09-08 |
| `per_tube_homeomorphisms` | `R44.per_tube_homeomorphisms_holds` | exchange 3, 2026-09-08 |
| `feature_tube_maps_glue` | `R44.feature_tube_maps_glue_holds` | exchange 3, 2026-09-08 |
| `feature_tube_map_carries_carrier` | `R44.feature_tube_map_carries_carrier_holds` | exchange 3, 2026-09-08 |
| `feature_circular_cone_containment` | `R44.feature_circular_cone_containment_holds` | exchange 3, 2026-09-08 |
| `planar_area_carrier_recovery` | `R44.planar_area_carrier_recovery_holds` | exchange 3, 2026-09-08; alternative diameter-endpoint proof of the unchanged proposition |
| `cone_sector_budgets` | `R44.cone_sector_budgets_holds` | exchange 4, 2026-09-09 |
| `connected_feature_companion` | `R44.connected_feature_companion_holds` | exchange 4, 2026-09-09; uses the discharged open-cone inclusion |
| `feature_containment_rigidity` | `R44.feature_containment_rigidity_holds` | exchange 4, 2026-09-09; compact-isometry proof of the unchanged proposition |
| `companion_pose_discrete` | `R44.companion_pose_discrete_holds` | exchange 4, 2026-09-09; metadata side condition follows ruling R8 |
| `only_registered_mates` | `R44.only_registered_mates_holds` | exchange 5, 2026-09-09; retains the frozen distinct-companion premises |
| `component_solids_cover` | `R44.component_solids_cover_holds` | exchange 5, 2026-09-09; clamping-to-interior coverage argument |
| `small_collar_realization` | `R44.small_collar_realization_holds` | exchange 6, 2026-09-09; admission-free assembly-collar construction |
| `complete_dihedral_list` | `R44.complete_dihedral_list_holds` | exchange 7, 2026-09-10; native meridian interpretation, with named R8/R10 finite hooks |
| `generic_feature_partner` | `R44.generic_feature_partner_holds` | exchange 7, 2026-09-10; native boundary-strata interpretation |
| `baseline_component_covers_grid` | `R44.baseline_component_covers_grid_holds` | exchange 7, 2026-09-10; admission-free global component assembly |
| `unrestricted_alignment` | `R44.unrestricted_alignment_holds` | exchange 7, 2026-09-10; admission-free registration assembly |

## Remaining fields

_Empty._ `R44.Hypotheses` has zero fields. The historical conditional theorem
`R44.r44_einstein_of_hypotheses (H : Hypotheses)` remains available, while
`R44.r44_einstein` has no hypothesis argument.

Lean proves:

- the strict cone `w < -K‖v‖` lies in the interior of the tangent cone of the
  hypograph of every `K`-Lipschitz function;
- `2π(1-L/√(1+L²)) > 4π/3 ↔ 8L² < 1` for `L ≥ 0`;
- the R44 instance from the phase-1 `lipschitzBoundsCheck`;
- invariance of the model solid angle under linear isometries; and
- monotonicity of `solidAngle` under containment.

The former target-1 stopping point is now discharged by
`circular_cone_solid_angle_holds`, using measurable coordinate splitting,
Tonelli, disk-volume squeezing, and explicit interval integrals.

Target 2's unchanged carrier-recovery proposition is discharged by
`planar_area_carrier_recovery_holds`. The exchange-3 delivery proves it by an
alternative diameter-endpoint argument, not by formalizing the written
connected-coplanar-region/area calculation. The subsequent
carrier-to-signed-frame/feature-table readout is
`carrier_feature_frame_reduction_holds`; `planar_area_native_reduction`
composes the two proved endpoints.

For target 3, Lean proves `native_features_length`,
`native_feature_centers_nodup`, `native_feature_normal_axis`,
`featureTubeSupport_coordinate_bound`, and
`featureTubeSupports_pairwiseDisjoint`; it also defines the exact cutoff and
tube map and proves `featureTubeMap_fixed_on_boundary`. Exchange 3 supplies
the continuous inverse, the finite gluing homeomorphism, and the exact image
equality as theorems, so the three Object tube-construction fields are gone.

The discharged A-L2.1 theorem chooses a ball inside `interior Q`. For any
packing and compact test set, the images of its center lie in the compact
`diam Q`-thickening of the test set. Pairwise disjoint tile interiors make
those centers uniformly separated; total boundedness yields finiteness.
Component-to-global coverage is discharged. Group D no longer contains
the endpoint propositions `parent_local_to_global`,
`coarsening_realization`, or `nested_exhaustion`; those are Lean theorems over
the discharged endpoint theorems. `hierarchy_patch_nesting` is now a
kernel theorem from `nested_substitution_controls`: refinement translation
equivariance embeds level `n` in level `n+1` by `2·4^n(1,1,1)`, exactly the
difference of consecutive center shifts. `hierarchy_boxes_exhaust` is also a
kernel theorem, proved by an Archimedean power-of-four bound.
`hierarchy_box_containment` is now a theorem as well. The finite theorem
`hierarchy_cell_controls` checks that the root double refinement covers the
448 cells `4a+b` and that all 48 signed frames permute the 64 offsets under
the lower-corner action. The kernel proofs `cells_refine` and
`cells_two_refine` transport this root calculation to an arbitrary pose; an
induction using quotient and remainder modulo four covers every raw cube, and
translation by `c_n` gives the documented centered box.

The Object split retains one explicit formulation fact: `HasTubeHomeomorphism`
retains the document's stronger ambient homeomorphism `E3 ≃ₜ E3`, rather than
merely a homeomorphism between the subspaces `P` and `Q`. Thus no gluing content
was weakened. Other formulation costs are unchanged: the final symmetry statement uses `encard`
rather than installing a `Fintype` instance; dihedral angles are represented by
the solid angle `2θ` of a generic-edge tangent cone; and this phase does not
prove a set equality between `Q` and the finite triangle mesh carrier in
`solid/r44_solid.json`. Instead, `Q` and its strata are defined from the same
canonical panel/profile data, while the imported `solid_mesh_exact` finite
theorem certifies triangle-by-triangle agreement of that mesh with the panel
construction.
