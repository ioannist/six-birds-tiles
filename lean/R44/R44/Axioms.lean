import R44.LogicalSpine
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace R44

#print axioms children_partition_2P
#print axioms contact_closure_30
#print axioms profile_canonical
#print axioms atlas_44
#print axioms first_shells_33
#print axioms central_completion
#print axioms parent_conflicts_28
#print axioms parent_atlas_eq_fine
#print axioms mates_census
#print axioms deviations_distinct
#print axioms no_native_symmetry
#print axioms native_features_length
#print axioms native_feature_centers_nodup
#print axioms native_feature_normal_axis
#print axioms solid_mesh_exact
#print axioms boundary_sphere
#print axioms nested_substitution_controls
#print axioms hierarchy_cell_controls
#print axioms registered_shell_cell_controls
#print axioms orientation_group_24
#print axioms substitution_modular_coincidence
#print axioms seed_language_closure
#print axioms mesh_angle_audit
#print axioms no_self_mate
#print axioms unitCube_compact
#print axioms unitCube_regularClosed
#print axioms unitCube_interior_nonempty
#print axioms P_compact
#print axioms P_regularClosed
#print axioms P_interior_nonempty
#print axioms cellCenter_mem_interior_unitCube
#print axioms featureTubeMap_fixed_on_boundary
#print axioms featureTubeSupport_coordinate_bound
#print axioms featureTubeSupports_pairwiseDisjoint
#print axioms planar_area_native_reduction
#print axioms hasTubeHomeomorphism_of_tube_construction
#print axioms P_homeomorphic_Q_of_tube_homeomorphism
#print axioms Q_compact_of_tube_homeomorphism
#print axioms Q_regularClosed_of_tube_homeomorphism
#print axioms Q_interior_nonempty_of_tube_homeomorphism
#print axioms compactRegularClosedBall_of_tube_homeomorphism
#print axioms tube_ball
#print axioms tube_homeomorphism
#print axioms local_finiteness
#print axioms strictDownwardCone_isOpen
#print axioms strictDownwardCone_subset_tangentCone_hypograph
#print axioms circularCone_isOpen
#print axioms coneAngle_gt_four_pi_div_three_iff
#print axioms solidAngle_linearIsometry_image
#print axioms solidAngle_mono
#print axioms r44_cone_angle_bound
#print axioms uniform_solid_angle
#print axioms native_asymmetry_planar_reduction
#print axioms native_asymmetry_reduction
#print axioms retained_core_overlap_holds
#print axioms carrier_feature_frame_reduction_holds
#print axioms circular_cone_solid_angle_holds
#print axioms per_tube_homeomorphisms_holds
#print axioms feature_tube_maps_glue_holds
#print axioms feature_tube_map_carries_carrier_holds
#print axioms feature_circular_cone_containment_holds
#print axioms planar_area_carrier_recovery_holds
#print axioms mate_records_roles_nonempty
#print axioms cone_sector_budgets_holds
#print axioms connected_feature_companion_holds
#print axioms feature_containment_rigidity_holds
#print axioms companion_pose_discrete_holds
#print axioms only_registered_mates_holds
#print axioms component_solids_cover_holds
#print axioms small_collar_realization_holds
#print axioms DischargeAssembly.registered_assembly_collar_data
#print axioms DischargeCarrierStrata.carrier_coordinate_states_table
#print axioms DischargeMeshTrace.native_mesh_incidence_trace
#print axioms DischargeVertexData.feature_index_bounds
#print axioms DischargeVertexData.feature_vertex_lookup
#print axioms DischargeVertexData.carrier_vertex_lookup
#print axioms DischargeMeridian.native_oriented_wedge_charts
#print axioms DischargeNativeStrata.native_boundary_strata
#print axioms complete_dihedral_list_holds
#print axioms generic_feature_partner_holds
#print axioms baseline_component_covers_grid_holds
#print axioms unrestricted_alignment_holds
#print axioms Packing.ext
#print axioms Tiling.ext
#print axioms realizesPose_unique
#print axioms childOfParent_unique
#print axioms ParentPartition.ext
#print axioms hasUniqueParent_of_completeParents
#print axioms halfPose_translate
#print axioms halvedParentPoses_translate
#print axioms closedContacts_subset_legal
#print axioms hierarchyPatch_one
#print axioms hierarchyPatch_two
#print axioms hierarchy_patch_nesting
#print axioms cells_refine
#print axioms cells_two_refine
#print axioms hierarchy_cells_disjoint
#print axioms hierarchy_box_containment
#print axioms hierarchy_boxes_exhaust
#print axioms nested_contact_language
#print axioms nested_baseline_assembly
#print axioms nested_atlas_baseline_assembly
#print axioms formula_mate_owns_far_cell
#print axioms body_cellCenter_mem_interior
#print axioms component_cell_owner_unique
#print axioms perm_lt_three
#print axioms frameCoordinate_of_lt
#print axioms frameActReal_mul
#print axioms frameActReal_transpose
#print axioms realizesPose_relative
#print axioms role_companion_owns_far_cell
#print axioms shellCell_unique_owner_with_index
#print axioms enumerateShells_complete
#print axioms realizesPose_pose_unique
#print axioms featureAdjacent_comm
#print axioms sameFeatureComponent_symm
#print axioms sameFeatureComponent_trans
#print axioms shellOwner_indices_compatible
#print axioms mem_realizedShellCover
#print axioms realizedShellCover_exact
#print axioms realizedShellCover_compatible
#print axioms registered_first_shells
#print axioms realizesPose_transform
#print axioms touch_relative_has_shell_cell
#print axioms certified_shells_complete_parents
#print axioms complete_parent_conflicts
#print axioms actual_parent_crossContacts_legal
#print axioms parent_atlas_admissibility
#print axioms halved_parent_baseline_tiling
#print axioms registration_of_tiling
#print axioms handedness_eq_one_or_neg_one
#print axioms handedness_mul
#print axioms Registration.handedness_eq
#print axioms tiling_homochiral
#print axioms tiling_orientation_normalization
#print axioms tiling_handedness_dichotomy
#print axioms no_mixed_handedness
#print axioms tiling_chirality_corollary
#print axioms parent_local_to_global
#print axioms unique_parent
#print axioms uniqueParentPartition_translate
#print axioms coarsening_realization
#print axioms coarsening_is_tiling
#print axioms coarsening_placements
#print axioms coarsening_translation_equivariant
#print axioms period_halving
#print axioms period_iterate
#print axioms carrier_hierarchy_exists
#print axioms carrier_hierarchy_unique
#print axioms carrier_hierarchy
#print axioms carrierHierarchy_geometric
#print axioms geometric_hierarchy_canonical
#print axioms geometric_hierarchy_unique
#print axioms CarrierHierarchy.toGeometric_toCarrier
#print axioms GeometricHierarchy.toCarrier_toGeometric
#print axioms gridVector_norm_separated
#print axioms no_period
#print axioms sym_card_le_24
#print axioms nested_exhaustion
#print axioms existence
#print axioms r44_einstein_of_hypotheses
#print axioms r44_einstein

open Lean Elab Command

private def theoremNames : List Lean.Name :=
  [`R44.children_partition_2P, `R44.contact_closure_30, `R44.profile_canonical,
   `R44.atlas_44, `R44.first_shells_33, `R44.central_completion,
   `R44.parent_conflicts_28, `R44.parent_atlas_eq_fine, `R44.mates_census,
   `R44.deviations_distinct, `R44.no_native_symmetry,
   `R44.native_features_length, `R44.native_feature_centers_nodup,
   `R44.native_feature_normal_axis, `R44.solid_mesh_exact,
   `R44.boundary_sphere,
   `R44.nested_substitution_controls, `R44.hierarchy_cell_controls,
   `R44.registered_shell_cell_controls,
   `R44.orientation_group_24, `R44.substitution_modular_coincidence,
   `R44.seed_language_closure,
   `R44.mesh_angle_audit, `R44.no_self_mate, `R44.unitCube_compact,
   `R44.unitCube_regularClosed, `R44.unitCube_interior_nonempty,
   `R44.P_compact, `R44.P_regularClosed, `R44.P_interior_nonempty,
   `R44.cellCenter_mem_interior_unitCube,
   `R44.featureTubeMap_fixed_on_boundary,
   `R44.featureTubeSupport_coordinate_bound,
   `R44.featureTubeSupports_pairwiseDisjoint,
   `R44.planar_area_native_reduction,
   `R44.hasTubeHomeomorphism_of_tube_construction,
   `R44.P_homeomorphic_Q_of_tube_homeomorphism,
   `R44.Q_compact_of_tube_homeomorphism,
   `R44.Q_regularClosed_of_tube_homeomorphism,
   `R44.Q_interior_nonempty_of_tube_homeomorphism,
   `R44.compactRegularClosedBall_of_tube_homeomorphism,
   `R44.tube_homeomorphism, `R44.tube_ball,
   `R44.local_finiteness, `R44.strictDownwardCone_isOpen,
   `R44.strictDownwardCone_subset_tangentCone_hypograph,
   `R44.circularCone_isOpen, `R44.coneAngle_gt_four_pi_div_three_iff,
   `R44.solidAngle_linearIsometry_image, `R44.solidAngle_mono,
   `R44.r44_cone_angle_bound, `R44.uniform_solid_angle,
   `R44.native_asymmetry_planar_reduction,
   `R44.native_asymmetry_reduction,
   `R44.retained_core_overlap_holds,
   `R44.carrier_feature_frame_reduction_holds,
   `R44.circular_cone_solid_angle_holds,
   `R44.per_tube_homeomorphisms_holds,
   `R44.feature_tube_maps_glue_holds,
   `R44.feature_tube_map_carries_carrier_holds,
   `R44.feature_circular_cone_containment_holds,
   `R44.planar_area_carrier_recovery_holds,
   `R44.mate_records_roles_nonempty,
   `R44.cone_sector_budgets_holds,
   `R44.connected_feature_companion_holds,
   `R44.feature_containment_rigidity_holds,
   `R44.companion_pose_discrete_holds,
   `R44.only_registered_mates_holds,
   `R44.component_solids_cover_holds,
   `R44.small_collar_realization_holds,
   `R44.DischargeAssembly.registered_assembly_collar_data,
   `R44.DischargeCarrierStrata.carrier_coordinate_states_table,
   `R44.DischargeMeshTrace.native_mesh_incidence_trace,
   `R44.DischargeVertexData.feature_index_bounds,
   `R44.DischargeVertexData.feature_vertex_lookup,
   `R44.DischargeVertexData.carrier_vertex_lookup,
   `R44.DischargeMeridian.native_oriented_wedge_charts,
   `R44.DischargeNativeStrata.native_boundary_strata,
   `R44.complete_dihedral_list_holds,
   `R44.generic_feature_partner_holds,
   `R44.baseline_component_covers_grid_holds,
   `R44.unrestricted_alignment_holds,
   `R44.registration_of_tiling,
   `R44.handedness_eq_one_or_neg_one, `R44.handedness_mul,
   `R44.Registration.handedness_eq, `R44.tiling_homochiral,
   `R44.tiling_orientation_normalization, `R44.tiling_handedness_dichotomy,
   `R44.no_mixed_handedness, `R44.tiling_chirality_corollary,
   `R44.parent_local_to_global,
   `R44.unique_parent,
   `R44.Packing.ext, `R44.Tiling.ext, `R44.realizesPose_unique,
   `R44.childOfParent_unique, `R44.ParentPartition.ext,
   `R44.hasUniqueParent_of_completeParents,
   `R44.halfPose_mul, `R44.halfPose_translate,
   `R44.halfPose_realizes_halvePose, `R44.computedMacroLegal_even,
   `R44.halfPose_realizes_doubledPose,
   `R44.halvedParentPoses_translate,
   `R44.closedContacts_subset_legal,
   `R44.hierarchyPatch_one, `R44.hierarchyPatch_two,
   `R44.hierarchy_patch_nesting, `R44.cells_refine,
   `R44.cells_two_refine, `R44.hierarchy_cells_disjoint,
   `R44.hierarchy_box_containment,
   `R44.hierarchy_boxes_exhaust,
   `R44.nested_contact_language,
   `R44.nested_baseline_assembly,
   `R44.nested_atlas_baseline_assembly,
   `R44.formula_mate_owns_far_cell,
   `R44.body_cellCenter_mem_interior,
   `R44.component_cell_owner_unique,
   `R44.perm_lt_three, `R44.frameCoordinate_of_lt,
   `R44.frameActReal_mul, `R44.frameActReal_transpose,
   `R44.realizesPose_relative,
   `R44.role_companion_owns_far_cell,
   `R44.shellCell_unique_owner_with_index,
   `R44.enumerateShells_complete, `R44.realizesPose_pose_unique,
   `R44.featureAdjacent_comm, `R44.sameFeatureComponent_symm,
   `R44.sameFeatureComponent_trans, `R44.shellOwner_indices_compatible,
   `R44.mem_realizedShellCover, `R44.realizedShellCover_exact,
   `R44.realizedShellCover_compatible, `R44.registered_first_shells,
   `R44.realizesPose_transform, `R44.touch_relative_has_shell_cell,
   `R44.certified_shells_complete_parents,
   `R44.complete_parent_conflicts,
   `R44.actual_parent_crossContacts_legal,
   `R44.parent_atlas_admissibility,
   `R44.evenPose_transform, `R44.evenPose_relative_trans,
   `R44.parent_common_parity,
   `R44.halved_parent_baseline_tiling,
   `R44.uniqueParentPartition_translate, `R44.coarsening_is_tiling,
   `R44.coarsening_realization,
   `R44.coarsening_placements, `R44.coarsening_translation_equivariant,
   `R44.period_halving, `R44.period_iterate,
   `R44.carrier_hierarchy_exists, `R44.carrier_hierarchy_unique,
   `R44.carrier_hierarchy,
   `R44.carrierHierarchy_geometric,
   `R44.geometric_hierarchy_canonical, `R44.geometric_hierarchy_unique,
   `R44.CarrierHierarchy.toGeometric_toCarrier,
   `R44.GeometricHierarchy.toCarrier_toGeometric,
   `R44.gridVector_norm_separated, `R44.no_period, `R44.sym_card_le_24,
   `R44.nested_exhaustion, `R44.existence,
   `R44.r44_einstein_of_hypotheses, `R44.r44_einstein]

private def axiomLine (constName : Lean.Name) : CommandElabM String := do
  let axioms ← Lean.collectAxioms constName
  if axioms.isEmpty then
    pure s!"'{constName}' does not depend on any axioms"
  else
    pure s!"'{constName}' depends on axioms: {axioms.qsort Name.lt |>.toList}"

run_cmd do
  let lines ← theoremNames.mapM axiomLine
  IO.FS.writeFile "build_axioms.log" ("\n".intercalate lines ++ "\n")

end R44
