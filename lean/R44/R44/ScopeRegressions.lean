import R44.LogicalSpine

/-! Positive scope regressions supplied by the external round-2 reviewer.

These examples check both the forbidden diagonal uses and the intended
reflexive uses. They do not construct a term of `Hypotheses`.
-/
namespace R44RoundTwoReview
open R44

example (g : RigidMotion) (r : Role) (hne : profileCoefficient r ≠ 0) :
    ¬ CompleteFeatureMate g r g r :=
  R44.no_self_mate g r hne

example (T : Tiling Q) (g : RigidMotion) : ¬ FeatureAdjacent T g g := by
  intro h
  exact h.2.2.1 rfl

example (T : Tiling Q) (g : RigidMotion) : SameFeatureComponent T g g :=
  Relation.ReflTransGen.refl

example (g : RigidMotion) (r : Role) : FeatureContained g r g := by
  exact ⟨r, fun _ hx => hx⟩

example (hR : FeatureContainmentRigidity Q) (T : Tiling Q)
    (g h : RigidMotion) (hg : g ∈ T.placements) (hh : h ∈ T.placements)
    (hne : h ≠ g) (r s : Role)
    (hcontain : featureGraphAt g r ⊆ featureGraphAt h s) :
    CompleteFeatureMate g r h s :=
  hR T g h hg hh (Ne.symm hne) r s hcontain

example (T : Tiling Q) (R : Registration T)
    (g h : RigidMotion) (hg : g ∈ T.placements) (hh : h ∈ T.placements) :
    handedness g = handedness h :=
  R.handedness_eq g h hg hh

example (H : Hypotheses) (T : Tiling Q) :
    CarrierHierarchyNested (carrierHierarchy H T) :=
  (carrier_hierarchy H T).2.2.1

example (H : Hypotheses) (T : Tiling Q) :
    Nonempty (CarrierHierarchy H T) :=
  carrier_hierarchy_exists H T

example (H : Hypotheses) (T : Tiling Q) (K K' : CarrierHierarchy H T) :
    K = K' :=
  carrier_hierarchy_unique H T K K'

example (H : Hypotheses) (T : Tiling Q) :
    Nonempty (GeometricHierarchy H T) :=
  carrierHierarchy_geometric H T

example (H : Hypotheses) (T : Tiling Q) (K : GeometricHierarchy H T)
    (n : Nat) (c : CarrierCell T) :
    K.partition n c ∈ (coarseningIterate H n T).placements :=
  geometric_hierarchy_canonical H T K n c

example (H : Hypotheses) (T : Tiling Q)
    (K K' : GeometricHierarchy H T) : K = K' :=
  geometric_hierarchy_unique H T K K'

example (H : Hypotheses) (T : Tiling Q) (K : GeometricHierarchy H T) :
    K.toCarrier.toGeometric = K :=
  K.toCarrier_toGeometric

/- The nineteen discharged theorems instantiate the exact propositions consumed
at their former `Hypotheses` field sites. -/
example (hball : CompactRegularClosedBall Q) (hcensus : matesCensusCheck = true) :
    RetainedCoreOverlap Q :=
  retained_core_overlap_holds hball hcensus

example : CarrierFeatureFrameReduction :=
  carrier_feature_frame_reduction_holds

example : R44ConeSolidAngleFormula :=
  circular_cone_solid_angle_holds

example : PerTubeHomeomorphisms :=
  per_tube_homeomorphisms_holds

example : FeatureTubeMapsGlue :=
  feature_tube_maps_glue_holds

example : FeatureTubeMapCarriesCarrier :=
  feature_tube_map_carries_carrier_holds

example : FeatureCircularConeContainment Q :=
  feature_circular_cone_containment_holds

example : PlanarAreaCarrierRecovery :=
  planar_area_carrier_recovery_holds

example (hlf : EveryPackingLocallyFinite Q) : ConeSectorBudgets Q :=
  cone_sector_budgets_holds hlf

example (hlf : EveryPackingLocallyFinite Q) (hbudget : ConeSectorBudgets Q)
    (hgeneric : GenericFeaturePartners Q) (hangle : UniformFeatureSolidAngle Q) :
    WholeFeatureCompanions Q :=
  connected_feature_companion_holds hlf hbudget hgeneric hangle

example (hgeneric : GenericFeaturePartners Q) (hwhole : WholeFeatureCompanions Q) :
    FeatureContainmentRigidity Q :=
  feature_containment_rigidity_holds hgeneric hwhole

example (hprofile : profileCanonicalCheck = true)
    (hcensus : matesCensusCheck = true) (hrigid : FeatureContainmentRigidity Q) :
    CompanionPoseDiscrete Q :=
  companion_pose_discrete_holds hprofile hcensus hrigid

example (hwhole : WholeFeatureCompanions Q)
    (hrigid : FeatureContainmentRigidity Q)
    (hdiscrete : CompanionPoseDiscrete Q) (hoverlap : RetainedCoreOverlap Q)
    (hcensus : matesCensusCheck = true) : OnlyRegisteredMates Q :=
  only_registered_mates_holds hwhole hrigid hdiscrete hoverlap hcensus

example (hball : CompactRegularClosedBall Q)
    (hgrid : BaselineComponentCoversGrid Q) : ComponentSolidsCover Q :=
  component_solids_cover_holds hball hgrid

example (hH : HasTubeHomeomorphism) : SmallCollarRealization :=
  small_collar_realization_holds hH

example (hsolid : solidMeshCheck = true) (hangle : meshAngleAuditCheck = true)
    (hprofile : profileCanonicalCheck = true)
    (hdev : deviationsDistinctCheck = true) : CompleteDihedralList Q :=
  complete_dihedral_list_holds hsolid hangle hprofile hdev

example (hbudget : ConeSectorBudgets Q) (hdihedral : CompleteDihedralList Q) :
    GenericFeaturePartners Q :=
  generic_feature_partner_holds hbudget hdihedral

example (hmates : OnlyRegisteredMates Q) (hatlas : atlasCheck = true) :
    BaselineComponentCoversGrid Q :=
  baseline_component_covers_grid_holds hmates hatlas

example (hframes : orientationGroupCheck = true)
    (hcover : ComponentSolidsCover Q) : UnrestrictedAlignment Q :=
  unrestricted_alignment_holds hframes hcover

example : Nonempty (Tiling Q) ∧ ∀ T : Tiling Q,
    Per T = {0} ∧ (Set.univ : Set (Sym T)).encard ≤ 24 :=
  r44_einstein

end R44RoundTwoReview
