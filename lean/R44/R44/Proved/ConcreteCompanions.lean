/- -- [compile-fix: promoted to Proved after exchange 7]
# Concrete local companion facts, assembled without a Hypotheses record

A§2--5. This is an explicit dependency hub. It uses the shared MeshSemantics
bridge through CompleteDihedralList and the GenericFeaturePartner theorem.
Both bridges are admission-free after exchange 7. -- [compile-fix]
There is no new assumption, axiom or admission
and no circular use of a global-alignment/hierarchy field.
-/
import R44.Proved.CompleteDihedralList -- [compile-fix: promoted after exchange 7]
import R44.Proved.GenericFeaturePartner -- [compile-fix: promoted after exchange 7]
import R44.Proved.ConnectedFeatureCompanion -- [compile-fix]
import R44.Proved.FeatureContainmentRigidity -- [compile-fix]
import R44.Proved.CompanionPoseDiscrete -- [compile-fix]
import R44.Proved.OnlyRegisteredMates -- [compile-fix]
import R44.Proved.RetainedCoreOverlap -- [compile-fix: direct dependency after cycle removal]

namespace R44
open Set Generated
noncomputable section

-- [compile-fix begin: move the sorry-free shell-ownership bridge into the
-- Proved layer so the promoted endpoint chain does not import LogicalSpine]
private theorem shell_v3_eq (a b : V3) (hx : a.x = b.x) (hy : a.y = b.y)
    (hz : a.z = b.z) : a = b := by
  rcases a with ⟨ax, ay, az⟩
  rcases b with ⟨bx, byv, bz⟩
  simp_all

private theorem nativeFeatureData_mem_shell (r : Role) :
    nativeFeatureData r ∈ nativeFeatures := by
  have hr : r.val < nativeFeatures.length := by
    rw [native_features_length]
    exact r.isLt
  rw [show nativeFeatureData r = nativeFeatures[r.val] by
    simp [nativeFeatureData, getD, hr]]
  exact List.get_mem nativeFeatures ⟨r.val, hr⟩

private theorem frame_mem_of_registeredShellCellControls_shell
    (hcontrols : registeredShellCellControlsCheck = true)
    {p : Pose} (hp : p ∈ legalContacts) : p.frame ∈ allFrames := by
  simp only [registeredShellCellControlsCheck, Bool.and_eq_true] at hcontrols
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hcontrols.1.1.2 p hp)

set_option maxHeartbeats 2000000 in
private theorem featureMateFormula_center8_shell {m : RigidMotion} {p : Pose}
    {r s : Role} (hpframe : p.frame ∈ allFrames) (hm : RealizesPose m p)
    (hf : FeatureMateFormula m r s) :
    (p.frame.act (nativeFeatureData s).center8).add (p.shift.smul 8) =
      (nativeFeatureData r).center8 := by
  rcases hm with ⟨hlin, horigin⟩
  rcases hf with ⟨_, _, _, hcenter⟩
  have hc (i : Fin 3) :
      (m 0) i = featureCenter r i -
        (m.linearIsometryEquiv (featureCenter s)) i := by
    rw [hcenter]
    rfl
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  rw [hlin (featureCenter s) 0] at hc0
  rw [hlin (featureCenter s) 1] at hc1
  rw [hlin (featureCenter s) 2] at hc2
  unfold allFrames at hpframe
  obtain ⟨perm, hperm, hpframe⟩ := List.mem_flatMap.mp hpframe
  obtain ⟨sign, hsign, hpframe⟩ := List.mem_map.mp hpframe
  rcases p with ⟨pf, ⟨tx, ty, tz⟩⟩
  simp only at hpframe
  subst pf
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    apply shell_v3_eq <;>
    simp [featureCenter, scaledV3, frameActReal, frameCoordinate,
      Frame.act, N3.get, V3.add, V3.smul, V3.get, fr, n3, v,
      horigin] at hc0 hc1 hc2 ⊢ <;>
    apply Int.cast_injective (α := ℝ) <;>
    push_cast <;>
    linarith

set_option maxHeartbeats 2000000 in
private theorem featureMateFormula_normal_shell {m : RigidMotion} {p : Pose}
    {r s : Role} (hpframe : p.frame ∈ allFrames) (hm : RealizesPose m p)
    (hf : FeatureMateFormula m r s) :
    p.frame.act (nativeFeatureData s).normal =
      (nativeFeatureData r).normal.neg := by
  rcases hm with ⟨hlin, _⟩
  rcases hf with ⟨_, _, hnormal, _⟩
  have hn (i : Fin 3) :
      featureNormal r i =
        -(m.linearIsometryEquiv (featureNormal s)) i := by
    rw [hnormal]
    rfl
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  rw [hlin (featureNormal s) 0] at hn0
  rw [hlin (featureNormal s) 1] at hn1
  rw [hlin (featureNormal s) 2] at hn2
  unfold allFrames at hpframe
  obtain ⟨perm, hperm, hpframe⟩ := List.mem_flatMap.mp hpframe
  obtain ⟨sign, hsign, hpframe⟩ := List.mem_map.mp hpframe
  rcases p with ⟨pf, pt⟩
  simp only at hpframe
  subst pf
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    apply shell_v3_eq <;>
    simp [featureNormal, scaledV3, frameActReal, frameCoordinate,
      Frame.act, N3.get, V3.neg, V3.smul, V3.get, fr, n3, v]
      at hn0 hn1 hn2 ⊢ <;>
    norm_cast at hn0 hn1 hn2 <;>
    omega

private theorem featureMateFormula_coefficient_shell {m : RigidMotion} {r s : Role}
    (hf : FeatureMateFormula m r s) :
    (nativeFeatureData s).coefficient =
      -(nativeFeatureData r).coefficient := by
  rcases hf with ⟨_, hcoeff, _, _⟩
  unfold profileCoefficient at hcoeff
  omega

/-- The literal panel table turns the centre, normal, and polarity equations
    of a legal complete-feature mate into ownership of that feature's unique
    far-side shell cell by the companion's baseline chair. -/
theorem formula_mate_owns_far_cell
    (hcontrols : registeredShellCellControlsCheck = true)
    {m : RigidMotion} {p : Pose} {r s : Role}
    (hp : p ∈ legalContacts) (hm : RealizesPose m p)
    (hf : FeatureMateFormula m r s) :
    featureFarCell (nativeFeatureData r) ∈ body p := by
  have hpframe := frame_mem_of_registeredShellCellControls_shell hcontrols hp
  have hcenter := featureMateFormula_center8_shell hpframe hm hf
  have hnormal := featureMateFormula_normal_shell hpframe hm hf
  have hcoeff := featureMateFormula_coefficient_shell hf
  have hr := nativeFeatureData_mem_shell r
  have hs := nativeFeatureData_mem_shell s
  simp only [registeredShellCellControlsCheck, Bool.and_eq_true] at hcontrols
  have hpcheck := List.all_eq_true.mp hcontrols.1.2 p hp
  have hrcheck := List.all_eq_true.mp hpcheck (nativeFeatureData r) hr
  have hscheck := List.all_eq_true.mp hrcheck (nativeFeatureData s) hs
  simp [hcenter, hnormal, hcoeff] at hscheck
  exact hscheck

end
end R44
-- [compile-fix end]

namespace R44.DischargeConcrete
open DischargePolyhedral DischargeFeatureGraphs Generated -- [compile-fix]
noncomputable section

theorem dihedrals : CompleteDihedralList Q :=
  complete_dihedral_list_holds solid_mesh_exact mesh_angle_audit
    profile_canonical deviations_distinct.1

theorem budgets : ConeSectorBudgets Q :=
  cone_sector_budgets_holds (local_finiteness Q_object)

theorem generic : GenericFeaturePartners Q :=
  generic_feature_partner_holds budgets dihedrals

theorem whole : WholeFeatureCompanions Q :=
  whole_from_generic (local_finiteness Q_object) budgets generic

theorem rigidity : FeatureContainmentRigidity Q := by
  exact feature_containment_rigidity_holds generic whole
  -- The exact accepted exchange-4 endpoint takes generic, then whole.

theorem discrete : CompanionPoseDiscrete Q :=
  companion_pose_discrete_holds profile_canonical mates_census rigidity

theorem only_mates : OnlyRegisteredMates Q :=
  only_registered_mates_holds whole rigidity discrete
    (retained_core_overlap_holds Q_object mates_census) mates_census -- [compile-fix]

/-- Actual root role, actual distinct companion, and far-side cell owner. -/
theorem far_owner (T : Tiling Q) {g : RigidMotion}
    (hg : g∈T.placements) (r : Role) :
    ∃h∈T.placements,h≠g ∧ ∃s : Role,CompleteFeatureMate g r h s ∧
      ∃p∈legalContacts,RealizesPose (relativeMotion g h) p ∧
        featureFarCell (nativeFeatureData r)∈body p := by
  obtain ⟨h,hh,hne,_,⟨s,hsub⟩,_⟩ := whole T g hg r
  have hm := rigidity T g h hg hh (Ne.symm hne) r s hsub
  obtain ⟨p,hp,hreal⟩ := only_mates T g h hg hh (Ne.symm hne) ⟨r,s,hm⟩
  exact ⟨h,hh,hne,s,hm,p,hp,hreal,
    formula_mate_owns_far_cell registered_shell_cell_controls hp hreal
      (discrete.2 T g h hg hh (Ne.symm hne) r s hm)⟩

end
end R44.DischargeConcrete
