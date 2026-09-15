/- -- [compile-fix]
# Whole-feature matching implies the center/normal/eighth-grid formula

Written source: proof/ALIGNMENT_PROOF.md A-C4.4, after A-L4.3 and ERRATA E1.
This is the geometric half of CompanionPoseDiscrete. It uses equality of the
actual feature graphs and opposite coefficients, not an assumed registered
placement. Both handednesses are included in the 48 literal cubic frames.
The finite census interpretation is separate. No mathematical admissions.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.CubicFrameAlgebra -- [compile-fix]
import R44.Proved.FeatureContainmentRigidity -- [compile-fix]

namespace R44.DischargePyramid
open Set R44.Generated R44.DischargeGeometry R44.DischargeCharts
noncomputable section
set_option maxHeartbeats 0

/-- Multiplication of rigid motions is composition also on their set images. -/
theorem rigid_image_mul (g h : RigidMotion) (S : Set E3) :
    (g*h) '' S=g '' (h '' S) := by
  rw [Set.image_image]
  rfl

/-- The integer literal action commutes with division of all coordinates by d. -/
theorem frame_on_scaled (A : E3 ≃ₗᵢ[ℝ] E3) (f : Frame)
    (hf : f∈allFrames) (hA : ∀x i,A x i=frameActReal f x i)
    (d : ℝ) (c : V3) : A (scaledV3 d c)=scaledV3 d (f.act c) := by
  ext i
  rw [hA]
  have hi := perm_lt_three hf i
  rw [frameActReal,frameCoordinate_of_lt _ hi]
  have hget : (f.act c).get i=f.sign.get i*c.get (f.perm.get i) := by
    fin_cases i <;> rfl
  simp only [scaledV3,hget,Int.cast_mul] -- [compile-fix]
  ring
  -- API?: WithLp.toLp_apply is definitional evaluation of scaledV3;
  -- use change/simp only [scaledV3] if the pinned simplifier has no such lemma.

/-- Coordinates of a motion normalized by the native source and target charts. -/
theorem normalized_mate_graph (m : RigidMotion) (u v : Role)
    (hg : m '' nativeFeatureGraph v=nativeFeatureGraph u) :
    ((chartPose u)⁻¹*m*chartPose v) '' G ((profileCoefficient v:ℝ)/10000)
      =G ((profileCoefficient u:ℝ)/10000) := by
  rw [rigid_image_mul,rigid_image_mul,chart_graph,hg,← chart_graph u]
  exact (chartPose u).toEquiv.symm_image_image _ -- [compile-fix]

/-- Unnormalize the center and normal recovered from canonical pyramid graphs. -/
theorem mate_center_normal_frame (m : RigidMotion) (u v : Role)
    (hg : m '' nativeFeatureGraph v=nativeFeatureGraph u)
    (hc : profileCoefficient u = -profileCoefficient v) :
    m (featureCenter v)=featureCenter u ∧
      m.linearIsometryEquiv (featureNormal v) = -featureNormal u ∧
      CubicLinear m.linearIsometryEquiv := by
  let n : RigidMotion := (chartPose u)⁻¹*m*chartPose v
  have hreal : ((profileCoefficient u:ℝ)/10000) =
      -((profileCoefficient v:ℝ)/10000) := by
    rw [hc,Int.cast_neg]; ring
  have heq := normalized_mate_graph m u v hg
  rw [hreal] at heq
  change n '' G ((profileCoefficient v:ℝ)/10000) =
    G (-((profileCoefficient v:ℝ)/10000)) at heq
  have hn0 : n 0=0 := graph_eq_center (native_small v)
    ⟨neg_ne_zero.mpr (native_small v).1,by simpa using (native_small v).2⟩ n heq
  have hn2 := graph_eq_normal (native_small v) n heq
  have hnframe := graph_eq_cubic (native_small v) n heq
  have hfactor : m=chartPose u*n*(chartPose v)⁻¹ := by dsimp [n]; group
  have hcenter : m (featureCenter v)=featureCenter u := by
    have he := congrArg (fun x:E3 => chartPose u x) hn0
    simpa [n,AffineIsometryEquiv.coe_mul,Function.comp_def,
      chartPose_apply,chartEquiv_apply,chartLinear_apply] using he
  have hnlin : n.linearIsometryEquiv =
      (chartEquiv u)⁻¹*m.linearIsometryEquiv*(chartEquiv v) := by
    -- API?: linear part preserves multiplication/inverse of affine isometries.
    rfl -- [compile-fix]
  have hnormal : m.linearIsometryEquiv (featureNormal v) = -featureNormal u := by
    have he := congrArg (chartEquiv u) hn2
    rw [hnlin] at he
    simpa [chartEquiv_apply,chartLinear_apply, -- [compile-fix]
      pt,map_neg] using he
  have hlinfactor : m.linearIsometryEquiv =
      chartEquiv u*n.linearIsometryEquiv*(chartEquiv v)⁻¹ := by
    rw [hnlin]; group
  refine ⟨hcenter,hnormal,?_⟩
  rw [hlinfactor]
  exact cubic_mul (cubic_mul (chart_cubic u) hnframe) (cubic_inv (chart_cubic v))

/-- A genuine complete native feature match has precisely the discrete
formula asserted in A-C4.4, with no tiling or alignment premise. -/
theorem native_complete_mate_formula (m : RigidMotion) (u v : Role)
    (hg : m '' nativeFeatureGraph v=nativeFeatureGraph u)
    (hc : profileCoefficient u = -profileCoefficient v) :
    FeatureMateFormula m u v := by
  obtain ⟨hcenter,hnormal,f,hf,hlinear⟩ := mate_center_normal_frame m u v hg hc
  have horigin : m 0=featureCenter u-m.linearIsometryEquiv (featureCenter v) := by
    have hh := m.map_vadd (0:E3) (featureCenter v)
    simp only [vadd_eq_add,add_zero] at hh
    rw [hcenter] at hh
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hh.symm)
  have hs : m 0=scaledV3 8 ((nativeFeatureData u).center8.sub
      (f.act (nativeFeatureData v).center8)) := by
    rw [horigin,featureCenter,featureCenter,frame_on_scaled _ f hf hlinear]
    ext i
    fin_cases i <;> simp [scaledV3,V3.sub,V3.get,R44.v] <;> ring
  refine ⟨⟨f,hf,hlinear,?_⟩,hc,by simpa using (congrArg Neg.neg hnormal).symm,horigin⟩ -- [compile-fix]
  intro i
  refine ⟨((nativeFeatureData u).center8.sub
    (f.act (nativeFeatureData v).center8)).get i,?_⟩
  rw [hs]
  rfl

/-- The geometric conjunct of the frozen CompanionPoseDiscrete proposition.
Distinctness has already been used to obtain a CompleteFeatureMate; this
part only transports that actual mate into native relative coordinates. -/
theorem tiling_complete_mate_formula
    (T : Tiling Q) (g h : RigidMotion) (_hg : g∈T.placements)
    (_hh : h∈T.placements) (_hne : g≠h) (r s : Role)
    (hm : CompleteFeatureMate g r h s) :
    FeatureMateFormula (relativeMotion g h) r s := by
  apply native_complete_mate_formula _ r s _ hm.2.2
  have hg := congrArg (fun E:Set E3 => g.symm '' E) hm.1 -- [compile-fix]
  simpa [featureGraphAt,relativeMotion,rigid_image_mul,Set.image_image,
    AffineIsometryEquiv.coe_mul,Function.comp_def] using hg.symm

end
end R44.DischargePyramid
