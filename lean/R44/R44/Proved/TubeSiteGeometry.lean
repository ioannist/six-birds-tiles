/- -- [compile-fix]
# Tube sites are uniformly separated eighth-grid cubes

A§1 and A-L6.2, ERRATA E6. Native supports are actual coordinate cubes of
half-width eta; no local conical or mesh premise is used. Under registered
poses their centers remain in the eighth grid. Distinct physical sites are
separated by at least 21/200, hence by 1/16. Coincident supports still need
the paired-owner/profile compatibility lemma in AssemblyCollarData.

No admissions and no new atlas or mate enumeration.
-/
import R44.Proved.RegisteredCellGeometry -- [compile-fix: promoted dependency]
import R44.Proved.PerTubeHomeomorphisms -- [compile-fix]

namespace R44.DischargeSites
open Set Generated R44.DischargeGeometry R44.DischargePyramid
open R44.DischargeCells R44.DischargeRegistered
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000 -- [compile-fix]

def cubeAt (c:E3) : Set E3 := {x | ∀i:Fin 3,|x i-c i|≤eta}

theorem native_tube_cube (r:Role) :
    {x | featureTubeSupport r x}=cubeAt (featureCenter r) := by
  ext x
  constructor
  · exact featureTubeSupport_coordinate_bound
  · intro hx
    obtain ⟨i,k,haxis,hcenter⟩ := normal_plane_integer r
    have hr : r.val<nativeFeatures.length := by rw [native_features_length]; exact r.isLt
    have hn : (nativeFeatureData r).normal.get (featureAxis r)=1 ∨
        (nativeFeatureData r).normal.get (featureAxis r)= -1 := by
      have hh := native_feature_normal_axis ⟨r.val,hr⟩
      simpa [nativeFeatureData,getD,hr,featureAxis] using hh
    have h0 := hx (0:Fin 3)
    have h1 := hx (1:Fin 3)
    have h2 := hx (2:Fin 3)
    fin_cases i <;> rcases hn with hn|hn <;>
      rw [haxis] at hn <;> -- [compile-fix begin: specialize the certified normal sign to the selected coordinate]
      simp [featureTubeSupport,featureRadius,featureNormalCoordinate,
        featureTangentAxes,haxis,hn,frameCoordinate,featureNormal,scaledV3,
        max_le_iff,abs_neg]
    all_goals
      constructor
      · constructor <;> assumption
      · first | assumption | (simpa [abs_sub_comm] using h0) |
          (simpa [abs_sub_comm] using h1) | (simpa [abs_sub_comm] using h2)
      -- [compile-fix end]

def center8 (p:Pose) (r:Role) : V3 :=
  (p.frame.act (nativeFeatureData r).center8).add (p.shift.smul 8)

theorem placed_center {m:RigidMotion} {p:Pose}
    (hp:p.frame∈allFrames) (hm:RealizesPose m p) (r:Role) :
    m (featureCenter r)=scaledV3 8 (center8 p r) := by
  have hmap := m.map_vadd (0:E3) (featureCenter r)
  simp only [vadd_eq_add,add_zero] at hmap
  rw [hmap]
  ext i
  have hl := hm.1 (featureCenter r) i
  have ho := hm.2 i
  have hpi := perm_lt_three hp i
  simp only [featureCenter,scaledV3,frameActReal,frameCoordinate] at hl
  rw [dif_pos hpi] at hl
  change (m.linearIsometryEquiv (featureCenter r)) i + (m 0) i = -- [compile-fix]
    (scaledV3 8 (center8 p r)) i -- [compile-fix begin: expose coordinate application through PiLp addition]
  have hl' : (m.linearIsometryEquiv (featureCenter r)) i =
      (p.frame.sign.get i : ℝ) *
        (((nativeFeatureData r).center8.get (p.frame.perm.get i) : ℝ) / 8) := by
    change (m.linearIsometryEquiv
      (WithLp.toLp 2 fun j : Fin 3 =>
        ((nativeFeatureData r).center8.get j : ℝ) / 8)) i = _
    exact hl
  rw [hl', ho]
  fin_cases i <;>
    simp [center8,scaledV3,V3.add,V3.smul,Frame.act,V3.get,N3.get,v] at ho ⊢ <;>
    push_cast <;> ring
  -- [compile-fix end]

theorem cubic_cube_image {m:RigidMotion} {p:Pose}
    (hp:p.frame∈allFrames) (hm:RealizesPose m p) (c:E3) :
    m '' cubeAt c=cubeAt (m c) := by
  have hcoord (x:E3) (i:Fin 3) :
      |m x i-m c i|=|x ⟨p.frame.perm.get i,perm_lt_three hp i⟩-
        c ⟨p.frame.perm.get i,perm_lt_three hp i⟩| := by
    have hx := congrArg (fun v:E3 => v i) (m.map_vadd (0:E3) x)
    have hc := congrArg (fun v:E3 => v i) (m.map_vadd (0:E3) c)
    simp only [vadd_eq_add,add_zero,PiLp.add_apply,hm.1] at hx hc
    rw [hx,hc]
    have hs := DischargeBoxes.sign_pm hp i
    rcases hs with hs|hs <;>
      simp [frameActReal,frameCoordinate,perm_lt_three hp i,hs,abs_sub_comm] <;> -- [compile-fix]
      try { congr 1 <;> ring } -- [compile-fix]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩ i
    rw [hcoord]
    exact hy _
  · intro hx
    refine ⟨m.symm x,?_,m.apply_symm_apply x⟩
    intro j
    obtain ⟨i,hi⟩ := DischargeBoxes.perm_surjective hp j
    have h := hx i
    have hc := hcoord (m.symm x) i
    rw [m.apply_symm_apply x] at hc
    rw [hc] at h
    simpa [hi] using h

theorem placed_support_cube {m:RigidMotion} {p:Pose}
    (hp:p.frame∈allFrames) (hm:RealizesPose m p) (r:Role) :
    m '' {x | featureTubeSupport r x}=cubeAt (scaledV3 8 (center8 p r)) := by
  rw [native_tube_cube,cubic_cube_image hp hm,placed_center hp hm]

private theorem coord_le_dist (x y:E3) (i:Fin 3) : |x i-y i|≤dist x y := by
  have hsq : |(x-y) i| ^ 2 ≤ ‖x-y‖ ^ 2 := by -- [compile-fix begin: derive the coordinate bound from the Euclidean sum of squares]
    rw [EuclideanSpace.norm_sq_eq]
    simpa only [Real.norm_eq_abs] using
      (Finset.single_le_sum (s := Finset.univ)
        (fun j _ => sq_nonneg ‖(x-y) j‖) (Finset.mem_univ i))
  have h := (sq_le_sq₀ (abs_nonneg ((x-y) i)) (norm_nonneg (x-y))).mp hsq
  simpa [dist_eq_norm, Real.norm_eq_abs] using h
  -- [compile-fix end]

/-- Positive separation of distinct sites is explicit and independent of any
choice of owners or polarity. -/
theorem site_separation {a b:V3} (hab:a≠b) {x y:E3}
    (hx:x∈cubeAt (scaledV3 8 a)) (hy:y∈cubeAt (scaledV3 8 b)) :
    (21:ℝ)/200≤dist x y := by
  have hcoord : ∃i:Fin 3,a.get i≠b.get i := by
    by_contra h
    push_neg at h
    apply hab
    cases a; cases b
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    simp [V3.get] at h0 h1 h2
    simp_all
  obtain ⟨i,hi⟩ := hcoord
  have hgap : (1:ℝ)/8≤|(a.get i:ℝ)/8-(b.get i:ℝ)/8| := by
    have hInt : 1≤(a.get i-b.get i).natAbs := by
      have hn : a.get i-b.get i≠0 := sub_ne_zero.mpr hi
      have hp := Int.natAbs_pos.mpr hn
      omega
    have hAbsInt : (1:Int) ≤ |a.get i-b.get i| := by -- [compile-fix begin: bridge natAbs through integer abs before casting to real]
      rw [← Int.natCast_natAbs]
      exact_mod_cast hInt
    have hAbs : (1:ℝ)≤|(a.get i:ℝ)-(b.get i:ℝ)| := by
      exact_mod_cast hAbsInt
    -- [compile-fix end]
    rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<8)]
    linarith
  have hx' : |x i-(a.get i:ℝ)/8|≤eta := hx i
  have hy' : |y i-(b.get i:ℝ)/8|≤eta := hy i
  have htri : |(a.get i:ℝ)/8-(b.get i:ℝ)/8|≤
      |x i-(a.get i:ℝ)/8|+|x i-y i|+|y i-(b.get i:ℝ)/8| := by
    calc
      |(a.get i:ℝ)/8-(b.get i:ℝ)/8| =
          |((a.get i:ℝ)/8-x i)+(x i-y i)+(y i-(b.get i:ℝ)/8)| := by
            congr 1; ring
      _ ≤ |(a.get i:ℝ)/8-x i+(x i-y i)|+|y i-(b.get i:ℝ)/8| := abs_add_le _ _ -- [compile-fix]
      _ ≤ (|(a.get i:ℝ)/8-x i|+|x i-y i|)+|y i-(b.get i:ℝ)/8| :=
        add_le_add (abs_add_le _ _) (le_refl _) -- [compile-fix]
      _ = _ := by rw [abs_sub_comm ((a.get i:ℝ)/8) (x i)]
  have hdist := coord_le_dist x y i
  norm_num [eta] at hx' hy'
  linarith

end
end R44.DischargeSites
