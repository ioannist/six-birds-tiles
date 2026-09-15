/- -- [compile-fix]
# Metric carrier recovery for the fixed R44 solid

Relation to written proof: proof/PROOFS_registered.md R§6 and ERRATA E5.
IMPORTANT METHOD DEVIATION: the written proof recovers planes by intrinsic
planar area. This file proves the SAME frozen carrier-recovery conclusion
by diameter endpoints instead. It does not claim that Hausdorff-area
calculations have been formalized. It is an explicit alternative derivation,
not a modification of Q or of any frozen proposition.

Any point in a feature tube is strictly less than sqrt(12) from every point
of Q: one coordinate separation is ≤21/10, the other two ≤9/5, giving square
sum ≤1089/100<12. Diameter pairs therefore lie in the undeformed carrier.
The six antipodal carrier corners recover the center and axes. The preserved
missing corner forbids reversal. This avoids the admitted area bridge.

No mathematical admissions. The finite splits below read only the literal
panel coordinates and six corner possibilities, never rerun a certificate.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.CarrierSymmetries -- [compile-fix]

namespace R44.DischargeMetricCarrier
open Set R44.Generated R44.DischargeGeometry
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def ctr : E3 := WithLp.toLp 2 fun _ => 1
private def a0 : E3 := cellCorner (v 2 0 0)
private def a1 : E3 := cellCorner (v 0 2 0)
private def a2 : E3 := cellCorner (v 0 0 2)
private def b0 : E3 := cellCorner (v 0 2 2)
private def b1 : E3 := cellCorner (v 2 0 2)
private def b2 : E3 := cellCorner (v 2 2 0)

private theorem dist_sq_coords (x y : E3) :
    dist x y ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 + (x 2 - y 2)^2 := by
  simp [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ,
    Real.norm_eq_abs, sq_abs, add_assoc]

private theorem coord_extreme {a b : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 2) (hb : 0 ≤ b ∧ b ≤ 2)
    (h : (a-b)^2 = 4) :
    (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by
  have hf : (a-b-2)*(a-b+2) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h' | h'
  · right; constructor <;> linarith
  · left; constructor <;> linarith

private theorem coord_sq_le {a b : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 2) (hb : 0 ≤ b ∧ b ≤ 2) : (a-b)^2 ≤ 4 := by
  have hminus : 0 ≤ 2-(a-b) := by linarith
  have hplus : 0 ≤ 2+(a-b) := by linarith
  nlinarith [mul_nonneg hminus hplus]

private theorem diameter_coordinate_extremes {x y : E3}
    (hx : x ∈ P) (hy : y ∈ P) (hd : dist x y ^ 2 = 12) :
    ∀ i : Fin 3, (x i = 0 ∧ y i = 2) ∨ (x i = 2 ∧ y i = 0) := by
  have hxb := (mem_P_iff_box_notch x).mp hx |>.1
  have hyb := (mem_P_iff_box_notch y).mp hy |>.1
  have h0 := coord_sq_le (hxb 0) (hyb 0)
  have h1 := coord_sq_le (hxb 1) (hyb 1)
  have h2 := coord_sq_le (hxb 2) (hyb 2)
  rw [dist_sq_coords] at hd
  -- [compile-fix begin: isolate each coordinate equality before the finite index split]
  have hs0 : (x 0 - y 0) ^ 2 = 4 := by linarith
  have hs1 : (x 1 - y 1) ^ 2 = 4 := by linarith
  have hs2 : (x 2 - y 2) ^ 2 = 4 := by linarith
  intro i
  fin_cases i
  · simpa using coord_extreme (hxb 0) (hyb 0) hs0
  · simpa using coord_extreme (hxb 1) (hyb 1) hs1
  · simpa using coord_extreme (hxb 2) (hyb 2) hs2
  -- [compile-fix end]

private theorem diameter_pair_sum {x y : E3}
    (hx : x ∈ P) (hy : y ∈ P) (hd : dist x y ^ 2 = 12) :
    x + y = (2 : ℝ) • ctr := by
  have h := diameter_coordinate_extremes hx hy hd
  apply PiLp.ext
  intro i
  rcases h i with h | h <;> simp [ctr, h.1, h.2]

private theorem diameter_endpoint {x y : E3}
    (hx : x ∈ P) (hy : y ∈ P) (hd : dist x y ^ 2 = 12) :
    x = a0 ∨ x = a1 ∨ x = a2 ∨ x = b0 ∨ x = b1 ∨ x = b2 := by
  have h := diameter_coordinate_extremes hx hy hd
  have hxnot := (mem_P_iff_box_notch x).mp hx |>.2
  have hynot := (mem_P_iff_box_notch y).mp hy |>.2
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  all_goals
    solve
    | (exfalso
       obtain ⟨i, hi⟩ := hxnot
       fin_cases i <;> simp_all)
    | (exfalso
       obtain ⟨i, hi⟩ := hynot
       fin_cases i <;> simp_all)
    | (apply Or.inl; apply PiLp.ext; intro i; fin_cases i <;>
        simp [a0, cellCorner, V3.get, v, h0.1, h1.1, h2.1])
    | (apply Or.inr; apply Or.inl; apply PiLp.ext; intro i; fin_cases i <;>
        simp [a1, cellCorner, V3.get, v, h0.1, h1.1, h2.1])
    | (apply Or.inr; apply Or.inr; apply Or.inl; apply PiLp.ext; intro i; fin_cases i <;>
        simp [a2, cellCorner, V3.get, v, h0.1, h1.1, h2.1])
    | (apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl;
        apply PiLp.ext; intro i; fin_cases i <;>
        simp [b0, cellCorner, V3.get, v, h0.1, h1.1, h2.1])
    | (apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl;
        apply PiLp.ext; intro i; fin_cases i <;>
        simp [b1, cellCorner, V3.get, v, h0.1, h1.1, h2.1])
    | (apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr;
        apply PiLp.ext; intro i; fin_cases i <;>
        simp [b2, cellCorner, V3.get, v, h0.1, h1.1, h2.1])

private theorem rigid_apply (g : RigidMotion) (x : E3) :
    g x = g.linearIsometryEquiv x + g 0 := by
  simpa only [vadd_eq_add, add_zero] using g.map_vadd (0 : E3) x

private theorem three_anchor_sum (g : RigidMotion) :
    g a0 + g a1 + g a2 = (2 : ℝ) • g ctr + g 0 := by
  have ha : a0 + a1 + a2 = (2 : ℝ) • ctr := by
    apply PiLp.ext; intro i; fin_cases i <;>
      norm_num [a0, a1, a2, ctr, cellCorner, V3.get, v]
  calc
    _ = g.linearIsometryEquiv (a0 + a1 + a2) + (3 : ℝ) • g 0 := by
      -- [compile-fix begin: use the accepted affine expansion without recursive simp]
      rw [rigid_apply g a0, rigid_apply g a1, rigid_apply g a2,
        map_add, map_add]
      module
      -- [compile-fix end]
    _ = (2 : ℝ) • g ctr + g 0 := by
      rw [ha, map_smul, rigid_apply g ctr, smul_add]
      module -- [compile-fix]


private theorem center_in_box (r : Role) (i : Fin 3) :
    0 ≤ featureCenter r i ∧ featureCenter r i ≤ 2 := by
  -- [compile-fix begin: derive coordinate bounds from the accepted finite chart classifier]
  have center_eq (j : Fin 3) :
      featureCenter r j = ((nativeFeatureData r).center8.get j : ℝ) / 8 := by
    simp [featureCenter, scaledV3]
  have from_int_bounds (j : Fin 3)
      (hl : 0 ≤ (nativeFeatureData r).center8.get j)
      (hu : (nativeFeatureData r).center8.get j ≤ 16) :
      0 ≤ featureCenter r j ∧ featureCenter r j ≤ 2 := by
    rw [center_eq]
    have hl' : (0 : ℝ) ≤ ((nativeFeatureData r).center8.get j : ℝ) := by
      exact_mod_cast hl
    have hu' : ((nativeFeatureData r).center8.get j : ℝ) ≤ (16 : ℝ) := by
      exact_mod_cast hu
    constructor <;> norm_num <;> linarith
  obtain ⟨j, hcase⟩ := native_feature_chart_classification r
  dsimp only at hcase
  rcases hcase with hneg | hnotch | houter
  · rcases hneg with ⟨_, hc, htan⟩
    by_cases hij : i = j
    · subst i
      exact from_int_bounds j (by omega) (by omega)
    · have hi := htan i hij
      exact from_int_bounds i (by omega) (by omega)
  · rcases hnotch with ⟨_, hc, htan⟩
    by_cases hij : i = j
    · subst i
      exact from_int_bounds j (by omega) (by omega)
    · have hi := htan i hij
      exact from_int_bounds i (by omega) (by omega)
  · rcases houter with ⟨_, hc, htan, _⟩
    by_cases hij : i = j
    · subst i
      exact from_int_bounds j (by omega) (by omega)
    · have hi := htan i hij
      exact from_int_bounds i (by omega) (by omega)
  -- [compile-fix end]

private def boxBound (x : E3) : Prop :=
  ∀ i : Fin 3, -eta ≤ x i ∧ x i ≤ 2+eta

private theorem tube_box (r : Role) {x : E3} (hx : featureTubeSupport r x) :
    boxBound x := by
  intro i
  have h := abs_le.mp (featureTubeSupport_coordinate_bound hx i)
  have hc := center_in_box r i
  exact ⟨by linarith,by linarith⟩

private theorem Q_box {x : E3} (hx : x ∈ Q) : boxBound x := by
  rcases hx with ⟨hxP,_⟩ | ⟨r,_,ht,_⟩
  · intro i
    have hi := (mem_P_iff_box_notch x).mp hxP |>.1
    have hη : 0 ≤ eta := by norm_num [eta]
    exact ⟨by linarith [(hi i).1],by linarith [(hi i).2]⟩
  · exact tube_box r ht

private def interiorCoordinate (a : ℝ) : Prop := 6/25 ≤ a ∧ a ≤ 44/25

/-- Each tube avoids edges of its native panel by at least 6/25. -/
private theorem two_interior_coordinates (r : Role) {x : E3}
    (hx : featureTubeSupport r x) :
    (interiorCoordinate (x 1) ∧ interiorCoordinate (x 2)) ∨
    (interiorCoordinate (x 0) ∧ interiorCoordinate (x 2)) ∨
    (interiorCoordinate (x 0) ∧ interiorCoordinate (x 1)) := by
  -- [compile-fix begin: use tangent-coordinate bounds from the accepted chart classifier]
  obtain ⟨i, hcase⟩ := native_feature_chart_classification r
  dsimp only at hcase
  have htan : ∀ j : Fin 3, j ≠ i →
      2 ≤ (nativeFeatureData r).center8.get j ∧
        (nativeFeatureData r).center8.get j ≤ 14 := by
    intro j hji
    rcases hcase with hneg | hnotch | houter
    · exact hneg.2.2 j hji
    · have hj := hnotch.2.2 j hji
      exact ⟨by omega, hj.2⟩
    · exact houter.2.2.1 j hji
  have interior_of (j : Fin 3) (hji : j ≠ i) : interiorCoordinate (x j) := by
    have hj := featureTubeSupport_coordinate_bound hx j
    have hc := htan j hji
    have hcl : (2 : ℝ) ≤ ((nativeFeatureData r).center8.get j : ℝ) := by
      exact_mod_cast hc.1
    have hcu : ((nativeFeatureData r).center8.get j : ℝ) ≤ (14 : ℝ) := by
      exact_mod_cast hc.2
    have hj' :
        |x j - ((nativeFeatureData r).center8.get j : ℝ) / 8| ≤ eta := by
      simpa [featureCenter, scaledV3] using hj
    rw [abs_le] at hj'
    constructor <;> norm_num [interiorCoordinate, eta] at * <;> linarith
  fin_cases i
  · exact Or.inl ⟨interior_of 1 (by decide), interior_of 2 (by decide)⟩
  · exact Or.inr (Or.inl ⟨interior_of 0 (by decide), interior_of 2 (by decide)⟩)
  · exact Or.inr (Or.inr ⟨interior_of 0 (by decide), interior_of 1 (by decide)⟩)
  -- [compile-fix end]

private theorem sq_of_interval {a b c : ℝ} (h : -c ≤ a-b ∧ a-b ≤ c) :
    (a-b)^2 ≤ c^2 := by
  nlinarith [mul_nonneg (show 0 ≤ c-(a-b) by linarith [h.2])
    (show 0 ≤ c+(a-b) by linarith [h.1])]

/-- All pairs involving the closed support of any feature are strictly
below the carrier diameter. Using the support rather than just the edited
material also covers negative-feature recesses. -/
theorem tube_distance_strict (r : Role) {x y : E3}
    (hx : featureTubeSupport r x) (hy : y ∈ Q) : dist x y ^ 2 < 12 := by
  have hxb := tube_box r hx
  have hyb := Q_box hy
  have hwide (i : Fin 3) : (x i-y i)^2 ≤ (21/10 : ℝ)^2 := by
    apply sq_of_interval
    have hxi := hxb i
    have hyi := hyb i
    norm_num [eta] at hxi hyi
    exact ⟨by linarith,by linarith⟩
  have hnarrow (i : Fin 3) (hi : interiorCoordinate (x i)) :
      (x i-y i)^2 ≤ (9/5 : ℝ)^2 := by
    apply sq_of_interval
    have hyi := hyb i
    norm_num [eta] at hyi
    rcases hi with ⟨hxl,hxu⟩
    exact ⟨by linarith,by linarith⟩
  rw [dist_sq_coords]
  rcases two_interior_coordinates r hx with ⟨h1,h2⟩ | ⟨h0,h2⟩ | ⟨h0,h1⟩
  · nlinarith [hwide 0,hnarrow 1 h1,hnarrow 2 h2]
  · nlinarith [hnarrow 0 h0,hwide 1,hnarrow 2 h2]
  · nlinarith [hnarrow 0 h0,hnarrow 1 h1,hwide 2]

private theorem corner_outside {x : E3} (hx : ∀ i : Fin 3, x i=0 ∨ x i=2)
    (r : Role) : ¬ featureTubeSupport r x := by
  intro ht
  have hnot (i : Fin 3) (h : interiorCoordinate (x i)) : False := by
    rcases hx i with hi | hi <;> rcases h with ⟨hl,hu⟩ <;> rw [hi] at hl hu <;> norm_num at *
  rcases two_interior_coordinates r ht with ⟨h1,_⟩ | ⟨h0,_⟩ | ⟨h0,_⟩
  · exact hnot 1 h1
  · exact hnot 0 h0
  · exact hnot 0 h0

private theorem corner_Q_iff_P (x : E3) (hx : ∀ i : Fin 3, x i=0 ∨ x i=2) :
    x ∈ Q ↔ x ∈ P := mem_Q_iff_outside (corner_outside hx)

/-- Diameter equality forces both endpoints outside every edit support. -/
theorem diameter_pair_in_carrier {x y : E3} (hx : x ∈ Q) (hy : y ∈ Q)
    (hd : dist x y ^ 2 = 12) : x ∈ P ∧ y ∈ P := by
  have houtx : ∀ r, ¬ featureTubeSupport r x := by
    intro r ht
    have hs := tube_distance_strict r ht hy
    linarith
  have houty : ∀ r, ¬ featureTubeSupport r y := by
    intro r ht
    have hs := tube_distance_strict r ht hx
    rw [dist_comm] at hs
    linarith
  exact ⟨(mem_Q_iff_outside houtx).mp hx,(mem_Q_iff_outside houty).mp hy⟩

private theorem six_corners_Q :
    a0 ∈ Q ∧ a1 ∈ Q ∧ a2 ∈ Q ∧ b0 ∈ Q ∧ b1 ∈ Q ∧ b2 ∈ Q := by
  have hc (x : E3) (h : ∀ i : Fin 3, x i=0 ∨ x i=2) (hP : x ∈ P) : x ∈ Q :=
    (corner_Q_iff_P x h).mpr hP
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals
    apply hc
    · intro i
      fin_cases i <;> norm_num [a0,a1,a2,b0,b1,b2,cellCorner,V3.get,v]
    · norm_num [mem_P_iff_coordinates,a0,a1,a2,b0,b1,b2,cellCorner,V3.get,v]

private theorem origin_Q : (0 : E3) ∈ Q := by
  apply (corner_Q_iff_P 0 (by simp)).mpr
  norm_num [mem_P_iff_coordinates]

private theorem center_fixed_Q {g : RigidMotion} (hg : g '' Q = Q) :
    g ctr = ctr := by
  have hsend (x : E3) (hx : x ∈ Q) : g x ∈ Q := by
    rw [← hg]; exact ⟨x,hx,rfl⟩
  have ha : a0 ∈ Q := six_corners_Q.1
  have hb : b0 ∈ Q := six_corners_Q.2.2.2.1
  have hd : dist a0 b0 ^ 2 = 12 := by
    norm_num [dist_sq_coords,a0,b0,cellCorner,V3.get,v]
  have hgd : dist (g a0) (g b0)^2 = 12 := by simpa only [g.isometry.dist_eq] using hd
  have hP := diameter_pair_in_carrier (hsend a0 ha) (hsend b0 hb) hgd
  have hsum := diameter_pair_sum hP.1 hP.2 hgd
  have horig : a0+b0 = (2:ℝ) • ctr := by
    apply PiLp.ext; intro i; fin_cases i <;> norm_num [a0,b0,ctr,cellCorner,V3.get,v]
  rw [rigid_apply g a0,rigid_apply g b0] at hsum
  have hlin : g.linearIsometryEquiv a0+g.linearIsometryEquiv b0 =
      (2:ℝ) • g.linearIsometryEquiv ctr := by
    rw [← map_add,horig,map_smul]
  apply PiLp.ext
  intro i
  have hs := congrArg (fun z : E3 => z i) hsum
  have hl := congrArg (fun z : E3 => z i) hlin
  rw [rigid_apply g ctr]
  change (g.linearIsometryEquiv ctr) i + (g 0) i = ctr i -- [compile-fix]
  change (g.linearIsometryEquiv a0) i+(g 0) i+
    ((g.linearIsometryEquiv b0) i+(g 0) i)=2*ctr i at hs
  change (g.linearIsometryEquiv a0) i+(g.linearIsometryEquiv b0) i=
    2*(g.linearIsometryEquiv ctr) i at hl
  linarith

/-- The six native frames are obtained from Q itself, without first assuming carrier recovery. -/
theorem Q_self_isometry_frame {g : RigidMotion} (hg : g '' Q = Q) :
    ∃ p ∈ coordinatePermutations,
      RealizesPose g (po (fr p.x p.y p.z 1 1 1) (v 0 0 0)) := by
  have hsend : ∀ x ∈ Q, g x ∈ Q := by
    intro x hx; rw [← hg]; exact ⟨x, hx, rfl⟩
  have hc := center_fixed_Q hg
  have hpair (a b : E3) (ha : a ∈ Q) (hb : b ∈ Q)
      (hd : dist a b ^ 2 = 12) :
      g a = a0 ∨ g a = a1 ∨ g a = a2 ∨ g a = b0 ∨ g a = b1 ∨ g a = b2 := by
    have hgd : dist (g a) (g b)^2 = 12 := by
      simpa only [g.isometry.dist_eq] using hd
    have hP := diameter_pair_in_carrier (hsend a ha) (hsend b hb) hgd
    exact diameter_endpoint hP.1 hP.2 hgd
  have hm0 := hpair a0 b0 six_corners_Q.1 six_corners_Q.2.2.2.1
    (by norm_num [dist_sq_coords,a0,b0,cellCorner,V3.get,v])
  have hm1 := hpair a1 b1 six_corners_Q.2.1 six_corners_Q.2.2.2.2.1
    (by norm_num [dist_sq_coords,a1,b1,cellCorner,V3.get,v])
  have hm2 := hpair a2 b2 six_corners_Q.2.2.1 six_corners_Q.2.2.2.2.2
    (by norm_num [dist_sq_coords,a2,b2,cellCorner,V3.get,v])
  have hd01 : dist (g a0) (g a1)^2 = 8 := by
    rw [g.isometry.dist_eq]; norm_num [dist_sq_coords, a0, a1, cellCorner, V3.get, v]
  have hd02 : dist (g a0) (g a2)^2 = 8 := by
    rw [g.isometry.dist_eq]; norm_num [dist_sq_coords, a0, a2, cellCorner, V3.get, v]
  have hd12 : dist (g a1) (g a2)^2 = 8 := by
    rw [g.isometry.dist_eq]; norm_num [dist_sq_coords, a1, a2, cellCorner, V3.get, v]
  have hs := three_anchor_sum g
  rw [hc] at hs
  have hg0Q : g 0 ∈ Q := hsend 0 origin_Q
  have hsumcoords := fun i : Fin 3 => congrArg (fun z : E3 => z i) hs
  -- Choose the images of the three positive anchors. The distance equations
  -- remove mixed signs and duplicate axes. The notch removes the simultaneous
  -- reversal. No search/decide theorem about feature data is recomputed here.
  -- [compile-fix begin: replace the elaboration-heavy anchor product with indexed six-anchor cases]
  let anchors : Fin 6 → E3 := ![a0, a1, a2, b0, b1, b2] -- [compile-fix]
  obtain ⟨i0, hi0⟩ : ∃ i : Fin 6, g a0 = anchors i := by -- [compile-fix]
    rcases hm0 with h | h | h | h | h | h -- [compile-fix]
    · exact ⟨0, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨1, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨2, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨3, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨4, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨5, by simpa [anchors] using h⟩ -- [compile-fix]
  obtain ⟨i1, hi1⟩ : ∃ i : Fin 6, g a1 = anchors i := by -- [compile-fix]
    rcases hm1 with h | h | h | h | h | h -- [compile-fix]
    · exact ⟨0, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨1, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨2, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨3, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨4, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨5, by simpa [anchors] using h⟩ -- [compile-fix]
  obtain ⟨i2, hi2⟩ : ∃ i : Fin 6, g a2 = anchors i := by -- [compile-fix]
    rcases hm2 with h | h | h | h | h | h -- [compile-fix]
    · exact ⟨0, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨1, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨2, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨3, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨4, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨5, by simpa [anchors] using h⟩ -- [compile-fix]
  rw [hi0, hi1] at hd01 -- [compile-fix]
  rw [hi0, hi2] at hd02 -- [compile-fix]
  rw [hi1, hi2] at hd12 -- [compile-fix]
  have pair_side (i j : Fin 6) (hd : dist (anchors i) (anchors j) ^ 2 = 8) : -- [compile-fix]
      (((i : Nat) < 3 ∧ (j : Nat) < 3) ∨ -- [compile-fix]
       (3 ≤ (i : Nat) ∧ 3 ≤ (j : Nat))) ∧ i ≠ j := by -- [compile-fix]
    fin_cases i <;> fin_cases j -- [compile-fix]
    all_goals norm_num [anchors, dist_sq_coords, a0, a1, a2, b0, b1, b2, -- [compile-fix]
      cellCorner, V3.get, v] at hd -- [compile-fix]
    all_goals norm_num -- [compile-fix]
  have hp01 := pair_side i0 i1 hd01 -- [compile-fix]
  have hp02 := pair_side i0 i2 hd02 -- [compile-fix]
  have hp12 := pair_side i1 i2 hd12 -- [compile-fix]
  have hne01 := hp01.2 -- [compile-fix]
  have hne02 := hp02.2 -- [compile-fix]
  have hne12 := hp12.2 -- [compile-fix]
  have hside : -- [compile-fix]
      ((i0 : Nat) < 3 ∧ (i1 : Nat) < 3 ∧ (i2 : Nat) < 3) ∨ -- [compile-fix]
      (3 ≤ (i0 : Nat) ∧ 3 ≤ (i1 : Nat) ∧ 3 ≤ (i2 : Nat)) := by -- [compile-fix]
    rcases hp01.1 with h01 | h01 <;> rcases hp02.1 with h02 | h02 -- [compile-fix]
    · exact Or.inl ⟨h01.1, h01.2, h02.2⟩ -- [compile-fix]
    · omega -- [compile-fix]
    · omega -- [compile-fix]
    · exact Or.inr ⟨h01.1, h01.2, h02.2⟩ -- [compile-fix]
  have hlinear (x : E3) : -- [compile-fix]
      g.linearIsometryEquiv x = -- [compile-fix]
        (x 0 / 2) • g.linearIsometryEquiv a0 + -- [compile-fix]
        (x 1 / 2) • g.linearIsometryEquiv a1 + -- [compile-fix]
        (x 2 / 2) • g.linearIsometryEquiv a2 := by -- [compile-fix]
    rw [← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add] -- [compile-fix]
    congr 1 -- [compile-fix]
    apply PiLp.ext -- [compile-fix]
    intro i -- [compile-fix]
    fin_cases i <;> -- [compile-fix]
      simp [a0, a1, a2, cellCorner, V3.get, v] <;> ring -- [compile-fix]
  rcases hside with hsmall | hlarge -- [compile-fix]
  · fin_cases i0 -- [compile-fix]
    all_goals norm_num at hsmall -- [compile-fix]
    all_goals fin_cases i1 -- [compile-fix]
    all_goals norm_num at hsmall -- [compile-fix]
    all_goals try norm_num at hne01 -- [compile-fix]
    all_goals fin_cases i2 -- [compile-fix]
    all_goals norm_num at hsmall -- [compile-fix]
    all_goals try norm_num at hne02 -- [compile-fix]
    all_goals try norm_num at hne12 -- [compile-fix]
    all_goals simp [anchors] at hi0 hi1 hi2 -- [compile-fix]
    all_goals
      have hz0 := hsumcoords 0
      have hz1 := hsumcoords 1
      have hz2 := hsumcoords 2
      rw [hi0, hi1, hi2] at hz0 hz1 hz2 -- [compile-fix]
      norm_num [a0, a1, a2, ctr, cellCorner, V3.get, v]
        at hz0 hz1 hz2 -- [compile-fix]
    all_goals
      have hzero : g 0 = 0 := by
        apply PiLp.ext
        intro i
        change g 0 i = 0
        fin_cases i -- [compile-fix]
        · simpa using hz0 -- [compile-fix]
        · simpa using hz1 -- [compile-fix]
        · simpa using hz2 -- [compile-fix]
      have hA0 := rigid_apply g a0
      have hA1 := rigid_apply g a1
      have hA2 := rigid_apply g a2
      rw [hzero, add_zero, hi0] at hA0 -- [compile-fix]
      rw [hzero, add_zero, hi1] at hA1 -- [compile-fix]
      rw [hzero, add_zero, hi2] at hA2 -- [compile-fix]
    all_goals first -- [compile-fix]
      | (refine ⟨n3 0 1 2, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
      | (refine ⟨n3 0 2 1, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
      | (refine ⟨n3 1 0 2, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
      | (refine ⟨n3 1 2 0, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
      | (refine ⟨n3 2 0 1, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
      | (refine ⟨n3 2 1 0, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
  · fin_cases i0 -- [compile-fix]
    all_goals norm_num at hlarge -- [compile-fix]
    all_goals fin_cases i1 -- [compile-fix]
    all_goals norm_num at hlarge -- [compile-fix]
    all_goals try norm_num at hne01 -- [compile-fix]
    all_goals fin_cases i2 -- [compile-fix]
    all_goals norm_num at hlarge -- [compile-fix]
    all_goals try norm_num at hne02 -- [compile-fix]
    all_goals try norm_num at hne12 -- [compile-fix]
    all_goals simp [anchors] at hi0 hi1 hi2 -- [compile-fix]
    all_goals
      have hz0 := hsumcoords 0
      have hz1 := hsumcoords 1
      have hz2 := hsumcoords 2
      rw [hi0, hi1, hi2] at hz0 hz1 hz2 -- [compile-fix]
      norm_num [b0, b1, b2, ctr, cellCorner, V3.get, v]
        at hz0 hz1 hz2 -- [compile-fix]
      have hg0P : g 0 ∈ P := (corner_Q_iff_P (g 0) (by
        intro i
        fin_cases i <;> right <;> simp <;> linarith)).mp hg0Q -- [compile-fix]
      rw [mem_P_iff_coordinates] at hg0P
      exfalso
      rcases hg0P.2.2.2.2.2.2 with h | h | h <;> linarith
  -- [compile-fix end]


/-- The same paired-plane statement previously left open, now recovered
metrically. This does not assert a new formal theorem about planar areas. -/
def axisPlane (i : Fin 3) (c : ℝ) : Set E3 := {x | x i = c}

theorem paired_outer_planes_from_metric (g : RigidMotion) (hQ : g '' Q = Q) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i : Fin 3,
      g '' axisPlane i 0 = axisPlane (σ i) 0 ∧
      g '' axisPlane i 2 = axisPlane (σ i) 2 := by
  classical
  obtain ⟨p,hp,hpose⟩ := Q_self_isometry_frame hQ
  have hp' := hp
  have hindex : ∀ i : Fin 3, p.get i < 3 := by
    simp [coordinatePermutations] at hp'
    rcases hp' with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      intro i <;> fin_cases i <;> norm_num [N3.get,n3]
  let φ : Fin 3 → Fin 3 := fun i => ⟨p.get i,hindex i⟩
  have hφinj : Function.Injective φ := by
    intro i j hij
    have h := congrArg Fin.val hij
    change p.get i = p.get j at h
    have hp'' := hp
    simp [coordinatePermutations] at hp''
    -- [compile-fix begin: separate contradiction pruning from reflexive survivors]
    rcases hp'' with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      fin_cases i <;> fin_cases j
    all_goals norm_num [N3.get, n3] at h
    all_goals rfl
    -- [compile-fix end]
  let e : Equiv.Perm (Fin 3) :=
    Equiv.ofBijective φ ⟨hφinj,Finite.surjective_of_injective hφinj⟩
      -- API?: expected finite-endomap theorem: injectivity implies surjectivity.
  have hzero : g 0 = 0 := by
    apply PiLp.ext
    intro i
    -- [compile-fix begin: specialize the pose translation equation after each Fin case]
    fin_cases i
    · simpa [po, v, V3.get] using hpose.2 (0 : Fin 3)
    · simpa [po, v, V3.get] using hpose.2 (1 : Fin 3)
    · simpa [po, v, V3.get] using hpose.2 (2 : Fin 3)
    -- [compile-fix end]
  have hc (x : E3) (i : Fin 3) : g x i = x (e i) := by
    rw [rigid_apply g x,hzero,add_zero]
    rw [hpose.1 x i]
    -- [compile-fix begin: expose the six certified permutations before simplifying their action]
    have hp'' := hp
    simp [coordinatePermutations] at hp''
    rcases hp'' with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      fin_cases i <;>
      simp [frameActReal, frameCoordinate, po, fr, v, V3.get, hindex,
        φ, e, N3.get, n3]
    -- [compile-fix end]
  have hcoord (x : E3) (i : Fin 3) : g x (e.symm i) = x i := by
    rw [hc]
    simp
  have himage (i : Fin 3) (c : ℝ) :
      g '' axisPlane i c = axisPlane (e.symm i) c := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change g x (e.symm i) = c
      rw [hcoord]
      exact hx
    · intro hy
      refine ⟨g.symm y,?_,g.apply_symm_apply y⟩
      change g.symm y i = c
      rw [← hcoord (g.symm y) i,g.apply_symm_apply]
      exact hy
  exact ⟨e.symm,fun i => ⟨himage i 0,himage i 2⟩⟩

end
end R44.DischargeMetricCarrier
