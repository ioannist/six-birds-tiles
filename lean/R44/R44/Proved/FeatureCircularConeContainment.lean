/- -- [compile-fix]
# Discharge: feature_circular_cone_containment

Written proof: proof/ALIGNMENT_PROOF.md A-L4.1. The square tent is Euclidean-
Lipschitz with constant at most 3/25 in its two tangent coordinates, including
base edges and the apex. FeatureLocalCharts establishes actual open-
neighborhood agreement beyond the closed square, so this proof does not
silently apply a relative-tube identity at a tube-boundary point.

The cone is the frozen strict circularCone, and the tangent cone is the
frozen radial definition. No formula for solidAngle, MeshSemantics admission,
polyhedral sector budget, or Hypotheses inhabitant is assumed. All displayed
helper claims are proved. Uncompiled; unconfirmed API calls are marked.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.FeatureLocalCharts -- [compile-fix]

namespace R44.DischargeCones
open Set R44.DischargeGeometry R44.DischargeCharts
noncomputable section

private theorem abs_max_zero_sub (a b : ℝ) :
    |max 0 a-max 0 b| ≤ |a-b| := by
  have hab : a ≤ b+|a-b| := by linarith [le_abs_self (a-b)]
  have hba : b ≤ a+|a-b| := by linarith [neg_le_abs (a-b)]
  have ha : max 0 a ≤ max 0 b+|a-b| := by
    apply max_le
    · positivity
    · exact hab.trans (add_le_add_left (le_max_right _ _) _) -- [compile-fix]
  have hb : max 0 b ≤ max 0 a+|a-b| := by
    apply max_le
    · positivity
    · exact hba.trans (add_le_add_left (le_max_right _ _) _) -- [compile-fix]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem abs_max_radius_sub (u v u' v' : ℝ) :
    abs (max |u'| |v'| - max |u| |v|) ≤ max |u'-u| |v'-v| := by -- [compile-fix]
  let d := max |u'-u| |v'-v|
  have hu : |u'| ≤ |u|+d := by
    calc
      |u'| = |u+(u'-u)| := by congr 1; ring
      _ ≤ |u|+|u'-u| := abs_add_le _ _
      _ ≤ |u|+d := add_le_add_right (le_max_left _ _) _ -- [compile-fix]
  have hv : |v'| ≤ |v|+d := by
    calc
      |v'| = |v+(v'-v)| := by congr 1; ring
      _ ≤ |v|+|v'-v| := abs_add_le _ _
      _ ≤ |v|+d := add_le_add_right (le_max_right _ _) _ -- [compile-fix]
  have hu' : |u| ≤ |u'|+d := by
    calc
      |u| = |u'-(u'-u)| := by congr 1; ring
      _ ≤ |u'|+|u'-u| := abs_sub _ _
      _ ≤ |u'|+d := add_le_add_right (le_max_left _ _) _ -- [compile-fix]
  have hv' : |v| ≤ |v'|+d := by
    calc
      |v| = |v'-(v'-v)| := by congr 1; ring
      _ ≤ |v'|+|v'-v| := abs_sub _ _
      _ ≤ |v'|+d := add_le_add_right (le_max_right _ _) _ -- [compile-fix]
  have hupper : max |u'| |v'| ≤ max |u| |v|+d :=
    max_le (hu.trans (add_le_add_left (le_max_left _ _) _)) -- [compile-fix]
      (hv.trans (add_le_add_left (le_max_right _ _) _)) -- [compile-fix]
  have hlower : max |u| |v| ≤ max |u'| |v'|+d :=
    max_le (hu'.trans (add_le_add_left (le_max_left _ _) _)) -- [compile-fix]
      (hv'.trans (add_le_add_left (le_max_right _ _) _)) -- [compile-fix]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Global tangent-coordinate estimate; the normal coordinate is absent. -/
theorem height_tangential_bound (r : Role) (x y : E3) :
    |featureHeight r y-featureHeight r x| ≤
      (3/25 : ℝ) * max |chartU r y-chartU r x| |chartV r y-chartV r x| := by
  let h : ℝ := (profileCoefficient r : ℝ)/10000
  let d := max |chartU r y-chartU r x| |chartV r y-chartV r x|
  have hc : |h| ≤ (12:ℝ)/10000 := by
    have hc' : |(profileCoefficient r : ℝ)| ≤ 12 := by
      -- [compile-fix begin: bridge the certified Int.natAbs bound through the real cast]
      have hc'' : ((profileCoefficient r).natAbs : ℝ) ≤ 12 := by
        exact_mod_cast (coefficient_bounds profile_canonical r).2
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hc''
      -- [compile-fix end]
    dsimp [h]
    rw [abs_div,abs_of_pos (show (0:ℝ)<10000 by norm_num)]
    exact div_le_div_of_nonneg_right hc' (by norm_num)
  have hr : |featureRadius r y-featureRadius r x| ≤ d :=
    abs_max_radius_sub (chartU r x) (chartV r x) (chartU r y) (chartV r y)
  have hd : 0 ≤ d := (abs_nonneg _).trans (le_max_left _ _)
  calc
    |featureHeight r y-featureHeight r x| =
        |h| * |max 0 (1-featureRadius r y/eta)-
          max 0 (1-featureRadius r x/eta)| := by
            unfold featureHeight
            rw [← mul_sub,abs_mul]
    _ ≤ |h| * |(1-featureRadius r y/eta)-(1-featureRadius r x/eta)| :=
      mul_le_mul_of_nonneg_left (abs_max_zero_sub _ _) (abs_nonneg h)
    _ = |h| * (|featureRadius r y-featureRadius r x|/eta) := by
      have heq : (1-featureRadius r y/eta)-(1-featureRadius r x/eta) =
          -(featureRadius r y-featureRadius r x)/eta := by ring
      rw [heq] -- [compile-fix]
      simp only [abs_div, abs_neg, abs_of_pos (show 0 < eta by norm_num [eta])] -- [compile-fix]
    _ ≤ ((12:ℝ)/10000)*(d/eta) := by
      exact mul_le_mul hc (div_le_div_of_nonneg_right hr (by norm_num [eta]))
        (div_nonneg (abs_nonneg _) (by norm_num [eta])) (by norm_num)
    _ = (3/25 : ℝ)*d := by norm_num [eta]; ring

private theorem max_abs_le_sqrt (a b : ℝ) :
    max |a| |b| ≤ Real.sqrt (a^2+b^2) := by
  have hs0 := Real.sqrt_nonneg (a^2+b^2)
  have hs2 : Real.sqrt (a^2+b^2)^2 = a^2+b^2 :=
    Real.sq_sqrt (by positivity)
  apply max_le
  · nlinarith [sq_abs a,sq_nonneg b,abs_nonneg a]
  · nlinarith [sq_abs b,sq_nonneg a,abs_nonneg b]

/-- A strict circular-cone direction remains below the signed graph for
every positive step in the globally continued native hypograph. -/
theorem native_cone_in_tangent (r : Role) {x : E3}
    (hx : x ∈ nativeFeatureGraph r) :
    chartEquiv r '' circularCone (3/25) ⊆ tangentCone Q x := by
  rw [native_tangentCone_eq_hypograph r hx]
  rintro d ⟨w,hw,rfl⟩
  obtain ⟨_,hxgraph⟩ := graph_coordinates r hx
  refine ⟨1,zero_lt_one,?_⟩
  intro t ht _
  have hc := ray_coordinates r x w t
  have hLip := height_tangential_bound r x (x+t • chartEquiv r w)
  have hU : chartU r (x+t • chartEquiv r w)-chartU r x = t*w 0 := by
    rw [hc.1]; ring
  have hV : chartV r (x+t • chartEquiv r w)-chartV r x = t*w 1 := by
    rw [hc.2.1]; ring
  rw [hU,hV,abs_mul,abs_mul,abs_of_pos ht] at hLip
  have hmax : max (t*|w 0|) (t*|w 1|) ≤
      t*Real.sqrt (w 0^2+w 1^2) := by
    have hs := max_abs_le_sqrt (w 0) (w 1)
    exact max_le
      (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hs) ht.le)
      (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hs) ht.le)
  have hlo := neg_le_of_abs_le
    (hLip.trans (mul_le_mul_of_nonneg_left hmax (by norm_num)))
  have hdown : t*w 2 < t*(-(3/25:ℝ)*Real.sqrt (w 0^2+w 1^2)) :=
    mul_lt_mul_of_pos_left hw ht
  change featureNormalCoordinate r (x+t • chartEquiv r w) ≤
    featureHeight r (x+t • chartEquiv r w)
  rw [hc.2.2,hxgraph]
  nlinarith

/-- Tangent directions transport by the linear part of an affine isometry. -/
theorem affine_tangent_transport (g : RigidMotion) (S : Set E3) (x : E3) :
    g.linearIsometryEquiv '' tangentCone S x ⊆ tangentCone (g '' S) (g x) := by
  rintro v ⟨w,⟨ε,hε,hw⟩,rfl⟩
  refine ⟨ε,hε,?_⟩
  intro t ht hs
  refine ⟨x+t • w,hw t ht hs,?_⟩
  have h := g.map_vadd x (t • w)
  simpa only [vadd_eq_add,map_smul,add_comm] using h

end
end R44.DischargeCones

namespace R44
open Set DischargeCharts DischargeCones
noncomputable section

/-- Frozen field proposition. Tiling assumptions are retained but are not
needed: this is a local statement about any isometric copy of the actual Q. -/
theorem feature_circular_cone_containment_holds : FeatureCircularConeContainment Q := by
  intro T g _hg r x hx
  obtain ⟨y,hy,rfl⟩ := hx
  let A : E3 ≃ₗᵢ[ℝ] E3 := (chartEquiv r).trans g.linearIsometryEquiv
  refine ⟨A,?_⟩
  apply interior_maximal
  · rintro v ⟨w,hw,rfl⟩
    apply affine_tangent_transport g Q y
    refine ⟨chartEquiv r w, native_cone_in_tangent r hy ⟨w,hw,rfl⟩,rfl⟩
  · exact A.toHomeomorph.isOpenMap _ (circularCone_isOpen (3/25))
      -- API?: expected Homeomorph.isOpenMap: an open set has open image.

end
end R44
