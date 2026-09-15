/- -- [compile-fix]
# Discharge: per_tube_homeomorphisms

Written proof: proof/ALIGNMENT_PROOF.md A§1, explicit normal-line tube map.
No erratum changes this native construction. The clamp inverse in
TubeCalculus is algebraically the four-interval inverse of the written map.

This proves the frozen field for the globally defined featureTubeMap,
including identity outside the tube, not just a map between subspaces.
No hypothesis record, other residual field, or MeshSemantics admission is
used. No mathematical admissions occur. Uncompiled proof script.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.TubeCalculus -- [compile-fix]

namespace R44.DischargeTube
open Set R44.DischargeGeometry
noncomputable section

@[fun_prop] theorem continuous_frameCoordinate (i : Nat) :
    Continuous (fun x : E3 => frameCoordinate x i) := by
  unfold frameCoordinate
  split_ifs <;> fun_prop

@[fun_prop] theorem continuous_radius (r : Role) : Continuous (featureRadius r) := by
  exact (((continuous_frameCoordinate _).comp
    (continuous_id.sub continuous_const)).abs).max
    (((continuous_frameCoordinate _).comp
      (continuous_id.sub continuous_const)).abs)

@[fun_prop] theorem continuous_normalCoordinate (r : Role) :
    Continuous (featureNormalCoordinate r) := by
  unfold featureNormalCoordinate
  exact continuous_const.mul ((continuous_frameCoordinate _).comp
    (continuous_id.sub continuous_const))

@[fun_prop] theorem continuous_height (r : Role) : Continuous (featureHeight r) := by
  unfold featureHeight
  exact continuous_const.mul (continuous_const.max
    (continuous_const.sub ((continuous_radius r).div_const eta)))
    -- API?: expected Continuous.div_const: dividing a continuous real function by a fixed real is continuous.

@[fun_prop] theorem continuous_cutoff : Continuous tubeCutoff := by
  unfold tubeCutoff
  fun_prop

@[fun_prop] theorem continuous_forward (r : Role) : Continuous (featureTubeMap r) := by
  unfold featureTubeMap
  exact continuous_id.add
    ((((continuous_cutoff.comp (continuous_normalCoordinate r)).mul
      (continuous_height r))).smul continuous_const)

theorem height_strict (r : Role) (x : E3) : |featureHeight r x| < eta :=
  (featureHeight_abs_bound r x).trans_lt (by norm_num [eta])

/-- Only the normal coordinate changes under the inverse. -/
def inverseTubeMap (r : Role) (x : E3) : E3 :=
  x + (backward eta (featureHeight r x) (featureNormalCoordinate r x) -
    featureNormalCoordinate r x) • featureNormal r

@[simp] theorem radius_inverse (r : Role) (x : E3) :
    featureRadius r (inverseTubeMap r x) = featureRadius r x := by
  exact radius_normal_shift r x _

@[simp] theorem height_inverse (r : Role) (x : E3) :
    featureHeight r (inverseTubeMap r x) = featureHeight r x := by
  exact height_normal_shift r x _

@[simp] theorem normal_inverse (r : Role) (x : E3) :
    featureNormalCoordinate r (inverseTubeMap r x) =
      backward eta (featureHeight r x) (featureNormalCoordinate r x) := by
  rw [inverseTubeMap, normal_shift]
  ring

@[simp] theorem radius_forward (r : Role) (x : E3) :
    featureRadius r (featureTubeMap r x) = featureRadius r x :=
  radius_normal_shift r x _

@[simp] theorem height_forward (r : Role) (x : E3) :
    featureHeight r (featureTubeMap r x) = featureHeight r x :=
  height_normal_shift r x _

@[simp] theorem normal_forward (r : Role) (x : E3) :
    featureNormalCoordinate r (featureTubeMap r x) =
      forward eta (featureHeight r x) (featureNormalCoordinate r x) := by
  rw [featureTubeMap, normal_shift]
  rfl

theorem inverse_forward (r : Role) (x : E3) :
    inverseTubeMap r (featureTubeMap r x) = x := by
  rw [inverseTubeMap, height_forward, normal_forward,
    backward_forward (height_strict r x)]
  unfold featureTubeMap forward tubeCutoff
  module

theorem forward_inverse (r : Role) (x : E3) :
    featureTubeMap r (inverseTubeMap r x) = x := by
  have hz := forward_backward (height_strict r x) (featureNormalCoordinate r x)
  rw [featureTubeMap, height_inverse, normal_inverse]
  unfold inverseTubeMap
  have hc :
      (backward eta (featureHeight r x) (featureNormalCoordinate r x) -
        featureNormalCoordinate r x) +
      tubeCutoff (backward eta (featureHeight r x) (featureNormalCoordinate r x)) *
        featureHeight r x = 0 := by
    change backward _ _ _ + _ = _ at hz
    unfold tubeCutoff
    linarith
  calc
    _ = x + ((backward eta (featureHeight r x) (featureNormalCoordinate r x) -
        featureNormalCoordinate r x) +
      tubeCutoff (backward eta (featureHeight r x) (featureNormalCoordinate r x)) *
        featureHeight r x) • featureNormal r := by module
    _ = x := by rw [hc]; simp

@[fun_prop] theorem continuous_inverse (r : Role) : Continuous (inverseTubeMap r) := by
  exact continuous_id.add (((backward_continuous (continuous_height r)
    (continuous_normalCoordinate r) (height_strict r)).sub
    (continuous_normalCoordinate r)).smul continuous_const)

/-- The explicit global homeomorphism; later files use its injectivity and
surjectivity, rather than presupposing a homeomorphism of the completed Q. -/
def tubeHomeomorph (r : Role) : E3 ≃ₜ E3 where
  toFun := featureTubeMap r
  invFun := inverseTubeMap r
  left_inv := inverse_forward r
  right_inv := forward_inverse r
  continuous_toFun := continuous_forward r
  continuous_invFun := continuous_inverse r

@[simp] theorem tubeHomeomorph_apply (r : Role) (x : E3) :
    tubeHomeomorph r x = featureTubeMap r x := rfl

/-- Each formula fixes every point outside its own *closed* support. -/
theorem forward_fixed_outside (r : Role) (x : E3)
    (hx : ¬ featureTubeSupport r x) : featureTubeMap r x = x := by
  by_cases hr : featureRadius r x ≤ eta
  · have hn : eta < |featureNormalCoordinate r x| := by
      exact lt_of_not_ge (fun hn => hx ⟨hr,hn⟩)
    have hcut : tubeCutoff (featureNormalCoordinate r x) = 0 := by
      unfold tubeCutoff
      apply max_eq_left
      have h := (one_le_div (show 0 < eta by norm_num [eta])).mpr hn.le
      linarith
    simp [featureTubeMap, hcut]
  · have hh : featureHeight r x = 0 := by
      unfold featureHeight
      have h := (one_le_div (show 0 < eta by norm_num [eta])).mpr (le_of_not_ge hr)
      rw [max_eq_left (show 1 - featureRadius r x / eta ≤ 0 by linarith)]
      ring
    simp [featureTubeMap, hh]

/-- Any bijection fixing the complement of a set preserves the set. -/
theorem support_preserved {X : Type*} (F : X ≃ X) (S : Set X)
    (hfix : ∀ x, x ∉ S → F x = x) {x : X} (hx : x ∈ S) : F x ∈ S := by
  by_contra hnot
  have h : F (F x) = F x := hfix (F x) hnot
  have heq : F x = x := F.injective h
  exact hnot (heq.symm ▸ hx)

theorem forward_support (r : Role) {x : E3} (hx : featureTubeSupport r x) :
    featureTubeSupport r (featureTubeMap r x) := by
  exact support_preserved (tubeHomeomorph r).toEquiv
    {x | featureTubeSupport r x} (forward_fixed_outside r) hx

end
end R44.DischargeTube

namespace R44
noncomputable section

/-- Frozen Hypotheses field; no premises were added. -/
theorem per_tube_homeomorphisms_holds : PerTubeHomeomorphisms := by
  intro r
  exact ⟨DischargeTube.tubeHomeomorph r, fun _ => rfl⟩

end
end R44
