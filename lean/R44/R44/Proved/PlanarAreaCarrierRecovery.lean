/- -- [compile-fix]
# Discharge: planar_area_carrier_recovery

Written target: proof/PROOFS_registered.md R§6, ERRATA E5.
EXPLICIT METHOD DEVIATION: this replaces the written planar-area derivation
by a diameter-endpoint argument for the same fixed Q and the exact same
frozen proposition PlanarAreaCarrierRecovery. No planar-area measure theorem
is claimed. There is no change to any Hypotheses field or definition.
The formerly admitted paired outer-plane statement is proved verbatim using
MetricCarrierRecovery; the affine recovery downstream is unchanged.

Reason for the alternate proof: every point of any feature tube has squared
distance <12 from every point of Q. Consequently the diameter endpoints are
exactly the six undeformed antipodal corners. They recover the center and
axes, and the missing corner excludes simultaneous reversal. This supplies
both the paired-plane lemma and the field without Hausdorff-area machinery.
The written area proof need not be deemed false for this replacement to work.

All scripts are uncompiled here. No mathematical admissions or dependencies
on either the mesh-semantics admission or another residual field occur.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.MetricCarrierRecovery -- [compile-fix]

namespace R44
open Set
open R44.DischargeGeometry
noncomputable section

private def coordinatePlane (i : Fin 3) (c : ℝ) : Set E3 := {x | x i = c}
private def axisPoint (i : Fin 3) (c : ℝ) : E3 :=
  WithLp.toLp 2 fun j => if j = i then c else 0

private theorem paired_outer_planes_from_metric
    (g : RigidMotion) (hQ : g '' Q = Q) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i : Fin 3,
      g '' coordinatePlane i 0 = coordinatePlane (σ i) 0 ∧
      g '' coordinatePlane i 2 = coordinatePlane (σ i) 2 := by
  exact DischargeMetricCarrier.paired_outer_planes_from_metric g hQ

/-- A paired 0/2 plane atlas determines the affine coordinate functions;
there is no remaining translation or sign reversal. -/
private theorem coordinates_from_paired_planes (g : RigidMotion)
    (σ : Equiv.Perm (Fin 3))
    (hp : ∀ i : Fin 3,
      g '' coordinatePlane i 0 = coordinatePlane (σ i) 0 ∧
      g '' coordinatePlane i 2 = coordinatePlane (σ i) 2) :
    ∀ x : E3, ∀ i : Fin 3, g x (σ i) = x i := by
  intro x i
  have hp0 (y : E3) (hy : y i = 0) : g y (σ i) = 0 := by
    have hm : g y ∈ g '' coordinatePlane i 0 := ⟨y, hy, rfl⟩
    rw [(hp i).1] at hm
    exact hm
  have hp2 (y : E3) (hy : y i = 2) : g y (σ i) = 2 := by
    have hm : g y ∈ g '' coordinatePlane i 2 := ⟨y, hy, rfl⟩
    rw [(hp i).2] at hm
    exact hm
  have hzero : g 0 (σ i) = 0 := hp0 0 rfl
  let e := axisPoint i 2
  have he : e i = 2 := by simp [e, axisPoint]
  have hge : g e (σ i) = 2 := hp2 e he
  have hAe : (g.linearIsometryEquiv e) (σ i) = 2 := by
    have h := congrArg (fun y : E3 => y (σ i)) (g.map_vadd (0 : E3) e)
    simp only [vadd_eq_add, add_zero] at h
    change g e (σ i) = (g.linearIsometryEquiv e) (σ i) + g 0 (σ i) at h
    linarith
  let y : E3 := x - (x i / 2) • e
  have hy : y i = 0 := by
    change x i - (x i / 2) * e i = 0
    rw [he]
    ring
  have hgy := hp0 y hy
  have hxy : (x i / 2) • e + y = x := by
    dsimp [y]
    abel
  have hmap := congrArg (fun z : E3 => z (σ i))
    (g.map_vadd y ((x i / 2) • e))
  simp only [vadd_eq_add, hxy, map_smul] at hmap
  change g x (σ i) = (x i / 2) * (g.linearIsometryEquiv e) (σ i) + g y (σ i) at hmap
  rw [hAe, hgy] at hmap
  linarith

private theorem carrier_from_coordinate_permutation (g : RigidMotion)
    (σ : Equiv.Perm (Fin 3))
    (hcoord : ∀ x : E3, ∀ i : Fin 3, g x (σ i) = x i) :
    g '' P = P := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨hbox, i, hnotch⟩ := (mem_P_iff_box_notch x).mp hx
    apply (mem_P_iff_box_notch (g x)).mpr
    constructor
    · intro j
      obtain ⟨i, rfl⟩ := σ.surjective j
      simpa only [hcoord] using hbox i
    · exact ⟨σ i, by simpa only [hcoord] using hnotch⟩
  · intro y hy
    let x := g.symm y
    have hxy : g x = y := g.apply_symm_apply y
    have hc : ∀ i : Fin 3, y (σ i) = x i := by
      intro i
      rw [← hxy]
      exact hcoord x i
    obtain ⟨hbox, j, hnotch⟩ := (mem_P_iff_box_notch y).mp hy
    refine ⟨x, ?_, hxy⟩
    apply (mem_P_iff_box_notch x).mpr
    constructor
    · intro i
      rw [← hc i]
      exact hbox (σ i)
    · obtain ⟨i, rfl⟩ := σ.surjective j
      exact ⟨i, by simpa only [hc] using hnotch⟩

/-- Exact frozen endpoint, now with a metric proof of the paired-plane
statement and no mathematical admission. See the explicit method deviation. -/
theorem planar_area_carrier_recovery_holds : PlanarAreaCarrierRecovery := by
  intro g hQ
  obtain ⟨σ, hplanes⟩ := paired_outer_planes_from_metric g hQ
  exact carrier_from_coordinate_permutation g σ (coordinates_from_paired_planes g σ hplanes)

end
end R44
