/- -- [compile-fix]
# Uniformly separated supported ambient homeomorphisms glue

Written source: A§1/A-L6.2 and R§8--9, proof/ALIGNMENT_PROOF.md and
proof/PROOFS_registered.md; ERRATA E2 and E6. This is the all-space analogue
of the accepted finite native-tube composition. It does not assume coverage
of the solid or matching of the geometric interfaces: those are separate
premises to be verified for an assembly.

Uniform separation is stronger than local finiteness and is available for
the eighth-grid tubes. Near ANY point the resulting map agrees with ONE
ambient homeomorphism or the identity. The same statement applies to its
inverse. No infinite sum, inverse-limit assertion, or infinite composition
is used. No mathematical admission.
-/
import Mathlib

namespace R44.DischargeSeparatedGlue
open Set
noncomputable section

section
variable {X I : Type*} [MetricSpace X]
variable (K : I → Set X) (F : I → X ≃ₜ X)
variable (δ : ℝ) (hδ : 0<δ)
variable (hsep : ∀i j, i≠j → ∀x∈K i,∀y∈K j,δ≤dist x y)
variable (hfix : ∀i x,x∉K i → F i x=x)

include hsep hδ in -- [compile-fix]
private theorem unique_support {i j:I} {x:X} (hi:x∈K i) (hj:x∈K j) : i=j := by
  by_contra hn
  have h := hsep i j hn x hi x hj
  simp only [dist_self] at h
  linarith

include hfix in -- [compile-fix]
private theorem supports_preserved (i:I) (x:X) : F i x∈K i ↔ x∈K i := by
  constructor
  · intro hx
    by_contra hn
    rw [hfix i x hn] at hx
    exact hn hx
  · intro hx
    by_contra hn
    have he : F i (F i x)=F i x := hfix i (F i x) hn
    have he' : F i x=x := (F i).injective he
    exact hn (by rw [he']; exact hx) -- [compile-fix]

include hfix in -- [compile-fix]
private theorem inverse_fixed (i:I) (x:X) (hx:x∉K i) : (F i).symm x=x := by
  apply (F i).injective
  rw [(F i).apply_symm_apply,hfix i x hx]

include hfix in -- [compile-fix]
private theorem inverse_support (i:I) (x:X) : (F i).symm x∈K i ↔ x∈K i := by
  simpa using (supports_preserved K F hfix i ((F i).symm x)).symm

private def patch (x:X) : X := by -- [compile-fix]
  classical -- [compile-fix]
  exact if hx : ∃i,x∈K i then F (Classical.choose hx) x else x -- [compile-fix]

include hsep hδ in -- [compile-fix]
private theorem patch_on (i:I) {x:X} (hx:x∈K i) : patch K F x=F i x := by
  have he : ∃j,x∈K j := ⟨i,hx⟩
  rw [patch,dif_pos he]
  have hi : Classical.choose he=i :=
    unique_support K δ hδ hsep (Classical.choose_spec he) hx
  rw [hi]

private theorem patch_off {x:X} (hx : ∀i,x∉K i) : patch K F x=x := by
  simp only [patch]
  rw [dif_neg (by simpa using hx)]

include δ hδ hsep hfix in -- [compile-fix]
/-- Local agreement on a fixed-radius ball proves continuity. The argument
works even when the ball touches the boundary of the selected support. -/
private theorem patch_continuous : Continuous (patch K F) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let U := Metric.ball x (δ/3)
  have hU : U∈nhds x := Metric.ball_mem_nhds x (by positivity)
  by_cases hn : ∃i, (K i∩U).Nonempty
  · obtain ⟨i,u,hu,hux⟩ := hn
    have hlocal : ∀y∈U,patch K F y=F i y := by
      intro y hy
      by_cases hi : y∈K i
      · exact patch_on K F δ hδ hsep i hi
      · have hnone : ∀j,y∉K j := by
          intro j hj
          have hji : j≠i := by intro he; subst j; exact hi hj
          have hlower := hsep j i hji y hj u hu
          have hupper : dist y u<δ := by
            calc
              dist y u ≤ dist y x+dist x u := dist_triangle _ _ _
              _ < δ/3+δ/3 := add_lt_add
                (Metric.mem_ball.mp hy) (by simpa [dist_comm] using Metric.mem_ball.mp hux)
              _ < δ := by linarith
          linarith
        rw [patch_off K F hnone,hfix i y hi]
    have heq : patch K F =ᶠ[nhds x] F i := -- [compile-fix]
      Filter.mem_of_superset hU (fun y hy => hlocal y hy) -- [compile-fix]
    exact (F i).continuous.continuousAt.congr_of_eventuallyEq heq -- [compile-fix]
    -- API?: ContinuousAt.congr_of_eventuallyEq transports continuity along
    -- equality on a neighborhood; orient the eventual equality as required.
  · have hnone : ∀y∈U,∀i,y∉K i := by
      intro y hy i hi
      exact hn ⟨i,y,hi,hy⟩
    have he : ∀ᶠ y in nhds x,patch K F y=y :=
      Filter.mem_of_superset hU (fun y hy => patch_off K F (hnone y hy))
    exact continuousAt_id.congr_of_eventuallyEq he -- [compile-fix]

include δ hδ hsep hfix in -- [compile-fix]
/-- The ambient gluing object, with agreement on every support and identity
outside their union. The support family is allowed to be infinite. -/
theorem glue :
    ∃G : X ≃ₜ X,
      (∀i x,x∈K i → G x=F i x) ∧
      (∀x,(∀i,x∉K i) → G x=x) := by
  let f := patch K F
  let b := patch K (fun i => (F i).symm)
  have hbfix : ∀i x,x∉K i → (F i).symm x=x := inverse_fixed K F hfix
  have hleft : Function.LeftInverse b f := by
    intro x
    by_cases hx : ∃i,x∈K i
    · obtain ⟨i,hi⟩ := hx
      have hfi := (supports_preserved K F hfix i x).mpr hi
      rw [show f x=F i x from patch_on K F δ hδ hsep i hi]
      rw [show b (F i x)=(F i).symm (F i x) from
        patch_on K (fun i => (F i).symm) δ hδ hsep i hfi]
      exact (F i).symm_apply_apply x
    · have hn : ∀i,x∉K i := by simpa using hx
      rw [show f x=x from patch_off K F hn]
      exact patch_off K (fun i => (F i).symm) hn
  have hright : Function.RightInverse b f := by
    intro x
    by_cases hx : ∃i,x∈K i
    · obtain ⟨i,hi⟩ := hx
      have hbi := (inverse_support K F hfix i x).mpr hi
      rw [show b x=(F i).symm x from
        patch_on K (fun i => (F i).symm) δ hδ hsep i hi]
      rw [show f ((F i).symm x)=F i ((F i).symm x) from
        patch_on K F δ hδ hsep i hbi]
      exact (F i).apply_symm_apply x
    · have hn : ∀i,x∉K i := by simpa using hx
      rw [show b x=x from patch_off K (fun i => (F i).symm) hn]
      exact patch_off K F hn
  let G : X ≃ₜ X := {
    toFun := f
    invFun := b
    left_inv := hleft
    right_inv := hright
    continuous_toFun := patch_continuous K F δ hδ hsep hfix
    continuous_invFun := patch_continuous K (fun i => (F i).symm) δ hδ hsep hbfix }
  exact ⟨G,fun i x hx => patch_on K F δ hδ hsep i hx,
    fun x hx => patch_off K F hx⟩

end
end -- [compile-fix]
end R44.DischargeSeparatedGlue
