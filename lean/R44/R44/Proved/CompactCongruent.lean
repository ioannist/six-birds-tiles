/- -- [compile-fix]
# Compact isometric containment

Used for A-L4.3 (proof/ALIGNMENT_PROOF.md, ERRATA E1). This is an explicitly
alternative proof of the graph-equality step: two congruent compact sets
cannot be properly contained one in the other. The written argument uses
one-dimensional graph length; compactness proves the same conclusion without
any Hausdorff-measure computation. No R44 geometric hypotheses are used here.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import Mathlib

namespace R44.DischargeCompact
open Set Function
noncomputable section

/-- A compact set cannot properly contain its image under an isometry. -/
theorem compact_isometry_image_eq {X : Type*} [MetricSpace X]
    {K : Set X} (hK : IsCompact K) (f : X → X) (hf : Isometry f)
    (hsub : f '' K ⊆ K) : f '' K = K := by
  classical
  apply Set.Subset.antisymm hsub
  intro x hx
  by_contra hnot
  have hc : IsClosed (f '' K) := (hK.image hf.continuous).isClosed
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hc.isOpen_compl x hnot
  have hsep (y : X) (hy : y∈K) : ε ≤ dist x (f y) := by
    by_contra hn
    have hb : f y ∈ Metric.ball x ε := by
      simpa [Metric.mem_ball,dist_comm] using lt_of_not_ge hn
    exact (hball hb) ⟨y,hy,rfl⟩
  let u : ℕ → X := fun n => f^[n] x
  have hu (n : ℕ) : u n∈K := by
    induction n with
    | zero => exact hx
    | succ n hn => exact hsub ⟨u n,hn,by simp [u,Function.iterate_succ_apply']⟩
  have hiter (m : ℕ) : Isometry (f^[m]) := by
    induction m with
    | zero => exact isometry_id
    | succ m hm => simpa [Function.iterate_succ] using hm.comp hf
  have hdist {m n : ℕ} (hmn : m<n) : ε ≤ dist (u m) (u n) := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_lt hmn
      -- API?: expected n=m+k+1 for m<n; re-associate Nat addition if needed.
    have heq : u (m+k+1) = f^[m] (f (u k)) := by
      simp only [u, Nat.add_assoc, Function.iterate_add_apply, -- [compile-fix]
        Function.iterate_succ_apply'] -- [compile-fix]
    rw [heq]
    change ε ≤ dist (f^[m] x) (f^[m] (f (u k)))
    rw [(hiter m).dist_eq]
    exact hsep _ (hu k)
  obtain ⟨C,hCK,hC,hcover⟩ := hK.finite_cover_balls (show 0<ε/3 by positivity)
    -- API?: expected IsCompact.finite_cover_balls: finite C⊆K whose ε/3 balls cover K.
  letI : Fintype C := hC.fintype
  have hchoose (n : ℕ) : ∃c : C, dist (u n) c.1 < ε/3 := by
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp (hcover (hu n))
    obtain ⟨hcC,huc⟩ := Set.mem_iUnion.mp hc
    exact ⟨⟨c,hcC⟩,huc⟩
  choose c hc using hchoose
  have hninj : ¬ Function.Injective c := by
    intro hi
    haveI : Finite ℕ := Finite.of_injective c hi
      -- API?: expected Finite.of_injective into a finite type.
    exact not_finite ℕ -- [compile-fix]
  obtain ⟨m,n,hcEq,hmn⟩ := Function.not_injective_iff.mp hninj
    -- API?: expected not_injective_iff : ¬Injective c ↔ ∃m n,c m=c n ∧ m≠n.
  have hupper : dist (u m) (u n) < ε := by
    have hm := hc m
    have hn := hc n
    rw [← hcEq] at hn
    have ht := dist_triangle (u m) (c m).1 (u n)
    rw [dist_comm (c m).1 (u n)] at ht
    linarith
  rcases lt_or_gt_of_ne hmn with h | h
  · exact (not_lt_of_ge (hdist h)) hupper
  · exact (not_lt_of_ge (hdist h)) (by simpa [dist_comm] using hupper)

end
end R44.DischargeCompact
