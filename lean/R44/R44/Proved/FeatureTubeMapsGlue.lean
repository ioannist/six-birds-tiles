/- -- [compile-fix]
# Discharge: feature_tube_maps_glue

Written proof: proof/ALIGNMENT_PROOF.md A§1, finite native ambient gluing.
The stronger all-assembly ownership discussion in ERRATA E6 is not needed
for these 192 pairwise disjoint native tubes. Gluing here is implemented as
a finite composition of global homeomorphisms. Preservation of each support
is proved from injectivity and identity on its complement, so no unproved
piecewise-continuity or inverse-gluing assertion is used.

The exact frozen premises are retained, including the boundary-fixing
premise (which is redundant once the explicit outside formula is known).
No mathematical admissions; no dependency on MeshSemantics or Hypotheses.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.PerTubeHomeomorphisms -- [compile-fix]

namespace R44
open Set DischargeTube
noncomputable section

/-- Frozen field proposition, copied without changing its premises. -/
theorem feature_tube_maps_glue_holds : FeatureTubeMapsGlue := by
  intro hdisjoint _hboundary hlocal
  classical
  choose F hF using hlocal
  have hfix (r : Role) (x : E3) (hx : ¬ featureTubeSupport r x) : F r x = x := by
    rw [hF r x]
    exact forward_fixed_outside r x hx
  have finite_glue (s : Finset Role) :
      ∃ G : E3 ≃ₜ E3,
        (∀ r ∈ s, ∀ x, featureTubeSupport r x → G x = featureTubeMap r x) ∧
        (∀ x, (∀ r ∈ s, ¬ featureTubeSupport r x) → G x = x) := by
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨Homeomorph.refl E3, ?_, ?_⟩
        · simp
        · intro x _
          rfl
    | @insert r s hrs ih =>
        obtain ⟨G, hGin, hGout⟩ := ih
        refine ⟨G.trans (F r), ?_, ?_⟩
        · intro a ha x hx
          change F r (G x) = featureTubeMap a x
          rcases Finset.mem_insert.mp ha with har | has
          · subst a
            have hout : ∀ a ∈ s, ¬ featureTubeSupport a x := by
              intro a has hax
              have hne : r ≠ a := by intro h; subst a; exact hrs has
              exact Set.disjoint_left.mp (hdisjoint r a hne) hx hax
            rw [hGout x hout, hF r x]
          · have har : r ≠ a := by intro h; subst a; exact hrs has
            rw [hGin a has x hx]
            have hax : featureTubeSupport a (featureTubeMap a x) :=
              forward_support a hx
            have hnot : ¬ featureTubeSupport r (featureTubeMap a x) := by
              intro hrx
              exact Set.disjoint_left.mp (hdisjoint r a har) hrx hax
            exact hfix r _ hnot
        · intro x hout
          change F r (G x) = x
          rw [hGout x (fun a ha => hout a (Finset.mem_insert_of_mem ha))]
          exact hfix r x (hout r (Finset.mem_insert_self r s))
  obtain ⟨G, hGin, hGout⟩ := finite_glue Finset.univ
  refine ⟨G, ?_, ?_⟩
  · intro r x hx
    exact hGin r (Finset.mem_univ r) x hx
  · intro x hx
    exact hGout x (fun r _ => hx r)

end
end R44
