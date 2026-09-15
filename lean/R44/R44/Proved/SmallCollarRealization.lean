/- -- [compile-fix]
# Discharge attempt: small_collar_realization

R§8--9 and A§1/A-L6.2; ERRATA E2 and E6. The passage from the local
paired-panel data to an actual GLOBAL HOMEOMORPHISM and then a physical
TILING is proved here. In particular the inverse is glued and whole-tile
images are checked. No volume-density shortcut is used.

The frozen statement is unchanged. -- [compile-fix: exchange 6 proved
registered_assembly_collar_data and discharged this endpoint]
-/
import R44.Proved.AssemblyCollarData -- [compile-fix: promoted dependency]

namespace R44.DischargeAssembly
open Set
noncomputable section

/-- Derive the whole-space homeomorphism from genuinely local data. -/
theorem realize_collars (A : Set RigidMotion) (D : CollarData A) :
    ∃G : E3 ≃ₜ E3,∀g∈A,G '' (g '' P)=g '' Q := by
  obtain ⟨G,hGin,hGout⟩ := DischargeSeparatedGlue.glue
    D.support D.map (1/16:ℝ) (by norm_num) D.separated D.fixes_outside
  refine ⟨G,?_⟩
  have hpoint (g : RigidMotion) (hg:g∈A) (x:E3) :
      G x∈g '' Q ↔ x∈g '' P := by
    by_cases hx : ∃i,x∈D.support i
    · obtain ⟨i,hi⟩ := hx
      rw [hGin i x hi]
      exact D.local_membership i x hi g hg
    · have hn : ∀i,x∉D.support i := by simpa using hx
      rw [hGout x hn]
      exact (D.outside_membership x hn g hg).symm
  intro g hg
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hpoint g hg x).mpr hx
  · intro hy
    refine ⟨G.symm y,?_,G.apply_symm_apply y⟩
    exact (hpoint g hg (G.symm y)).mp (by simpa using hy)

/-- No premise here asserts that the Q copies already form a packing. -/
theorem physical_tiling_of_collars (A : Set RigidMotion)
    (B : RegisteredBaselineTiling A) (D : CollarData A) :
    ∃T : Tiling Q,T.placements=A := by
  obtain ⟨G,hG⟩ := realize_collars A D
  let T : Tiling Q := {
    placements := A
    disjoint_interiors := by
      intro g h hg hh hne
      have hg' : g ∈ B.tiling.placements := by -- [compile-fix begin: rewrite dependent membership explicitly]
        rw [B.placements_eq]
        exact hg
      have hh' : h ∈ B.tiling.placements := by
        rw [B.placements_eq]
        exact hh
      have hd := B.tiling.disjoint_interiors
        hg' hh' hne
      -- [compile-fix end]
      have hdi : Disjoint (G '' interior (g '' P)) (G '' interior (h '' P)) :=
        (Set.disjoint_image_iff G.injective).mpr hd
        -- API?: disjoint images under an injective map iff disjoint sources.
      simpa only [G.image_interior,hG g hg,hG h hh] using hdi
    covers := by
      intro x
      obtain ⟨g,hg,hx⟩ := B.tiling.covers (G.symm x)
      have hgA : g∈A := by simpa only [B.placements_eq] using hg -- [compile-fix]
      refine ⟨g,hgA,?_⟩
      rw [←hG g hgA]
      exact ⟨G.symm x,hx,G.apply_symm_apply x⟩ }
  exact ⟨T,rfl⟩

end
end R44.DischargeAssembly

namespace R44
noncomputable section

theorem small_collar_realization_holds : HasTubeHomeomorphism → SmallCollarRealization := by
  intro hH A B
  obtain ⟨D⟩ := DischargeAssembly.registered_assembly_collar_data hH A B
  exact DischargeAssembly.physical_tiling_of_collars A B.toRegisteredBaselineTiling D

end
end R44
