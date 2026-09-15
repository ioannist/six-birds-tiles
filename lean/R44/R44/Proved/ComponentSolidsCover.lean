/- -- [compile-fix]
# Discharge: component_solids_cover

A-L6.2, proof/ALIGNMENT_PROOF.md; ERRATA E6. EXPLICIT ALTERNATIVE PROOF:
CarrierCoreCover replaces infinite tube gluing with the retained-core-density
argument. The component carriers are uniformly 1/10-close to interiors of
the component's physical Q tiles. Every additional Q tile contains a ball of
radius 1/4 and must therefore overlap one component tile. The original
Tiling.covers then proves physical component coverage. This is not an
inference from baseline coverage alone or from equal volumes.

The frozen proposition is unchanged. No mesh, generic-stratification, or
other residual hypothesis is assumed or imported. No mathematical admission.
-/
import R44.Proved.CarrierCoreCover -- [compile-fix]

namespace R44
open Set DischargeCoreCover
noncomputable section

theorem component_solids_cover_holds :
    CompactRegularClosedBall Q → BaselineComponentCoversGrid Q → ComponentSolidsCover Q := by
  intro _hobject hgrid T g hg
  obtain ⟨A,hAg,_hreg,hcover,_hdisj⟩ := hgrid T g hg
  let B : Set RigidMotion := {h | h ∈ T.placements ∧ SameFeatureComponent T g h}
  have hBP : ∀ x : E3, ∃ h ∈ B, x ∈ h '' P := by
    intro x
    obtain ⟨h,hh,hcomp,y,hy,hxy⟩ := hcover (A x)
    refine ⟨h,⟨hh,hcomp⟩,y,hy,?_⟩
    apply A.injective
    change A (h y) = A x -- [compile-fix begin: normalize rigid-motion composition by reduction]
    change A (h y) = A x at hxy
    exact hxy -- [compile-fix end]
    -- API?: expected (A*h) y = A (h y); use rfl/change if the simp name differs.
  have hall : T.placements ⊆ B :=
    carrier_cover_forces_all_members T B (fun _ h => h.1) hBP
  intro x
  obtain ⟨h,hh,hx⟩ := T.covers x
  exact ⟨h,hh,(hall hh).2,hx⟩

end
end R44
