/- -- [compile-fix: promoted to Proved after exchange 7]
# Discharge: unrestricted_alignment

A-T6.3 in proof/ALIGNMENT_PROOF.md. A covering feature component leaves no
additional tile. The argument below uses regular closure and an OPEN
interior neighborhood, not the incorrect claim that a covered point must
already lie in an interior, and not a Baire assertion about uncountably many
boundaries. Registration then propagates along finite companion paths.

The exact frozen statement is preserved. -- [compile-fix: exchange 7 closes
both upstream bridges, so this endpoint is admission-free.]
-/
import R44.Proved.ConcreteCompanions -- [compile-fix: promoted after exchange 7]
import R44.Proved.RegisteredComponentGeometry -- [compile-fix: promoted dependency]

namespace R44.DischargeAlignment
open Set DischargePolyhedral DischargeRegistered
noncomputable section

/-- In a packing by regular-closed solids, a subfamily which already covers
space contains every placement. The inhabited interior is essential. -/
theorem covering_subfamily_exhausts
    (T : Tiling Q) (B : Set RigidMotion) (hB : B⊆T.placements)
    (hcover : ∀x : E3,∃h∈B,x∈h '' Q) : T.placements⊆B := by
  intro k hk
  obtain ⟨z,hz⟩ := Q_object.2.2.1
  have hx : k z∈interior (k '' Q) := by
    change k.toHomeomorph z ∈ interior (k.toHomeomorph '' Q) -- [compile-fix begin: expose homeomorphism coercions]
    rw [←k.toHomeomorph.image_interior]
    exact ⟨z,hz,rfl⟩
  obtain ⟨h,hh,hm⟩ := hcover (k z)
  by_cases hkh : k=h
  · simpa [hkh] using hh
  · have hcl : closure (interior (h '' Q))=h '' Q := by
      change closure (interior (h.toHomeomorph '' Q)) = h.toHomeomorph '' Q
      rw [←h.toHomeomorph.image_interior,←h.toHomeomorph.image_closure,
        Q_object.2.1]
      -- [compile-fix end]
    have hn : k z∈closure (interior (h '' Q)) := by -- [compile-fix]
      rw [hcl] -- [compile-fix]
      exact hm -- [compile-fix]
    have hex : (interior (k '' Q)∩interior (h '' Q)).Nonempty := by
      exact (mem_closure_iff_nhds.mp hn) (interior (k '' Q))
        (isOpen_interior.mem_nhds hx)
      -- API?: mem_closure_iff_nhds: every neighborhood meets the set.
    obtain ⟨y,hyk,hyh⟩ := hex
    exact False.elim (Set.disjoint_left.mp
      (T.disjoint_interiors hk (hB hh) hkh) hyk hyh)

end
end R44.DischargeAlignment

namespace R44
open Set DischargeAlignment DischargeRegistered
noncomputable section

theorem unrestricted_alignment_holds :
    orientationGroupCheck = true → ComponentSolidsCover Q → UnrestrictedAlignment Q := by
  intro _hgroup hcover T
  obtain ⟨g,hg,_⟩ := T.covers (0:E3)
  let B : Set RigidMotion := {h | h∈T.placements ∧ SameFeatureComponent T g h}
  have hall : T.placements⊆B := covering_subfamily_exhausts T B
    (fun _ hh => hh.1) (fun x => by -- [compile-fix begin: package component membership into B]
      obtain ⟨h, hh, hcomp, hx⟩ := hcover T g hg x
      exact ⟨h, ⟨hh, hcomp⟩, hx⟩)
    -- [compile-fix end]
  refine ⟨⟨g⁻¹,?_⟩⟩
  intro h hh
  exact Classical.choice -- [compile-fix]
    (component_registered DischargeConcrete.only_mates atlas_44 (hall hh).2) -- [compile-fix]

end
end R44
