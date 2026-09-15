/- -- [compile-fix]
# Discharge: feature_tube_map_carries_carrier

Written proof: proof/ALIGNMENT_PROOF.md A§1. The signed-tent hypograph agrees
with the frozen Q inside each closed tube and with P off the supports.
This is an exact image equality, including recesses, support boundaries,
and all points outside the tubes. E6's whole-tile concern is addressed
pointwise; no argument only about retained interior cores is substituted.

There are no mathematical admissions. NativeGeometry supplies the actual
set identities; it does not import the outstanding mesh/area bridges.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.PerTubeHomeomorphisms -- [compile-fix]

namespace R44
open Set DischargeGeometry DischargeTube
noncomputable section

/-- Within a tube, the dividing level 0 maps exactly to the signed graph. -/
private theorem local_image_membership (r : Role) (x : E3)
    (hx : featureTubeSupport r x) : featureTubeMap r x ∈ Q ↔ x ∈ P := by
  have himage := forward_support r hx
  rw [mem_Q_iff_in_tube r _ himage, normal_forward, height_forward,
    forward_le_height_iff (height_strict r x), carrier_in_tube r x hx]

/-- Frozen field proposition. Its conclusion follows from membership
transport at every point and surjectivity of the given homeomorphism. -/
theorem feature_tube_map_carries_carrier_holds : FeatureTubeMapCarriesCarrier := by
  intro F hF
  classical
  have hmem (x : E3) : F x ∈ Q ↔ x ∈ P := by
    by_cases hs : ∃ r : Role, featureTubeSupport r x
    · obtain ⟨r, hr⟩ := hs
      rw [hF.1 r x hr]
      exact local_image_membership r x hr
    · have hout : ∀ r : Role, ¬ featureTubeSupport r x := by
        intro r hr
        exact hs ⟨r, hr⟩
      rw [hF.2 x hout]
      exact mem_Q_iff_outside hout
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact (hmem x).mpr hx
  · intro y hy
    refine ⟨F.symm y, ?_, F.apply_symm_apply y⟩
    apply (hmem (F.symm y)).mp
    simpa using hy

end
end R44
