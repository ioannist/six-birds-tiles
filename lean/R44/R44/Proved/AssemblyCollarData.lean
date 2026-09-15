/- -- [compile-fix]
# Complete registered-assembly collar data

A§1/A-L6.2 and R§8--9, proof/ALIGNMENT_PROOF.md and
proof/PROOFS_registered.md; ERRATA E2 and E6.

The frozen endpoint and CollarData record are unchanged. Sites are actual
physical feature centers, NOT oriented tile/role pairs: the latter would
count every paired tube twice. Supports are defined after the one common
registration and pulled back. Their independence of the chosen owner is
proved in support_of_owner. The local membership assertion applies to
EVERY tile, including tiles not incident to the panel.

No physical Q tiling, companion lemma, mesh lemma, or Hypotheses record is
assumed. hH is retained verbatim; the construction uses the already proved
explicit native tube homeomorphisms rather than choosing an arbitrary map
from that premise. No mathematical admission in this file or its new imports.
-/
import R44.Proved.AssemblyCollarIncidence -- [compile-fix: promoted dependency]
import R44.Proved.FeatureTubeMapsGlue -- [compile-fix]
import R44.Proved.FeatureTubeMapCarriesCarrier -- [compile-fix]
import R44.Proved.SeparatedHomeomorphismGluing -- [compile-fix: promoted dependency]

namespace R44.DischargeAssembly
open Set DischargeSites DischargeCollarMaps DischargeCollarIncidence
open DischargeGeometry DischargeTube
noncomputable section
set_option maxHeartbeats 0

/-- Unchanged local data record. In particular local_membership quantifies
all owners, not only the chosen pair. -/
structure CollarData (A : Set RigidMotion) where
  Site : Type
  support : Site → Set E3
  map : Site → E3 ≃ₜ E3
  separated : ∀i j,i≠j → ∀x∈support i,∀y∈support j,(1/16:ℝ)≤dist x y
  fixes_outside : ∀i x,x∉support i → map i x=x
  outside_membership : ∀x,(∀i,x∉support i) →
    ∀g∈A,(x∈g '' P ↔ x∈g '' Q)
  local_membership : ∀i x,x∈support i →
    ∀g∈A,(map i x∈g '' Q ↔ x∈g '' P)

private theorem image_iff (g : RigidMotion) (S : Set E3) (x : E3) :
    x∈g '' S ↔ g.symm x∈S := by
  constructor
  · rintro ⟨y,hy,rfl⟩; simpa using hy
  · intro hx; exact ⟨g.symm x,hx,g.apply_symm_apply x⟩

/-- The former assembly-incidence admission, with the statement unchanged. -/
theorem registered_assembly_collar_data
    (hH : HasTubeHomeomorphism) (A : Set RigidMotion)
    (B : AtlasBaselineTiling A) : Nonempty (CollarData A) := by
  classical
  let I := {c : E3 // ∃g∈A,∃r : Role,g (featureCenter r)=c}
  let e : RigidMotion := (reg B).ambient
  let S : I → Set E3 := fun i => e ⁻¹' cubeAt (e i.val)
  have owner : ∀i : I,∃g : RigidMotion,g∈A ∧
      ∃r : Role,g (featureCenter r)=i.val := fun i => i.property
  choose g hg r hr using owner
  let F : I → E3 ≃ₜ E3 := fun i => movedMap (g i) (r i)
  have support_of_owner (i : I) (h : RigidMotion) (hh : h∈A)
      (s : Role) (hs : h (featureCenter s)=i.val) :
      S i=h '' {x | featureTubeSupport s x} := by
    have heq : (e*h) '' {x | featureTubeSupport s x}=cubeAt (e i.val) := by
      rw [native_tube_cube,cubic_cube_image
        (pose_frame B h hh) (pose_realizes B h hh)]
      congr 1
      exact congrArg e hs
    ext x
    change e x∈cubeAt (e i.val) ↔ x∈h '' {z | featureTubeSupport s z}
    rw [←heq,image_iff,image_iff]
    have harg : (e*h).symm (e x)=h.symm x := by -- [compile-fix begin: cancel the common registration explicitly]
      apply (e*h).injective
      simp [AffineIsometryEquiv.coe_mul]
    rw [harg] -- [compile-fix end]
  refine ⟨{
    Site := I
    support := S
    map := F
    separated := ?_
    fixes_outside := ?_
    outside_membership := ?_
    local_membership := ?_
  }⟩
  · intro i j hij x hx y hy
    let a := center8 (pose B (g i) (hg i)) (r i)
    let b := center8 (pose B (g j) (hg j)) (r j)
    have ha : e i.val=scaledV3 8 a := by
      rw [←hr i]
      exact placed_center (pose_frame B (g i) (hg i))
        (pose_realizes B (g i) (hg i)) (r i)
    have hb : e j.val=scaledV3 8 b := by
      rw [←hr j]
      exact placed_center (pose_frame B (g j) (hg j))
        (pose_realizes B (g j) (hg j)) (r j)
    have hab : a≠b := by
      intro h
      apply hij
      apply Subtype.ext
      apply e.injective
      rw [ha,hb,h]
    have hxx : e x∈cubeAt (scaledV3 8 a) := by simpa only [S,Set.mem_preimage,ha] using hx
    have hyy : e y∈cubeAt (scaledV3 8 b) := by simpa only [S,Set.mem_preimage,hb] using hy
    have hd := site_separation hab hxx hyy
    rw [e.isometry.dist_eq] at hd -- [compile-fix: current affine-isometry distance API]
    linarith
  · intro i x hx
    have hout : ¬featureTubeSupport (r i) ((g i).symm x) := by
      intro h
      apply hx
      rw [support_of_owner i (g i) (hg i) (r i) (hr i)]
      exact ⟨(g i).symm x,h,(g i).apply_symm_apply x⟩
    change movedMap (g i) (r i) x=x
    rw [movedMap_apply,forward_fixed_outside (r i) _ hout] -- [compile-fix: supply the explicit point argument]
    exact (g i).apply_symm_apply x
  · intro x hx h hh
    have hout : ∀s : Role,¬featureTubeSupport s (h.symm x) := by
      intro s hs
      let i : I := ⟨h (featureCenter s),h,hh,s,rfl⟩
      apply hx i
      rw [support_of_owner i h hh s rfl]
      exact ⟨h.symm x,hs,h.apply_symm_apply x⟩
    rw [image_iff,image_iff]
    exact (mem_Q_iff_outside hout).symm
  · intro i x hx h hh
    have hx' : x∈(g i) '' {z | featureTubeSupport (r i) z} := by
      rwa [support_of_owner i (g i) (hg i) (r i) (hr i)] at hx
    exact all_owner_membership B (g i) (hg i) (r i) hx' h hh

end
end R44.DischargeAssembly
