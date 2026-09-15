/- -- [compile-fix]
# Integrating the literal contact frames along a feature component

A-L6.1 and A-T6.3, proof/ALIGNMENT_PROOF.md; ERRATA E2. A single root is
normalized once. Subsequent shifts are integrated in that common frame.
No local-to-global orientation assumption is built into the definitions.

The small coordinate-permutation lemmas below read the literal 24-frame
encoding and use ordinary coordinate identities. They do not re-run the
contact, mate, shell or group-generation censuses, whose results are taken
from the existing named theorems. No native_decide is introduced; one kernel -- [compile-fix]
`decide` normalizes the fixed 24-frame multiplication table. -- [compile-fix]
-/
import R44.Proved.CompanionCollisionSemantics -- [compile-fix]
import R44.CollarPredicates -- [compile-fix: foundational predicates avoid a consumer cycle]
import R44.PoseAlgebra -- [compile-fix: foundational pose composition]

namespace R44.DischargeRegistered
open Set Generated DischargeCollision DischargePyramid
open scoped R44.DischargeCollision
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem group_length : orientationGroup.length=24 := by rfl

theorem group_frame_mem {f : Frame} (hf : f∈orientationGroup) : f∈allFrames := by
  have hcheck : orientationGroup.all -- [compile-fix begin: project the fixed 24-frame inclusion without a branch tree]
      (fun a => decide (a ∈ allFrames)) = true := by
    decide
  exact of_decide_eq_true (List.all_eq_true.mp hcheck f hf)
  -- [compile-fix end]

/-- The literal encoding lists every orientation-preserving cubic frame.
This reads the 6 permutations and 8 sign possibilities, not the generator
closure or a solid-placement search. -/
theorem proper_group_mem {f : Frame} (hf : f∈allFrames)
    (hp : properFrame f=true) : f∈orientationGroup := by
  have hcheck : allFrames.all (fun a => -- [compile-fix begin: project the fixed proper-frame classification without 48 branches]
      decide (properFrame a = true → a ∈ orientationGroup)) = true := by
    decide
  exact (of_decide_eq_true (List.all_eq_true.mp hcheck f hf)) hp
  -- [compile-fix end]

/-- Composition of proper-frame encodings, proved by their coordinate
identities. The indexing is not a new geometric certificate. -/
theorem group_mul {f k : Frame} (hf : f∈orientationGroup)
    (hk : k∈orientationGroup) : f.mul k∈orientationGroup := by
  have hcheck : orientationGroup.all (fun a => -- [compile-fix begin: avoid elaborating 576 `fin_cases` branches]
      orientationGroup.all (fun b => decide (a.mul b ∈ orientationGroup))) = true := by
    decide
  exact of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp hcheck f hf) k hk)
    -- [compile-fix end]

private theorem legal_properties (hatlas : atlasCheck=true) {p : Pose}
    (hp : p∈legalContacts) : p.frame∈allFrames ∧ properFrame p.frame=true := by
  have hc := registered_shell_cell_controls
  simp only [registeredShellCellControlsCheck,Bool.and_eq_true] at hc
  have hf : p.frame∈allFrames :=
    List.contains_iff_mem.mp (List.all_eq_true.mp hc.1.1.2 p hp)
  have he : setEq computedLegalContacts legalContacts=true := by
    simp only [atlasCheck] at hatlas -- [compile-fix begin: project the fifth Boolean conjunct without flattening the certificate]
    have h0 := (Bool.and_eq_true_iff.mp hatlas).1
    have h1 := (Bool.and_eq_true_iff.mp h0).1
    have h2 := (Bool.and_eq_true_iff.mp h1).1
    exact (Bool.and_eq_true_iff.mp h2).2 -- [compile-fix end]
  have hpc : p∈computedLegalContacts := by
    have hi : subset legalContacts computedLegalContacts=true :=
      (Bool.and_eq_true_iff.mp he).2 -- [compile-fix]
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hi p hp)
  have hproper : computedLegalContacts.all (properFrame ·.frame)=true := by
    simp only [atlasCheck] at hatlas -- [compile-fix begin: the proper-frame condition is the final conjunct]
    exact (Bool.and_eq_true_iff.mp hatlas).2 -- [compile-fix end]
  exact ⟨hf,List.all_eq_true.mp hproper p hpc⟩

theorem legal_group_mem (hatlas : atlasCheck=true) {p : Pose}
    (hp : p∈legalContacts) : p.frame∈orientationGroup :=
  proper_group_mem (legal_properties hatlas hp).1 (legal_properties hatlas hp).2

def poseOfRegistered {m : RigidMotion} (R : RegisteredPose m) : Pose :=
  po (getD orientationGroup R.frameIndex.val identityFrame) R.shift

theorem poseOfRegistered_realizes {m : RigidMotion} (R : RegisteredPose m) :
    RealizesPose m (poseOfRegistered R) := ⟨R.linear_eq,R.origin_eq⟩

theorem poseOfRegistered_mem {m : RigidMotion} (R : RegisteredPose m) :
    (poseOfRegistered R).frame∈orientationGroup := by
  have hlt : R.frameIndex.val<orientationGroup.length := by rw [group_length]; exact R.frameIndex.isLt
  simp only [poseOfRegistered,po]
  rw [show getD orientationGroup R.frameIndex.val identityFrame=
      orientationGroup[R.frameIndex.val] by simp [R44.getD,hlt]]
  exact List.getElem_mem _

noncomputable def registeredOfPose {m : RigidMotion} {p : Pose}
    (hp : p.frame∈orientationGroup) (hm : RealizesPose m p) : RegisteredPose m := by
  let i : Fin orientationGroup.length := -- [compile-fix begin: use noncomputable choice instead of eliminating a Prop existential into data]
    Classical.choose (List.get_of_mem hp)
  have hi : orientationGroup.get i = p.frame :=
    Classical.choose_spec (List.get_of_mem hp)
  have hi24 : i.val<24 := by simpa [group_length] using i.isLt
  refine ⟨⟨i.val,hi24⟩,p.shift,?_,hm.2⟩
  have he : getD orientationGroup i.val identityFrame=p.frame := by
    simpa [R44.getD,i.isLt] using hi
  simpa [he] using hm.1 -- [compile-fix end]

theorem registered_identity : Nonempty (RegisteredPose (1 : RigidMotion)) := by
  apply Nonempty.intro
  apply registeredOfPose (p:=rootPose)
  · simp [rootPose,po,identityFrame,orientationGroup,fr,n3,v]
  · constructor
    · intro x i -- [compile-fix begin: normalize identity affine and literal-frame actions]
      change x i = frameActReal identityFrame x i
      fin_cases i <;>
        simp [frameActReal,frameCoordinate,identityFrame,fr,n3,v,N3.get,V3.get]
      -- [compile-fix end]
    · intro i; fin_cases i <;> norm_num [rootPose,po,v,V3.get]

theorem registered_mul {m n : RigidMotion}
    (hm : Nonempty (RegisteredPose m)) (hn : Nonempty (RegisteredPose n)) :
    Nonempty (RegisteredPose (m*n)) := by
  obtain ⟨M⟩ := hm
  obtain ⟨N⟩ := hn
  have hM := poseOfRegistered_mem M
  have hN := poseOfRegistered_mem N
  exact ⟨registeredOfPose (group_mul hM hN)
    (PoseAlgebra.realizesPose_transform (poseOfRegistered_realizes M) (poseOfRegistered_realizes N) -- [compile-fix]
      (group_frame_mem hM) (group_frame_mem hN))⟩

theorem complete_mate_symm {g h : RigidMotion} {r s : Role}
    (hm : CompleteFeatureMate g r h s) : CompleteFeatureMate h s g r := by
  refine ⟨hm.1.symm,hm.2.1.symm,?_⟩
  have he := hm.2.2
  omega

theorem adjacent_atlas (honly : OnlyRegisteredMates Q)
    {T : Tiling Q} {g h : RigidMotion} (hadj : FeatureAdjacent T g h) :
    AtlasRelated g h := by
  rcases hadj with ⟨hg,hh,hne,hm|hm⟩
  · exact honly T g h hg hh hne hm
  · obtain ⟨r,s,hm⟩ := hm
    exact honly T g h hg hh hne ⟨s,r,complete_mate_symm hm⟩

/-- Integrate the whole finite path in ONE common ambient frame. -/
theorem component_registered (honly : OnlyRegisteredMates Q) (hatlas : atlasCheck=true)
    {T : Tiling Q} {g h : RigidMotion} (hc : SameFeatureComponent T g h) :
    Nonempty (RegisteredPose (g⁻¹*h)) := by
  induction hc using Relation.ReflTransGen.trans_induction_on with -- [compile-fix begin: use the endpoint-explicit transitive recursor]
  | refl a => simpa using registered_identity
  | @single a b hab =>
      obtain ⟨p,hp,hr⟩ := adjacent_atlas honly hab
      exact ⟨registeredOfPose (legal_group_mem hatlas hp) hr⟩
  | @trans a b c hab hbc ihab ihbc =>
      have hreg := registered_mul ihab ihbc
      have heq : (a⁻¹*b)*(b⁻¹*c)=a⁻¹*c := by group
      rw [heq] at hreg
      exact hreg
      -- [compile-fix end]

end
end R44.DischargeRegistered
