/- -- [compile-fix]
# Discharge: only_registered_mates

A-L5.3 in proof/ALIGNMENT_PROOF.md. This is the exhaustive compulsory-
companion argument, not the weaker assertion that an unmatched face is
illegal. The role-sensitive certificate interpretation is in
CompanionCollisionSemantics. Owner 1 uses the inverse physical/literal pose.
Every option is taken from the original unpruned isolated-mate set.

The frozen premises are unchanged. The RetainedCoreOverlap premise is
redundant because RetainedBoxGeometry explicitly exhibits physical core
intersections for the boxes of this certificate. No generic or mesh bridge
is imported: WholeFeatureCompanions, rigidity and discreteness are used only
as the existing frozen premises. There are no mathematical admissions.
-/
import R44.Proved.CompanionCollisionSemantics -- [compile-fix]

namespace R44
open Set Generated DischargeCollision DischargeBoxes DischargePyramid
open scoped R44.DischargeCollision
noncomputable section
set_option maxHeartbeats 0

theorem only_registered_mates_holds :
    WholeFeatureCompanions Q → FeatureContainmentRigidity Q → CompanionPoseDiscrete Q →
      RetainedCoreOverlap Q → matesCensusCheck = true → OnlyRegisteredMates Q := by
  intro hwhole hrigid hdiscrete _hcore hc T g h hg hh hne hmate
  obtain ⟨r,s,hmate⟩ := hmate
  have hformula := hdiscrete.2 T g h hg hh hne r s hmate
  obtain ⟨p,hpf,hp,hpair⟩ := formula_pair_literal hc hformula
  have hpiso : p∈isolatedMates := by
    apply isolated_of_pair hpair
    cases he : baselineOverlap8 rootEighth p with
    | false => rfl
    | true =>
      exfalso
      exact collision_contradicts_packing T hg hh hne
        (p:=rootEighth) (q:=p)
        (by simp [rootEighth,po,identityFrame,allFrames,coordinatePermutations,signTriples,fr,n3,v])
        hpf (by simpa [relativeMotion] using eighth_root) hp he
  have hfine : p∈fineAtlas8 := by
    by_contra hnot
    obtain ⟨w,hw,he⟩ := rejection_for hc hpiso hnot
    obtain ⟨howner,hrole,_hnorm,hnotother,hcollision⟩ := witness_semantics hc hw
    let role : Role := ⟨w.role,hrole⟩
    rcases howner with howner | howner
    · obtain ⟨k,hk,hkg,q,hqf,hq,hoption⟩ :=
        actual_role_option hwhole hrigid hdiscrete hc T g hg role
      have hnp : normalizedOther w=p := by simp [normalizedOther,howner,he]
      have hkp : k≠h := by
        intro hkh
        subst k
        have heqp : q=p := eighth_pose_unique hqf hpf hq hp
        apply hnotother
        simpa [role,hnp,heqp] using hoption
      have hov : baselineOverlap8 p q=true := by
        simpa [hnp] using hcollision q hoption
      exact collision_contradicts_packing T hh hk (Ne.symm hkp)
        hpf hqf hp hq hov
    · obtain ⟨k,hk,hkh,q,hqf,hq,hoption⟩ :=
        actual_role_option hwhole hrigid hdiscrete hc T h hh role
      have hnp : normalizedOther w=p.inverse := by
        simp [normalizedOther,howner,he]
      have hinv : RealizesEighthPose (relativeMotion h g) p.inverse := by
        have heq : relativeMotion h g=(relativeMotion g h)⁻¹ := by
          dsimp [relativeMotion]; group
        rw [heq]
        exact eighth_inverse hpf hp
      have hinvf : p.inverse.frame∈allFrames :=
        frame_transpose_member p.frame hpf
      have hkg : k≠g := by
        intro hkg
        subst k
        have heqp : q=p.inverse := eighth_pose_unique hqf hinvf hq hinv
        apply hnotother
        simpa [role,hnp,heqp] using hoption
      have hov : baselineOverlap8 p.inverse q=true := by
        simpa [hnp] using hcollision q hoption
      exact collision_contradicts_packing T hg hk (Ne.symm hkg)
        hinvf hqf hinv hq hov
  obtain ⟨q,hq,hqp⟩ := List.mem_map.mp hfine
  subst p
  refine ⟨q,hq,hp.1,?_⟩
  intro i
  have hz := hp.2 i
  fin_cases i <;> simpa [po,V3.smul,V3.get,v] using hz

end
end R44
