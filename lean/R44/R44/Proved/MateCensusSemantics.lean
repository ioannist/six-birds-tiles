/- -- [compile-fix]
# Literal-to-real meaning of the complete-feature census

Written source: proof/ALIGNMENT_PROOF.md A-C4.4 and A-FS5.2; the generator is
R44.FiniteModel.generatedMatePairs and the existing certificate is
R44.mates_census. This interprets the existing certificate, NOT a new
census. Native-role lookup, generic hash-set extensionality and real/integer
coordinate conversion are proved symbolically. The fixed record-role metadata -- [compile-fix begin: ruling R8 provenance]
is checked by the named finite theorem `R44.mate_records_roles_nonempty` under
manager ruling R8; it is not part of mateLiteralCheck's abstract conjunction.
No mate generation or collision test is rerun.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines.
-- [compile-fix end]
-/
import R44.Proved.NativeMateGeometry -- [compile-fix]
import R44.Proved.HashListSemantics -- [compile-fix]

-- [compile-fix begin: ruling R8 replaces the nonreducing delivered `rfl` by a named finite certificate]
namespace R44
open Generated

/-- The fixed string-decoded census records all carry at least one role.
The proposition is identical to the delivered metadata side condition. -/
theorem mate_records_roles_nonempty :
    (mateRecords.all fun r => !r.roles.isEmpty) = true := by
  native_decide

end R44
-- [compile-fix end]

namespace R44.DischargeMateCensus
open Set R44.Generated R44.DischargePyramid
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private instance : LawfulBEq V3 where
  eq_of_beq := by
    intro a b h; rcases a with ⟨ax,ay,az⟩; rcases b with ⟨bx,byv,bz⟩
    unfold instBEqV3 instBEqV3.beq at h
    simp at h; simp_all
  rfl := by
    intro a; rcases a with ⟨ax,ay,az⟩
    unfold instBEqV3 instBEqV3.beq; simp
private instance : LawfulBEq N3 where
  eq_of_beq := by
    intro a b h; rcases a with ⟨ax,ay,az⟩; rcases b with ⟨bx,byv,bz⟩
    unfold instBEqN3 instBEqN3.beq at h
    simp at h; simp_all
  rfl := by
    intro a; rcases a with ⟨ax,ay,az⟩
    unfold instBEqN3 instBEqN3.beq; simp
private instance : LawfulBEq Frame where
  eq_of_beq := by
    intro a b h; rcases a with ⟨ap,asg⟩; rcases b with ⟨bp,bsg⟩
    unfold instBEqFrame instBEqFrame.beq at h
    simp at h; simp_all
  rfl := by
    intro a; rcases a with ⟨ap,asg⟩
    unfold instBEqFrame instBEqFrame.beq; simp
private instance : LawfulBEq Pose where
  eq_of_beq := by
    intro a b h; rcases a with ⟨af,atr⟩; rcases b with ⟨bf,btr⟩ -- [compile-fix]
    unfold instBEqPose instBEqPose.beq at h
    simp at h; simp_all
  rfl := by
    intro a; rcases a with ⟨af,atr⟩ -- [compile-fix]
    unfold instBEqPose instBEqPose.beq; simp

-- API?: Hashable functions respect equality automatically. These instances
-- use the standard LawfulBEq ⇒ LawfulHashable instance, not a table check.
private instance : LawfulHashable Pose := inferInstance
private instance : LawfulHashable (Pose × Nat) := inferInstance

private theorem data_get (r : Role) :
    nativeFeatureData r = nativeFeatures[r.val] := by
  have hr : r.val < nativeFeatures.length := by
    rw [native_features_length]; exact r.isLt
  simp [nativeFeatureData,R44.getD,hr]

private theorem data_mem (r : Role) : nativeFeatureData r ∈ nativeFeatures := by
  rw [data_get]; exact List.getElem_mem _

private theorem data_of_mem {a : Feature} (ha : a∈nativeFeatures) :
    ∃r : Role,nativeFeatureData r=a := by
  obtain ⟨i,hi⟩ := List.get_of_mem ha
  -- API?: List.get_of_mem : a ∈ xs → ∃ i : Fin xs.length, xs.get i = a.
  let r : Role := ⟨i.val,by simpa [native_features_length] using i.isLt⟩
  exact ⟨r,by rw [data_get]; exact hi⟩

/-- This scans only the role-list metadata of the FIXED records, not the
geometric generation or census. Its named finite certificate is checked under R8. -- [compile-fix]
The metadata is necessary: an arbitrary abstract record list could append
an empty-role pose that is invisible to literalMatePairs. -/
private theorem record_roles_nonempty :
    ∀r∈mateRecords,r.roles≠[] := by
  have h : (mateRecords.all fun r => !r.roles.isEmpty) = true := by -- [compile-fix begin: identical proposition, named native_decide proof under ruling R8]
    exact R44.mate_records_roles_nonempty
    -- [compile-fix end]
  simpa [List.all_eq_true] using h


/-- Exact integer center difference used by generatedMatePairs. -/
def formulaPose (f : Frame) (u v : Role) : Pose :=
  po f ((nativeFeatureData u).center8.sub (f.act (nativeFeatureData v).center8))

/-- The geometric formula realizes its literal integer pose. This is a
real/integer transport lemma, not finite evaluation of the census. -/
theorem formula_realizes (m : RigidMotion) (u v : Role)
    (hm : FeatureMateFormula m u v) :
    ∃f∈allFrames,RealizesEighthPose m (formulaPose f u v) ∧
      f.act (nativeFeatureData v).normal=(nativeFeatureData u).normal.neg ∧
      (nativeFeatureData v).coefficient=-(nativeFeatureData u).coefficient := by
  obtain ⟨⟨f,hf,hlin,_⟩,hcoeff,hnorm,hcenter⟩ := hm
  have hn : scaledV3 1 (f.act (nativeFeatureData v).normal) =
      scaledV3 1 (nativeFeatureData u).normal.neg := by
    rw [← frame_on_scaled m.linearIsometryEquiv f hf hlin]
    change m.linearIsometryEquiv (featureNormal v)=_
    have hh := congrArg Neg.neg hnorm
    simp only [neg_neg] at hh -- [compile-fix begin: commute negation with the integer-to-real normal]
    rw [hh.symm]
    ext i
    fin_cases i <;> simp [featureNormal,scaledV3,V3.neg,V3.smul,V3.get,R44.v]
    -- [compile-fix end]
  have hnInt : f.act (nativeFeatureData v).normal=(nativeFeatureData u).normal.neg := by
    rcases hfv : f.act (nativeFeatureData v).normal with ⟨fx,fy,fz⟩ -- [compile-fix begin: use constructor injectivity; V3 has no ext theorem]
    rcases huv : (nativeFeatureData u).normal.neg with ⟨ux,uy,uz⟩
    rw [V3.mk.injEq] -- [compile-fix]
    constructor
    · have h := congrArg (fun w:E3 => w 0) hn
      simp [hfv,huv,scaledV3,V3.get] at h
      exact_mod_cast h
    constructor
    · have h := congrArg (fun w:E3 => w 1) hn
      simp [hfv,huv,scaledV3,V3.get] at h
      exact_mod_cast h
    · have h := congrArg (fun w:E3 => w 2) hn
      simp [hfv,huv,scaledV3,V3.get] at h
      exact_mod_cast h
    -- [compile-fix end]
  have hcInt : (nativeFeatureData v).coefficient=-(nativeFeatureData u).coefficient := by
    change profileCoefficient v = -profileCoefficient u
    omega
  refine ⟨f,hf,⟨hlin,?_⟩,hnInt,hcInt⟩
  intro i
  rw [hcenter,featureCenter,featureCenter,frame_on_scaled _ f hf hlin]
  fin_cases i <;>
    simp [formulaPose,po,scaledV3,V3.sub,V3.get,R44.v] <;> ring

/-- Conversely, the literal generator's normal and coefficient tests imply
the real formula; no actual tiling is required. -/
theorem realizes_formula (m : RigidMotion) (f : Frame) (hf : f∈allFrames)
    (u v : Role) (hp : RealizesEighthPose m (formulaPose f u v))
    (hn : f.act (nativeFeatureData v).normal=(nativeFeatureData u).normal.neg)
    (hc : (nativeFeatureData v).coefficient=-(nativeFeatureData u).coefficient) :
    FeatureMateFormula m u v := by
  have hlin : ∀x i,m.linearIsometryEquiv x i=frameActReal f x i := hp.1
  have horigin : m 0=featureCenter u-m.linearIsometryEquiv (featureCenter v) := by
    rw [featureCenter,featureCenter,frame_on_scaled _ f hf hlin]
    ext i
    rw [hp.2]
    fin_cases i <;> simp [formulaPose,po,scaledV3,V3.sub,V3.get,R44.v] <;> ring
  refine ⟨⟨f,hf,hlin,?_⟩,?_,?_,horigin⟩
  · intro i; exact ⟨(formulaPose f u v).shift.get i,hp.2 i⟩
  · change profileCoefficient u = -profileCoefficient v
    change profileCoefficient v = -profileCoefficient u at hc
    omega
  · change scaledV3 1 (nativeFeatureData u).normal =
      -m.linearIsometryEquiv (scaledV3 1 (nativeFeatureData v).normal)
    rw [frame_on_scaled _ f hf hlin,hn]
    ext i
    fin_cases i <;> simp [scaledV3,V3.neg,V3.smul,V3.get,R44.v]

private theorem generated_pose_projection (p : Pose) :
    (∃j : Nat,(p,j)∈generatedMatePairs) ↔
      ∃f∈allFrames,∃u v : Role,
        p=formulaPose f u v ∧
        f.act (nativeFeatureData v).normal=(nativeFeatureData u).normal.neg ∧
        (nativeFeatureData v).coefficient=-(nativeFeatureData u).coefficient := by
  classical
  constructor
  · rintro ⟨j,hj⟩
    rw [generatedMatePairs,DischargeHashLists.mem_hashDedup] at hj
    obtain ⟨f,hf,a,ha,b,hb,hif⟩ := by
      simpa only [List.mem_flatMap,List.mem_filterMap] using hj
      -- API?: mem_filterMap supplies b ∈ nativeFeatures and the option equality.
    split_ifs at hif with htest
    · obtain ⟨u,hu⟩ := data_of_mem ha
      obtain ⟨v,hv⟩ := data_of_mem hb
      have tests : f.act b.normal=a.normal.neg ∧ b.coefficient= -a.coefficient := by
        simpa using htest
      have hp := congrArg (fun q : Pose × Nat => q.1) (Option.some.inj hif)
      refine ⟨f,hf,u,v,?_,?_,?_⟩
      · simpa [formulaPose,hu,hv] using hp.symm
      · simpa [hu,hv] using tests.1
      · simpa [hu,hv] using tests.2
    -- [compile-fix begin: `split_ifs` discharges the impossible branch in the pinned tactic behavior]
    -- The delivered trailing `· contradiction` therefore had no remaining goal.
    -- [compile-fix end]
  · rintro ⟨f,hf,u,v,rfl,hn,hc⟩
    refine ⟨(nativeFeatureData u).role,?_⟩
    rw [generatedMatePairs,DischargeHashLists.mem_hashDedup]
    apply List.mem_flatMap.mpr
    refine ⟨f,hf,List.mem_flatMap.mpr ⟨nativeFeatureData u,data_mem u,?_⟩⟩
    apply List.mem_filterMap.mpr
    exact ⟨nativeFeatureData v,data_mem v,by simp [hn,hc,formulaPose]⟩

private theorem literal_pose_projection (p : Pose) :
    (∃j : Nat,(p,j)∈literalMatePairs) ↔ p∈matePoses := by
  classical
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨r,hr,k,hk,hpair⟩ := by
      simpa only [literalMatePairs,List.mem_flatMap,List.mem_map] using hj
    have hp : r.pose=p := congrArg Prod.fst hpair
    change p∈mateRecords.map MateRecord.pose
    exact List.mem_map.mpr ⟨r,hr,hp⟩
  · intro hp
    change p∈mateRecords.map MateRecord.pose at hp
    obtain ⟨r,hr,hpose⟩ := List.mem_map.mp hp
    obtain ⟨k,hk⟩ := List.exists_mem_of_ne_nil r.roles -- [compile-fix begin: pass the explicit list argument required by the pinned API]
      (record_roles_nonempty r hr)
      -- API?: expected List.exists_mem_of_ne_nil : xs ≠ [] → ∃a,a∈xs.
      -- [compile-fix end]
    refine ⟨k,?_⟩
    apply List.mem_flatMap.mpr
    exact ⟨r,hr,List.mem_map.mpr ⟨k,hk,by simp [hpose]⟩⟩

/-- Project the ALREADY CERTIFIED pair-set equality to poses. The abstract
hash equality is interpreted by the generic membership theorem, and fixed
record nonemptiness supplies the only converse projection side condition. -/
private theorem census_projection_semantics
    (_hprofile : profileCanonicalCheck = true) (hcensus : matesCensusCheck = true) :
    ∀m : RigidMotion,
      (∃f∈allFrames,∃u v : Role,
        RealizesEighthPose m (formulaPose f u v) ∧
        f.act (nativeFeatureData v).normal=(nativeFeatureData u).normal.neg ∧
        (nativeFeatureData v).coefficient=-(nativeFeatureData u).coefficient)
      ↔ CensusMatePose m := by
  have heq : hashSetEq generatedMatePairs literalMatePairs=true := by
    simp only [matesCensusCheck,matesCensusCheckWith] at hcensus -- [compile-fix begin: peel the Boolean certificate without expanding every conjunct]
    have h0 := (Bool.and_eq_true_iff.mp hcensus).1
    have h1 := (Bool.and_eq_true_iff.mp h0).1
    have h2 := (Bool.and_eq_true_iff.mp h1).1
    have h3 := (Bool.and_eq_true_iff.mp h2).1
    have h4 := (Bool.and_eq_true_iff.mp h3).1
    have h5 := (Bool.and_eq_true_iff.mp h4).1
    have h6 := (Bool.and_eq_true_iff.mp h5).1
    have h7 := (Bool.and_eq_true_iff.mp h6).1
    have h8 := (Bool.and_eq_true_iff.mp h7).1
    have hliteral := (Bool.and_eq_true_iff.mp h8).1
    simp only [mateLiteralCheck] at hliteral
    exact (Bool.and_eq_true_iff.mp hliteral).2
    -- [compile-fix end]
  have hm := DischargeHashLists.hashSetEq_membership heq
  have hproj (p : Pose) :
      (∃j : Nat,(p,j)∈generatedMatePairs) ↔ p∈matePoses := by
    rw [← literal_pose_projection]
    exact exists_congr (fun j => hm (p,j))
  intro m
  constructor
  · rintro ⟨f,hf,u,v,hr,hn,hc⟩
    exact ⟨formulaPose f u v,
      (hproj _).mp ((generated_pose_projection _).mpr ⟨f,hf,u,v,rfl,hn,hc⟩),hr⟩
  · rintro ⟨p,hp,hr⟩
    obtain ⟨f,hf,u,v,he,hn,hc⟩ :=
      (generated_pose_projection p).mp ((hproj p).mpr hp)
    exact ⟨f,hf,u,v,he ▸ hr,hn,hc⟩

/-- The first conjunct of CompanionPoseDiscrete, kept separate from its
geometric conjunct. No mathematical admission is used. -/
theorem formula_set_eq_census
    (hprofile : profileCanonicalCheck = true) (hcensus : matesCensusCheck = true) :
    {m : RigidMotion | ∃u v : Role,FeatureMateFormula m u v} =
      {m : RigidMotion | CensusMatePose m} := by
  ext m
  constructor
  · rintro ⟨u,v,hm⟩
    obtain ⟨f,hf,hpose,hn,hc⟩ := formula_realizes m u v hm
    exact (census_projection_semantics hprofile hcensus m).mp ⟨f,hf,u,v,hpose,hn,hc⟩
  · intro hm
    obtain ⟨f,hf,u,v,hpose,hn,hc⟩ := (census_projection_semantics hprofile hcensus m).mpr hm
    exact ⟨u,v,realizes_formula m f hf u v hpose hn hc⟩

end
end R44.DischargeMateCensus
