/- -- [compile-fix]
# Role-sensitive semantics of the compulsory-companion certificate

A-FS5.2 / A-L5.3, proof/ALIGNMENT_PROOF.md. The pair (pose, ROOT ROLE), not
just pose membership, is retained when projecting the existing hash-set
certificate. Rejection options are never pruned by earlier rejections.
Owner 1 is interpreted using the actual inverse motion and inverse pose.
All Boolean facts come from matesCensusCheck; no native_decide is added.
-/
import R44.Proved.MateCensusSemantics -- [compile-fix]
import R44.Proved.RetainedBoxGeometry -- [compile-fix]
import R44.GlobalPredicates -- [compile-fix]
import R44.PoseAlgebra -- [compile-fix]

namespace R44.DischargeCollision
open R44.PoseAlgebra -- [compile-fix]
open Set Generated DischargeGeometry DischargePyramid DischargeMateCensus
open DischargeHashLists DischargeBoxes
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

scoped instance : LawfulBEq V3 where
  eq_of_beq := by intro a b h; cases a; cases b; simpa [instBEqV3,instBEqV3.beq] using h
  rfl := by intro a; cases a; simp [instBEqV3,instBEqV3.beq]
scoped instance : LawfulBEq N3 where
  eq_of_beq := by intro a b h; cases a; cases b; simpa [instBEqN3,instBEqN3.beq] using h
  rfl := by intro a; cases a; simp [instBEqN3,instBEqN3.beq]
scoped instance : LawfulBEq Frame where
  eq_of_beq := by intro a b h; cases a; cases b; simpa [instBEqFrame,instBEqFrame.beq] using h
  rfl := by intro a; cases a; simp [instBEqFrame,instBEqFrame.beq]
scoped instance : LawfulBEq Pose where
  eq_of_beq := by intro a b h; cases a; cases b; simpa [instBEqPose,instBEqPose.beq] using h
  rfl := by intro a; cases a; simp [instBEqPose,instBEqPose.beq]
open scoped R44.DischargeCollision
scoped instance : LawfulHashable Pose := inferInstance
scoped instance : LawfulHashable (Pose × Nat) := inferInstance
-- API?: the standard LawfulBEq-derived LawfulHashable instances are the
-- same container side conditions used in the accepted MateCensusSemantics.


private theorem feature_data_mem (r : Role) : nativeFeatureData r∈nativeFeatures := by
  have hr : r.val<nativeFeatures.length := by rw [native_features_length]; exact r.isLt
  have he : nativeFeatureData r=nativeFeatures[r.val] := by
    simp [nativeFeatureData,R44.getD,hr]
  rw [he]; exact List.getElem_mem _

/-- Index identity of the generated panel/slot data, not a geometry census. -/
private theorem role_index (r : Role) : (nativeFeatureData r).role=r.val := by
  have hr : r.val < nativeFeatures.length := by -- [compile-fix begin: avoid expanding 192 `fin_cases` branches]
    rw [native_features_length]
    exact r.isLt
  have hd : nativeFeatureData r = nativeFeatures[r.val] := by
    simp [nativeFeatureData, R44.getD, hr]
  rw [hd]
  have hroles : nativeFeatures.map Feature.role = List.range 192 := by
    rfl
  have hg := congrArg (fun xs : List Nat => xs[r.val]?) hroles
  simp [hr, r.isLt] at hg
  exact hg -- [compile-fix end]

private theorem pair_certificate (hc : matesCensusCheck=true) :
    hashSetEq generatedMatePairs literalMatePairs=true := by
  simp only [matesCensusCheck,matesCensusCheckWith] at hc -- [compile-fix begin: project the nested Boolean certificate without propositional expansion]
  have h0 := (Bool.and_eq_true_iff.mp hc).1
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
  exact (Bool.and_eq_true_iff.mp hliteral).2 -- [compile-fix end]

theorem formula_pair_literal (hc : matesCensusCheck=true)
    {m : RigidMotion} {u v : Role} (hm : FeatureMateFormula m u v) :
    ∃p : Pose,p.frame∈allFrames ∧ RealizesEighthPose m p ∧
      (p,u.val)∈literalMatePairs := by
  obtain ⟨f,hf,hr,hn,ha⟩ := formula_realizes m u v hm
  let p := formulaPose f u v
  have hg : (p,u.val)∈generatedMatePairs := by
    rw [generatedMatePairs,mem_hashDedup]
    refine List.mem_flatMap.mpr ⟨f,hf,List.mem_flatMap.mpr
      ⟨nativeFeatureData u,feature_data_mem u,List.mem_filterMap.mpr ?_⟩⟩
    refine ⟨nativeFeatureData v,feature_data_mem v,?_⟩
    simp [p,formulaPose,hn,ha,role_index]
  exact ⟨p,hf,hr,(hashSetEq_membership (pair_certificate hc) (p,u.val)).mp hg⟩

private theorem pair_record {p : Pose} {r : Nat} (hp : (p,r)∈literalMatePairs) :
    ∃w∈mateRecords,w.pose=p ∧ r∈w.roles := by
  obtain ⟨w,hw,i,hi,he⟩ := by
    simpa only [literalMatePairs,List.mem_flatMap,List.mem_map] using hp
  have he1 : w.pose = p := by simpa using congrArg Prod.fst he -- [compile-fix begin: expose component equalities before substitution]
  have he2 : i = r := by simpa using congrArg Prod.snd he
  subst r
  exact ⟨w,hw,he1,hi⟩ -- [compile-fix end]

theorem pair_pose_member {p : Pose} {r : Nat} (hp : (p,r)∈literalMatePairs) :
    p∈matePoses := by
  obtain ⟨w,hw,he,_⟩ := pair_record hp
  change p∈mateRecords.map MateRecord.pose
  exact List.mem_map.mpr ⟨w,hw,he⟩

theorem option_of_pair {p : Pose} {r : Role}
    (hp : (p,r.val)∈literalMatePairs) (hiso : p∈isolatedMates) :
    p∈partnerOptions r.val := by
  obtain ⟨w,hw,he,hr⟩ := pair_record hp
  have hlen : partnerTable.length=192 := by simp [partnerTable]
  have hget : partnerOptions r.val = mateRecords.filterMap (fun w =>
      if isolatedMateSet.contains w.pose && w.roles.contains r.val
      then some w.pose else none) := by
    simp [partnerOptions,partnerTable,R44.getD,r.isLt]
  rw [hget]
  refine List.mem_filterMap.mpr ⟨w,hw,?_⟩
  simp [he,hr,isolatedMateSet,Std.HashSet.contains_iff_mem,
    Std.HashSet.mem_ofList,hiso]
  -- API?: ofList membership is ordinary list membership under LawfulBEq.

theorem isolated_of_pair {p : Pose} {r : Nat}
    (hp : (p,r)∈literalMatePairs) (hn : baselineOverlap8 rootEighth p=false) :
    p∈isolatedMates := by
  exact List.mem_filter.mpr ⟨pair_pose_member hp,by simp [hn]⟩

/-- Multiplying just the translation part by eight converts eighth poses
into the existing integral RealizesPose interface; no scaling of distance. -/
def integerLift (m : RigidMotion) : RigidMotion := translation (7 • m 0)*m

private theorem integerLift_linear (m : RigidMotion) :
    (integerLift m).linearIsometryEquiv=m.linearIsometryEquiv := by
  rfl -- [compile-fix]
  -- API?: linear part of a translation is identity; the linear-part map preserves products.

private theorem integerLift_zero (m : RigidMotion) : integerLift m 0=8 • m 0 := by
  change 7 • m 0+m 0=8 • m 0
  module

theorem eighth_as_integer {m : RigidMotion} {p : Pose}
    (hm : RealizesEighthPose m p) : RealizesPose (integerLift m) p := by
  refine ⟨?_,?_⟩
  · rw [integerLift_linear]; exact hm.1
  · intro i
    rw [integerLift_zero]
    rw [show (8 • m 0) i = (8 : ℝ) * (m 0) i by simp] -- [compile-fix]
    rw [hm.2 i] -- [compile-fix]
    ring -- [compile-fix]

theorem eighth_pose_unique {m : RigidMotion} {p q : Pose}
    (hp : p.frame∈allFrames) (hq : q.frame∈allFrames)
    (hm : RealizesEighthPose m p) (hn : RealizesEighthPose m q) : p=q :=
  realizesPose_pose_unique hp hq (eighth_as_integer hm) (eighth_as_integer hn)

theorem eighth_root : RealizesEighthPose (1 : RigidMotion) rootEighth := by
  constructor
  · intro x i -- [compile-fix begin: normalize the identity affine action and literal frame]
    change x i = frameActReal identityFrame x i
    fin_cases i <;>
      simp [frameActReal,frameCoordinate,identityFrame,fr,n3,v,N3.get,V3.get]
    -- [compile-fix end]
  · intro i; fin_cases i <;> norm_num [rootEighth,po,identityFrame,fr,n3,v,V3.get]

/-- The literal inverse really is the inverse of an eighth-grid motion. -/
theorem eighth_inverse {m : RigidMotion} {p : Pose}
    (hp : p.frame∈allFrames) (hm : RealizesEighthPose m p) :
    RealizesEighthPose m⁻¹ p.inverse := by
  have hlin (x:E3) : m.linearIsometryEquiv x=frameActRealVector p.frame x := by
    ext i; exact hm.1 x i
  have hInv (x:E3) : m.linearIsometryEquiv.symm x=frameActRealVector p.frame.transpose x := by
    have h := frameActReal_transpose p.frame hp (m.linearIsometryEquiv.symm x)
    rw [←hlin,m.linearIsometryEquiv.apply_symm_apply] at h
    exact h.symm
  have hz : m⁻¹ 0= -m.linearIsometryEquiv.symm (m 0) := by
    apply m.linearIsometryEquiv.injective
    rw [map_neg,m.linearIsometryEquiv.apply_symm_apply]
    have he := m.map_vadd (0:E3) (m⁻¹ 0)
    simp only [vadd_eq_add,add_zero] at he -- [compile-fix begin: rewrite the inverse application explicitly]
    have he0 : m (m⁻¹ 0) = 0 := m.apply_symm_apply 0
    rw [he0] at he
    exact eq_neg_iff_add_eq_zero.mpr he.symm -- [compile-fix end]
  refine ⟨?_,?_⟩
  · intro x i
    change m.linearIsometryEquiv.symm x i=_
    exact congrArg (fun x:E3 => x i) (hInv x)
  · have hzero : m 0=scaledV3 8 p.shift := by ext i; exact hm.2 i
    have hiLin : ∀x i,m.linearIsometryEquiv.symm x i=
        frameActReal p.frame.transpose x i := by
      intro x i; exact congrArg (fun x:E3 => x i) (hInv x)
    rw [hz,hzero,frame_on_scaled _ p.frame.transpose
      (frame_transpose_member p.frame hp) hiLin]
    intro i
    fin_cases i <;>
      simp [Pose.inverse,po,V3.neg,V3.smul,V3.get,v,scaledV3] <;> ring

/-- An actual complete companion appears in the unpruned option list for
its ROOT ROLE. Distinctness is supplied by WholeFeatureCompanions. -/
theorem actual_role_option
    (hwhole : WholeFeatureCompanions Q) (hrigid : FeatureContainmentRigidity Q)
    (hdiscrete : CompanionPoseDiscrete Q) (hc : matesCensusCheck=true)
    (T : Tiling Q) (o : RigidMotion) (ho : o∈T.placements) (r : Role) :
    ∃ k∈T.placements,k≠o ∧ ∃q : Pose,q.frame∈allFrames ∧
      RealizesEighthPose (relativeMotion o k) q ∧ q∈partnerOptions r.val := by
  obtain ⟨k,hk,hko,_hcovers,⟨s,hs⟩,_hunq⟩ := hwhole T o ho r
  have hm := hrigid T o k ho hk (Ne.symm hko) r s hs
  have hf := hdiscrete.2 T o k ho hk (Ne.symm hko) r s hm
  obtain ⟨q,hq,hr,hpair⟩ := formula_pair_literal hc hf
  have hno : baselineOverlap8 rootEighth q=false := by
    cases he : baselineOverlap8 rootEighth q with
    | false => rfl
    | true =>
      exfalso
      apply collision_contradicts_packing T ho hk (Ne.symm hko)
        (o:=o) (p:=rootEighth) (q:=q) -- [compile-fix]
      · simp [rootEighth,po,identityFrame,allFrames,coordinatePermutations,signTriples,fr,n3,v]
      · exact hq
      · simpa [relativeMotion] using eighth_root
      · exact hr
      · exact he
  exact ⟨k,hk,hko,q,hq,hr,option_of_pair hpair (isolated_of_pair hpair hno)⟩

/-- Boolean witness contents, interpreted extensionally. -/
theorem witness_semantics (hc : matesCensusCheck=true)
    {w : RejectionWitness} (hw : w∈rejectionWitnesses) :
    (w.owner=0 ∨ w.owner=1) ∧ w.role<192 ∧
    normalizedOther w∈isolatedMates ∧
    normalizedOther w∉partnerOptions w.role ∧
    ∀q∈partnerOptions w.role,baselineOverlap8 (normalizedOther w) q=true := by
  have hall : rejectionWitnesses.all rejectionValid=true := by
    simp only [matesCensusCheck,matesCensusCheckWith] at hc -- [compile-fix begin: select the penultimate Boolean conjunct directly]
    have hprefix := (Bool.and_eq_true_iff.mp hc).1
    exact (Bool.and_eq_true_iff.mp hprefix).2 -- [compile-fix end]
  have hv := List.all_eq_true.mp hall w hw
  simp only [rejectionValid,Bool.and_eq_true,List.contains_iff_mem,
    Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq,Bool.not_eq_true] at hv -- [compile-fix]
  refine ⟨by tauto,by tauto,by tauto,?_,?_⟩
  · have hn : (partnerOptions w.role).contains (normalizedOther w)=false := by
      exact Bool.eq_false_of_not_eq_true' -- [compile-fix begin: normalize Boolean negation after selecting its conjunct]
        (a := (partnerOptions w.role).contains (normalizedOther w)) hv.1.2
        -- [compile-fix end]
    simpa using hn
  · intro q hq
    have ho : (partnerOptions w.role).all (collisionOptionValid (normalizedOther w))=true := by
      tauto
    exact collision_implies_baselineOverlap (List.all_eq_true.mp ho q hq)

/-- A pose in the isolated list which is not a fine atlas pose has a
rejection record; this uses the exact set-difference certificate. -/
theorem rejection_for (hc : matesCensusCheck=true) {p : Pose}
    (hp : p∈isolatedMates) (hn : p∉fineAtlas8) :
    ∃w∈rejectionWitnesses,w.rejected=p := by
  have he : hashSetEq (witnessRejectedSetWith rejectionWitnesses)
      (hashDiff isolatedMates fineAtlas8)=true := by
    simp only [matesCensusCheck,matesCensusCheckWith] at hc -- [compile-fix begin: select the rejected-set equality conjunct directly]
    have h0 := (Bool.and_eq_true_iff.mp hc).1
    have h1 := (Bool.and_eq_true_iff.mp h0).1
    have h2 := (Bool.and_eq_true_iff.mp h1).1
    have h3 := (Bool.and_eq_true_iff.mp h2).1
    have h4 := (Bool.and_eq_true_iff.mp h3).1
    exact (Bool.and_eq_true_iff.mp h4).2 -- [compile-fix end]
  have hd : p∈hashDiff isolatedMates fineAtlas8 := by
    simp [hashDiff,hp,hn,Std.HashSet.contains_iff_mem,Std.HashSet.mem_ofList]
  have hm := (hashSetEq_membership he p).mpr hd
  simpa only [witnessRejectedSetWith,List.mem_map] using hm

end
end R44.DischargeCollision
