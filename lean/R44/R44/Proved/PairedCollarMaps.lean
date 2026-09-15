/- -- [compile-fix]
# Matched panel profiles induce the same physical homeomorphism

A§1, R§8--9, ERRATA E2/E6. This is an exact pointwise identity for the
GLOBAL native tube formulas. Opposite normal and opposite height cancel;
the cutoff is even and the tangential square norm is invariant under D4.
The profile comparison is extracted from atlas_44, not re-enumerated.
No local companion/alignment theorem or admitted mesh bridge is imported.
-/
import R44.Proved.PanelIncidence -- [compile-fix: promoted dependency]

namespace R44.DischargeCollarMaps
open Set Generated DischargeGeometry DischargeCharts DischargeTube
open DischargePyramid DischargeCollision DischargeRegistered DischargeCells
open DischargeSites DischargePanels
open scoped R44.DischargeCollision
noncomputable section
set_option maxHeartbeats 0 -- [compile-fix: retain the delivery's unbounded allowance after profiling]
set_option maxRecDepth 1000000

theorem rigid_image_iff (g : RigidMotion) (S : Set E3) (x : E3) :
    x∈g '' S ↔ g.symm x∈S := by
  constructor
  · rintro ⟨y,hy,rfl⟩; simpa using hy
  · intro hx; exact ⟨g.symm x,hx,g.apply_symm_apply x⟩

def movedMap (g : RigidMotion) (r : Role) : E3 ≃ₜ E3 :=
  (g.toHomeomorph.symm.trans (tubeHomeomorph r)).trans g.toHomeomorph

@[simp] theorem movedMap_apply (g : RigidMotion) (r : Role) (x : E3) :
    movedMap g r x=g (featureTubeMap r (g.symm x)) := rfl

def squareNorm (w : E3) : ℝ := max |w 0| (max |w 1| |w 2|)

private theorem integral_axis_cases (r : Role) :
    (nativeFeatureData r).normal=v 1 0 0 ∨
    (nativeFeatureData r).normal=v (-1) 0 0 ∨
    (nativeFeatureData r).normal=v 0 1 0 ∨
    (nativeFeatureData r).normal=v 0 (-1) 0 ∨
    (nativeFeatureData r).normal=v 0 0 1 ∨
    (nativeFeatureData r).normal=v 0 0 (-1) := by
  obtain ⟨i, hi⟩ := native_feature_chart_classification r -- [compile-fix begin: reuse the accepted kernel classifier]
  dsimp at hi
  rcases hi with hi | hi | hi
  · rcases hi with ⟨hn, _⟩
    fin_cases i
    · exact Or.inr (Or.inl (by simpa [unitAxis,V3.get,v] using hn))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [unitAxis,V3.get,v] using hn))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa [unitAxis,V3.get,v] using hn)))))
  · rcases hi with ⟨hn, _⟩
    fin_cases i
    · exact Or.inl (by simpa [unitAxis,V3.get,v] using hn)
    · exact Or.inr (Or.inr (Or.inl (by simpa [unitAxis,V3.get,v] using hn)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [unitAxis,V3.get,v] using hn)))))
  · rcases hi with ⟨hn, _⟩
    fin_cases i
    · exact Or.inl (by simpa [unitAxis,V3.get,v] using hn)
    · exact Or.inr (Or.inr (Or.inl (by simpa [unitAxis,V3.get,v] using hn)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [unitAxis,V3.get,v] using hn))))) -- [compile-fix end]

private theorem normal_shape (r : Role) :
    featureNormal r=pt 1 0 0 ∨ featureNormal r=pt (-1) 0 0 ∨
    featureNormal r=pt 0 1 0 ∨ featureNormal r=pt 0 (-1) 0 ∨
    featureNormal r=pt 0 0 1 ∨ featureNormal r=pt 0 0 (-1) := by
  rcases integral_axis_cases r with h|h|h|h|h|h -- [compile-fix begin: coerce the six accepted integral cases]
  · left; rw [featureNormal,h]; ext i; fin_cases i <;> norm_num [scaledV3,V3.get,v,pt]
  · right; left; rw [featureNormal,h]; ext i; fin_cases i <;> norm_num [scaledV3,V3.get,v,pt]
  · right; right; left; rw [featureNormal,h]; ext i; fin_cases i <;> norm_num [scaledV3,V3.get,v,pt]
  · right; right; right; left; rw [featureNormal,h]; ext i; fin_cases i <;> norm_num [scaledV3,V3.get,v,pt]
  · right; right; right; right; left; rw [featureNormal,h]; ext i; fin_cases i <;> norm_num [scaledV3,V3.get,v,pt]
  · right; right; right; right; right; rw [featureNormal,h]
    ext i; fin_cases i <;> norm_num [scaledV3,V3.get,v,pt] -- [compile-fix end]

private theorem native_axis_cases (r : Role) :
    (nativeFeatureData r).normal=v 1 0 0 ∨
    (nativeFeatureData r).normal=v (-1) 0 0 ∨
    (nativeFeatureData r).normal=v 0 1 0 ∨
    (nativeFeatureData r).normal=v 0 (-1) 0 ∨
    (nativeFeatureData r).normal=v 0 0 1 ∨
    (nativeFeatureData r).normal=v 0 0 (-1) :=
  integral_axis_cases r -- [compile-fix: reuse the accepted classifier]

theorem normal_inner (r : Role) (x : E3) :
    featureNormalCoordinate r x=inner ℝ (x-featureCenter r) (featureNormal r) := by
  rcases native_axis_cases r with h|h|h|h|h|h <;>
    simp [featureNormalCoordinate,featureAxis,featureAxisOf,h,featureNormal,
      scaledV3,frameCoordinate,EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct,Fin.sum_univ_succ,V3.get,v]
    -- API?: EuclideanSpace.inner_eq_star_dotProduct is the finite coordinate
    -- formula for the real inner product; `rfl`/`simp [PiLp.inner_apply]` is
    -- an equivalent API route, not an extra geometric assertion.

theorem radius_projection (r : Role) (x : E3) :
    featureRadius r x=squareNorm
      ((x-featureCenter r)-(featureNormalCoordinate r x) • featureNormal r) := by
  rcases native_axis_cases r with h|h|h|h|h|h <;>
    simp [featureRadius,squareNorm,featureNormalCoordinate,featureTangentAxes,
      featureAxis,featureAxisOf,h,featureNormal,scaledV3,frameCoordinate,
      V3.get,v,max_comm,max_left_comm,max_assoc,abs_nonneg] <;>
    exact max_comm _ _ -- [compile-fix: close the two remaining max permutations]

private theorem frame_squareNorm (f : Frame) (hf : f∈allFrames)
    (L : E3 ≃ₗᵢ[ℝ] E3) (hL : ∀x i,L x i=frameActReal f x i) (x : E3) :
    squareNorm (L x)=squareNorm x := by
  have h0 := hL x 0; have h1 := hL x 1; have h2 := hL x 2
  obtain ⟨p,hp,s,hs,hf⟩ := by simpa only
    [allFrames,List.mem_flatMap,List.mem_map] using hf
  subst f
  simp only [coordinatePermutations,List.mem_cons,List.mem_singleton,
    List.not_mem_nil,or_false] at hp -- [compile-fix: eliminate the current explicit nil tail]
  simp only [signTriples,List.mem_cons,List.mem_singleton,
    List.not_mem_nil,or_false] at hs -- [compile-fix]
  have hsign : (s.x=-1 ∨ s.x=1) ∧ (s.y=-1 ∨ s.y=1) ∧
      (s.z=-1 ∨ s.z=1) := by -- [compile-fix begin: separate the eight sign cases from the six permutations]
    rcases hs with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> simp [v]
  have hxabs (a : ℝ) : |(s.x:ℝ)*a|=|a| := by
    rcases hsign.1 with h|h <;> rw [h] <;> norm_num
  have hyabs (a : ℝ) : |(s.y:ℝ)*a|=|a| := by
    rcases hsign.2.1 with h|h <;> rw [h] <;> norm_num
  have hzabs (a : ℝ) : |(s.z:ℝ)*a|=|a| := by
    rcases hsign.2.2 with h|h <;> rw [h] <;> norm_num
  rcases hp with (rfl|rfl|rfl|rfl|rfl|rfl) <;>
    simp [squareNorm,h0,h1,h2,frameActReal,frameCoordinate,fr,n3,v,N3.get,
      V3.get,hxabs,hyabs,hzabs,max_comm,max_left_comm,max_assoc]
  all_goals
    first
    | exact (max_left_comm _ _ _).symm
    | rw [max_comm (|x 2|),max_assoc,max_left_comm] -- [compile-fix end]

/-- This changes neither the solid nor its local formulas. -/
theorem opposite_chart_coordinates {m : RigidMotion} {p : Pose}
    (hp : p.frame∈allFrames) (hm : RealizesPose m p) (r s : Role)
    (hc : m (featureCenter s)=featureCenter r)
    (hn : m.linearIsometryEquiv (featureNormal s)= -featureNormal r)
    (x : E3) :
    featureNormalCoordinate r (m x)= -featureNormalCoordinate s x ∧
    featureRadius r (m x)=featureRadius s x := by
  have hd : m x-featureCenter r=m.linearIsometryEquiv (x-featureCenter s) := by
    rw [←hc] -- [compile-fix begin: state affine displacement via vsub explicitly]
    simpa only [vsub_eq_sub] using (m.map_vsub x (featureCenter s)).symm -- [compile-fix end]
  have hn' : featureNormal r= -m.linearIsometryEquiv (featureNormal s) := by
    rw [hn]; simp
  have hz : featureNormalCoordinate r (m x)= -featureNormalCoordinate s x := by
    rw [normal_inner,normal_inner,hd,hn',inner_neg_right]
    rw [m.linearIsometryEquiv.inner_map_map]
    -- API?: LinearIsometryEquiv.inner_map_map preserves the real inner product.
  refine ⟨hz,?_⟩
  rw [radius_projection,radius_projection,hd,hz,hn']
  have he :
      m.linearIsometryEquiv (x-featureCenter s)-
          (-featureNormalCoordinate s x) • (-m.linearIsometryEquiv (featureNormal s))=
      m.linearIsometryEquiv
        ((x-featureCenter s)-featureNormalCoordinate s x • featureNormal s) := by
    simp [map_sub,map_smul] -- [compile-fix: normalize both nested linear-map operations]
  rw [he]
  exact frame_squareNorm p.frame hp m.linearIsometryEquiv hm.1 _

/-- Equal geometric site and complementary profile give identical conjugate
maps, INCLUDING support boundaries and points outside the supports. -/
theorem native_opposite_maps {m : RigidMotion} {p : Pose}
    (hp : p.frame∈allFrames) (hm : RealizesPose m p) (r s : Role)
    (hc : m (featureCenter s)=featureCenter r)
    (hn : m.linearIsometryEquiv (featureNormal s)= -featureNormal r)
    (ha : profileCoefficient s= -profileCoefficient r) (x : E3) :
    m (featureTubeMap s x)=featureTubeMap r (m x) := by
  obtain ⟨hz,hr⟩ := opposite_chart_coordinates hp hm r s hc hn x
  have hh : featureHeight s x= -featureHeight r (m x) := by
    simp [featureHeight,hr,ha,Int.cast_neg]; ring
  have hcut : tubeCutoff (featureNormalCoordinate s x)=
      tubeCutoff (featureNormalCoordinate r (m x)) := by
    simp [tubeCutoff,hz]
  conv_lhs => rw [featureTubeMap,add_comm] -- [compile-fix begin: expose vector-first affine addition]
  change m ((tubeCutoff (featureNormalCoordinate s x) * featureHeight s x) •
    featureNormal s +ᵥ x) = _
  rw [m.map_vadd] -- [compile-fix end]
  simp only [vadd_eq_add,map_smul]
  rw [hn,hh,hcut]
  simpa [featureTubeMap, add_comm] -- [compile-fix: commute the final vector sum]

/-- The six exposed faces are recovered from their two cells. -/
private theorem exposed_face_mem (p : Pose) (a : V3) (ha : a∈body p)
    (i : Fin 3) (s : Int) (hs : s=1 ∨ s= -1)
    (hb : a.add (unitAxis i s)∉body p) :
    {axis := i.val, center2 := ((a.smul 2).add (v 1 1 1)).add (unitAxis i s),
      outward := s : Face}∈faces p := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_filterMap.mpr ?_⟩
  refine ⟨(i.val,s),?_,?_⟩
  · fin_cases i <;> rcases hs with rfl|rfl <;> simp
  · simp [List.contains_iff_mem,hb]

/-- A whole-tile touching relation follows from opposite OWNED boundary
cells. The nonownership premise rules out an internal face of the second body. -/
theorem far_implies_touch {p : Pose} (r : Role) (hf : farCell r∈body p)
    (hn : nearCell r∉body p) : touch rootPose p=true := by
  obtain ⟨i,s,hs,he,o,ho,hc⟩ := native_marked r
  have nearRoot : nearCell r∈body rootPose := by
    simpa [body,rootPose,po,cellLower,identityFrame,Frame.act,fr,n3,
      N3.get,V3.get,v] using near_mem r
  have farNotRoot : farCell r∉body rootPose := by
    simpa [body,rootPose,po,cellLower,identityFrame,Frame.act,fr,n3,
      N3.get,V3.get,v] using far_not_mem r
  have rev : (farCell r).add (unitAxis i (-s))=nearCell r := by
    rw [he] -- [compile-fix begin: prove V3 equality by constructors; no extensionality theorem is registered]
    rcases nearCell r with ⟨x,y,z⟩
    fin_cases i <;> rcases hs with rfl|rfl <;>
      simp [V3.add,unitAxis,v] -- [compile-fix end]
  let f : Face := {
    axis := i.val
    center2 := (((nearCell r).smul 2).add (v 1 1 1)).add (unitAxis i s)
    outward := s } -- [compile-fix: current record-field parser layout]
  let f' : Face := {
    axis := i.val
    center2 := (((farCell r).smul 2).add (v 1 1 1)).add (unitAxis i (-s))
    outward := -s } -- [compile-fix]
  have h0 : f∈faces rootPose :=
    exposed_face_mem rootPose _ nearRoot i s hs (by simpa [←he] using farNotRoot)
  have h1 : f'∈faces p :=
    exposed_face_mem p _ hf i (-s) (by rcases hs with rfl|rfl <;> simp)
      (by simpa [rev] using hn)
  unfold touch
  apply List.any_eq_true.mpr
  refine ⟨f,h0,List.any_eq_true.mpr ⟨f',h1,?_⟩⟩
  have hec : f.center2=f'.center2 := by
    dsimp [f,f']; rw [he]
    rcases nearCell r with ⟨x,y,z⟩ -- [compile-fix begin: prove V3 equality by constructors]
    fin_cases i <;> rcases hs with rfl|rfl <;>
      simp [V3.add,V3.smul,unitAxis,v] <;> ring -- [compile-fix end]
  simp only [oppositeFaces] -- [compile-fix begin: use the centre equality before unfolding the local records]
  rw [hec]
  simp [f,f'] -- [compile-fix end]

private theorem data_mem (r : Role) : nativeFeatureData r∈nativeFeatures := by
  have hr : r.val<nativeFeatures.length := by rw [native_features_length]; exact r.isLt
  simp [nativeFeatureData,R44.getD,hr,List.getElem_mem]

private theorem coefficient_at_role (r : Role) :
    getD certificateProfile (nativeFeatureData r).role 0=profileCoefficient r := by
  have h := profile_canonical
  simp only [profileCanonicalCheck,profileCanonicalCheckWith] at h -- [compile-fix begin: project the certified literal equality directly]
  have he : certificateProfile=panelProfile := by
    have h0 := (Bool.and_eq_true_iff.mp h).1
    have hh : (certificateProfile==panelProfile)=true :=
      (Bool.and_eq_true_iff.mp h0).2
    simpa using hh
    -- [compile-fix end]
  rw [he]
  have lit : nativeFeatures.map Feature.coefficient=panelProfile := by rfl
  rw [←lit]
  have hr : (nativeFeatureData r).role=r.val := by
    have hlen : r.val < nativeFeatures.length := by -- [compile-fix begin: structural index proof avoids expanding 192 roles]
      rw [native_features_length]
      exact r.isLt
    have hd : nativeFeatureData r = nativeFeatures[r.val] := by
      simp [nativeFeatureData,R44.getD,hlen]
    rw [hd]
    have hroles : nativeFeatures.map Feature.role=List.range 192 := by rfl
    have hg := congrArg (fun xs : List Nat => xs[r.val]?) hroles
    simp [hlen,r.isLt] at hg
    exact hg -- [compile-fix end]
  rw [hr]
  have hb : r.val<nativeFeatures.length := by rw [native_features_length]; exact r.isLt
  simp [R44.getD,hb,nativeFeatureData,profileCoefficient]

/-- Only the already proved atlas is used to read matchingProfile. -/
theorem atlas_matching {p : Pose} (hp : p∈legalContacts) :
    matchingProfile certificateProfile p=true := by
  have h := atlas_44
  simp only [atlasCheck] at h -- [compile-fix begin: project the fifth atlas conjunct directly]
  have h0 := (Bool.and_eq_true_iff.mp h).1
  have h1 := (Bool.and_eq_true_iff.mp h0).1
  have h2 := (Bool.and_eq_true_iff.mp h1).1
  have he : setEq computedLegalContacts legalContacts=true :=
    (Bool.and_eq_true_iff.mp h2).2 -- [compile-fix end]
  have hc : p∈computedLegalContacts :=
    List.contains_iff_mem.mp
      (List.all_eq_true.mp (Bool.and_eq_true_iff.mp he).2 p hp) -- [compile-fix: current Bool conjunction API]
  exact (List.mem_filter.mp hc).2

 theorem profile_at_shared_site {p : Pose} (hp : p∈legalContacts)
    (r s : Role)
    (hc : (nativeFeatureData r).center8=
      (p.frame.act (nativeFeatureData s).center8).add (p.shift.smul 8))
    (hn : (nativeFeatureData r).normal=
      (p.frame.act (nativeFeatureData s).normal).neg) :
    profileCoefficient s= -profileCoefficient r := by
  have hall := atlas_matching hp
  unfold matchingProfile at hall
  have hr := List.all_eq_true.mp hall _ (data_mem r)
  have hs : {nativeFeatureData s with
      center8 := (p.frame.act (nativeFeatureData s).center8).add (p.shift.smul 8),
      normal := p.frame.act (nativeFeatureData s).normal}∈movedFeatures p 8 := by
    exact List.mem_map.mpr ⟨nativeFeatureData s,data_mem s,rfl⟩
  have hh := List.all_eq_true.mp hr _ hs
  have axis : sameAxis (nativeFeatureData r).normal
      (p.frame.act (nativeFeatureData s).normal)=true := by
    have hn' : p.frame.act (nativeFeatureData s).normal=
        (nativeFeatureData r).normal.neg := by
      rw [hn] -- [compile-fix begin: expose the double native negation componentwise]
      rcases hact : p.frame.act (nativeFeatureData s).normal with ⟨x,y,z⟩
      simp [hact,V3.neg,V3.smul,v] -- [compile-fix end]
    rw [hn']
    rcases native_axis_cases r with h|h|h|h|h|h <;>
      simp [h,sameAxis,V3.neg,V3.smul,V3.get,v] -- [compile-fix: reduce the six signed axes]
  simp only [coincidentPort,←hc,beq_self_eq_true,axis,Bool.true_and,ite_true] at hh
  rw [coefficient_at_role r,coefficient_at_role s] at hh
  have he : profileCoefficient r= -profileCoefficient s := by simpa using hh
  omega

 theorem native_local_membership (r : Role) {x : E3}
    (hx : featureTubeSupport r x) : featureTubeMap r x∈Q ↔ x∈P := by
  rw [mem_Q_iff_in_tube r _ (forward_support r hx),normal_forward,height_forward,
    forward_le_height_iff (height_strict r x),carrier_in_tube r x hx]

end
end R44.DischargeCollarMaps
