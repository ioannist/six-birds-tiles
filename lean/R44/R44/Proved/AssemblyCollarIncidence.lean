/- -- [compile-fix]
# The all-owner incidence argument for a registered atlas baseline packing

A§1/R§8--9, ERRATA E2 and E6. This file does not assume a physical Q tiling.
The only packing used is the GIVEN P-baseline packing. Opposite port
profiles come from atlas_44. A tube cannot change any third tile, including
through a different protrusion: supports at different eighth-grid sites are
positively separated. No mesh, local companion, or alignment premise is used.
-/
import R44.Proved.PairedCollarMaps -- [compile-fix: promoted dependency]

namespace R44.DischargeCollarIncidence
open Set Generated DischargeGeometry DischargeTube DischargePyramid
open DischargeCollision DischargeRegistered DischargeCells DischargeSites
open DischargePanels DischargeCollarMaps
open scoped R44.DischargeCollision
noncomputable section
set_option maxHeartbeats 0

variable {A : Set RigidMotion} (B : AtlasBaselineTiling A)

private theorem v3_ext {a b : V3} (hx : a.x=b.x) (hy : a.y=b.y)
    (hz : a.z=b.z) : a=b := by
  cases a; cases b; simp_all -- [compile-fix: V3 has no registered ext theorem]

def reg : Registration B.tiling := Classical.choice B.registered

def pose (g : RigidMotion) (hg : g∈A) : Pose :=
  let r := (reg B).pose g (B.placements_eq.symm ▸ hg)
  po (getD orientationGroup r.frameIndex identityFrame) r.shift

 theorem pose_frame (g : RigidMotion) (hg : g∈A) : (pose B g hg).frame∈allFrames := by
  apply group_frame_mem
  have hi := ((reg B).pose g (B.placements_eq.symm ▸ hg)).frameIndex.isLt
  simp only [pose,po] -- [compile-fix begin: expose the in-range list lookup before applying membership]
  rw [show getD orientationGroup
      ((reg B).pose g (B.placements_eq.symm ▸ hg)).frameIndex.val identityFrame =
      orientationGroup[((reg B).pose g
        (B.placements_eq.symm ▸ hg)).frameIndex.val] by
    simp [R44.getD,show ((reg B).pose g
      (B.placements_eq.symm ▸ hg)).frameIndex.val<orientationGroup.length by
        simpa [group_length] using hi] <;> rfl]
  exact List.getElem_mem _ -- [compile-fix end]

 theorem pose_realizes (g : RigidMotion) (hg : g∈A) :
    RealizesPose ((reg B).ambient*g) (pose B g hg) := by
  exact ⟨((reg B).pose g (B.placements_eq.symm ▸ hg)).linear_eq,
    ((reg B).pose g (B.placements_eq.symm ▸ hg)).origin_eq⟩

include B -- [compile-fix: these propositions infer the baseline only from their proof bodies]

 theorem relative_integral (g h : RigidMotion) (hg : g∈A) (hh : h∈A) :
    ∃p : Pose,p.frame∈allFrames ∧ RealizesPose (relativeMotion g h) p := by
  let p := (pose B g hg).relative (pose B h hh)
  refine ⟨p,?_,?_⟩
  · exact frame_mul_member _ _
      (frame_transpose_member _ (pose_frame B g hg)) (pose_frame B h hh)
  · have hp := PoseAlgebra.realizesPose_relative (pose_realizes B g hg) -- [compile-fix]
      (pose_realizes B h hh) (pose_frame B g hg) (pose_frame B h hh)
    simpa [relativeMotion,mul_assoc] using hp

 theorem relative_disjoint (g h : RigidMotion) (hg : g∈A) (hh : h∈A)
    (hne : g≠h) : Disjoint (interior P) (interior ((relativeMotion g h) '' P)) := by
  have hd := B.tiling.disjoint_interiors
    (B.placements_eq.symm ▸ hg) (B.placements_eq.symm ▸ hh) hne
  rw [Set.disjoint_left] at hd ⊢ -- [compile-fix begin: carry a hypothetical overlap forward by g]
  intro x hx hy
  have hhset : g '' ((relativeMotion g h) '' P)=h '' P := by
    ext x
    simp [relativeMotion,AffineIsometryEquiv.coe_mul]
  have hgmem : g x∈interior (g '' P) := by
    have hm : g.toHomeomorph x∈g.toHomeomorph '' interior P := ⟨x,hx,rfl⟩
    rw [g.toHomeomorph.image_interior P] at hm
    exact hm
  have hhmem : g x∈interior (h '' P) := by
    have hm : g.toHomeomorph x∈
        g.toHomeomorph '' interior ((relativeMotion g h) '' P) := ⟨x,hy,rfl⟩
    rw [g.toHomeomorph.image_interior ((relativeMotion g h) '' P)] at hm
    rw [←hhset]
    exact hm
  exact hd hgmem hhmem -- [compile-fix end]

omit B -- [compile-fix: the following native coordinate facts do not depend on the baseline]

 theorem centers_injective : Function.Injective featureCenter := by
  intro r s he
  have hr : r.val<nativeFeatures.length := by rw [native_features_length]; exact r.isLt
  have hs : s.val<nativeFeatures.length := by rw [native_features_length]; exact s.isLt
  have hc : (nativeFeatureData r).center8=(nativeFeatureData s).center8 := by
    apply v3_ext -- [compile-fix]
    all_goals
      first
      | have h := congrArg (fun x:E3 => x 0) he
        simp [featureCenter,scaledV3,V3.get] at h; exact_mod_cast (by linarith : _)
      | have h := congrArg (fun x:E3 => x 1) he
        simp [featureCenter,scaledV3,V3.get] at h; exact_mod_cast (by linarith : _)
      | have h := congrArg (fun x:E3 => x 2) he
        simp [featureCenter,scaledV3,V3.get] at h; exact_mod_cast (by linarith : _)
  have hget : (nativeFeatures.map Feature.center8).get
      ⟨r.val,by simpa using hr⟩ =
      (nativeFeatures.map Feature.center8).get ⟨s.val,by simpa using hs⟩ := by
    simpa [nativeFeatureData,R44.getD,hr,hs] using hc
  exact Fin.ext (congrArg Fin.val (native_feature_centers_nodup.injective_get hget))
  -- API?: List.Nodup.injective_get is injectivity of the Fin-indexed get map.

 theorem center_support (r : Role) : featureTubeSupport r (featureCenter r) := by
  simp [featureTubeSupport,featureRadius,featureNormalCoordinate,
    frameCoordinate,eta]

 theorem center_in_carrier (r : Role) : featureCenter r∈P := by
  rw [carrier_in_tube r _ (center_support r)]
  simp [featureNormalCoordinate,frameCoordinate]

 theorem center8_data {m : RigidMotion} {p : Pose}
    (hp : p.frame∈allFrames) (hm : RealizesPose m p) (r s : Role)
    (hc : m (featureCenter s)=featureCenter r) :
    (nativeFeatureData r).center8=
      (p.frame.act (nativeFeatureData s).center8).add (p.shift.smul 8) := by
  rw [placed_center hp hm] at hc
  apply v3_ext -- [compile-fix]
  all_goals
    first
    | have h := congrArg (fun x:E3 => x 0) hc
      simp [featureCenter,scaledV3,center8,V3.get] at h
      exact_mod_cast (by linarith : _)
    | have h := congrArg (fun x:E3 => x 1) hc
      simp [featureCenter,scaledV3,center8,V3.get] at h
      exact_mod_cast (by linarith : _)
    | have h := congrArg (fun x:E3 => x 2) hc
      simp [featureCenter,scaledV3,center8,V3.get] at h
      exact_mod_cast (by linarith : _)

 theorem normal_data {m : RigidMotion} {p : Pose}
    (hp : p.frame∈allFrames) (hm : RealizesPose m p) (r s : Role)
    (hn : m.linearIsometryEquiv (featureNormal s)= -featureNormal r) :
    (nativeFeatureData r).normal=(p.frame.act (nativeFeatureData s).normal).neg := by
  rw [featureNormal,frame_on_scaled _ _ hp hm.1,featureNormal] at hn
  apply v3_ext -- [compile-fix]
  · have h := congrArg (fun x:E3 => x 0) hn
    simp [scaledV3,V3.neg,V3.smul,V3.get,v] at h ⊢
    have hi : (p.frame.act (nativeFeatureData s).normal).x =
        -(nativeFeatureData r).normal.x := by exact_mod_cast h
    omega -- [compile-fix begin: recover the three integral coordinates]
  · have h := congrArg (fun x:E3 => x 1) hn
    simp [scaledV3,V3.neg,V3.smul,V3.get,v] at h ⊢
    have hi : (p.frame.act (nativeFeatureData s).normal).y =
        -(nativeFeatureData r).normal.y := by exact_mod_cast h
    omega
  · have h := congrArg (fun x:E3 => x 2) hn
    simp [scaledV3,V3.neg,V3.smul,V3.get,v] at h ⊢
    have hi : (p.frame.act (nativeFeatureData s).normal).z =
        -(nativeFeatureData r).normal.z := by exact_mod_cast h
    omega -- [compile-fix end]

include B -- [compile-fix: the remaining assembly propositions use the baseline in their proofs]
/-- No label is supplied: a different baseline carrier that meets a tube
must bring its own native port at the same physical site. -/
theorem touching_tube_has_site (g h : RigidMotion) (hg : g∈A) (hh : h∈A)
    (hne : g≠h) (r : Role) {x : E3}
    (hx : x∈g '' {z | featureTubeSupport r z}) (hxP : x∈h '' P) :
    ∃s : Role,h (featureCenter s)=g (featureCenter r) ∧
      (relativeMotion g h).linearIsometryEquiv (featureNormal s)= -featureNormal r := by
  obtain ⟨p,hp,hm⟩ := relative_integral B g h hg hh
  have hd := relative_disjoint B g h hg hh hne
  have hroot : featureTubeSupport r (g.symm x) := by
    simpa only [rigid_image_iff,Set.mem_setOf_eq] using hx -- [compile-fix: reduce set-builder membership]
    -- API?: image membership under an equivalence equals membership of its inverse.
  have hother : g.symm x∈(relativeMotion g h) '' P := by
    obtain ⟨y,hy,rfl⟩ := hxP
    exact ⟨y,hy,rfl⟩
  have hfar := tube_meets_far hp hm hd r hroot hother
  obtain ⟨s,hc,hn⟩ := far_owner_has_role hp hm hd r hfar
  refine ⟨s,?_,hn⟩
  have he := congrArg g hc
  simpa [relativeMotion] using he

/-- Same sites have the same physical map. In the same tile this uses center
injectivity; in different tiles it uses two-cell incidence and atlas profiles. -/
theorem equal_site_maps (g h : RigidMotion) (hg : g∈A) (hh : h∈A)
    (r s : Role) (hc : g (featureCenter r)=h (featureCenter s)) :
    movedMap g r=movedMap h s := by
  by_cases he : g=h
  · subst h
    have hrs : r=s := centers_injective (g.injective hc)
    subst s; rfl
  obtain ⟨p,hp,hm⟩ := relative_integral B g h hg hh
  have hd := relative_disjoint B g h hg hh he
  have hcx : featureTubeSupport r (featureCenter r) := center_support r
  have hother : featureCenter r∈(relativeMotion g h) '' P := by
    refine ⟨featureCenter s,center_in_carrier s,?_⟩
    simpa [relativeMotion] using congrArg g.symm hc.symm
  have hfar := tube_meets_far hp hm hd r hcx hother
  obtain ⟨s',hcs',hns'⟩ := far_owner_has_role hp hm hd r hfar
  have hcs : (relativeMotion g h) (featureCenter s)=featureCenter r := by
    simpa [relativeMotion] using congrArg g.symm hc.symm
  have hss : s'=s := centers_injective ((relativeMotion g h).injective (hcs'.trans hcs.symm))
  subst s'
  have ht : touch rootPose p=true := far_implies_touch r hfar
    (packed_cells_disjoint hp hm hd _ (near_mem r))
  obtain ⟨q,hq,hmq⟩ := B.atlas_faces hg hh he ⟨p,hp,hm,ht⟩
  have hqf := group_frame_mem (legal_group_mem atlas_44 hq)
  have hscoeff := profile_at_shared_site hq r s
    (center8_data hqf hmq r s hcs) (normal_data hqf hmq r s hns')
  apply Homeomorph.ext
  intro x
  have hh' := native_opposite_maps hqf hmq r s hcs hns' hscoeff (h.symm x)
  have hh'' := congrArg g hh'
  simpa [movedMap_apply,relativeMotion] using hh''.symm

/-- If a tile has no role at this site, its entire closed baseline body
misses the tube. This is the all-owner part of ERRATA E6. -/
theorem no_site_no_carrier (g h : RigidMotion) (hg : g∈A) (hh : h∈A)
    (r : Role) (hn : ∀s : Role,h (featureCenter s)≠g (featureCenter r)) :
    Disjoint (g '' {z | featureTubeSupport r z}) (h '' P) := by
  rw [Set.disjoint_left]
  intro x hx hxP
  have hne : g≠h := by intro he; subst h; exact hn r rfl
  obtain ⟨s,hc,_⟩ := touching_tube_has_site B g h hg hh hne r hx hxP
  exact hn s hc

/-- Coincident centers determine coincident supports in the common frame;
no choice of a normal sign is needed for this equality of sets. -/
theorem equal_site_supports (g h : RigidMotion) (hg : g∈A) (hh : h∈A)
    (r s : Role) (hc : g (featureCenter r)=h (featureCenter s)) :
    g '' {z | featureTubeSupport r z}=h '' {z | featureTubeSupport s z} := by
  let e := (reg B).ambient
  have heq : (e*g) '' {z | featureTubeSupport r z}=
      (e*h) '' {z | featureTubeSupport s z} := by
    rw [native_tube_cube,native_tube_cube,
      cubic_cube_image (pose_frame B g hg) (pose_realizes B g hg),
      cubic_cube_image (pose_frame B h hh) (pose_realizes B h hh)]
    congr 1
    exact congrArg e hc
  ext x
  have hgx : x∈g '' {z | featureTubeSupport r z} ↔
      e x∈(e*g) '' {z | featureTubeSupport r z} := by
    simp [rigid_image_iff,AffineIsometryEquiv.coe_mul]
  have hhx : x∈h '' {z | featureTubeSupport s z} ↔
      e x∈(e*h) '' {z | featureTubeSupport s z} := by
    simp [rigid_image_iff,AffineIsometryEquiv.coe_mul]
  rw [hgx,hhx,heq]

/-- Distinct site supports cannot intersect after ONE common registration. -/
theorem site_supports_disjoint (g h : RigidMotion) (hg : g∈A) (hh : h∈A)
    (r s : Role) (hc : g (featureCenter r)≠h (featureCenter s)) :
    Disjoint (g '' {z | featureTubeSupport r z})
      (h '' {z | featureTubeSupport s z}) := by
  rw [Set.disjoint_left]
  intro x hx hy
  let e := (reg B).ambient
  have hgx : e x∈(e*g) '' {z | featureTubeSupport r z} := by
    obtain ⟨z,hz,rfl⟩ := hx; exact ⟨z,hz,rfl⟩
  have hhx : e x∈(e*h) '' {z | featureTubeSupport s z} := by
    obtain ⟨z,hz,rfl⟩ := hy; exact ⟨z,hz,rfl⟩
  rw [placed_support_cube (pose_frame B g hg) (pose_realizes B g hg)] at hgx
  rw [placed_support_cube (pose_frame B h hh) (pose_realizes B h hh)] at hhx
  have hdiff : center8 (pose B g hg) r≠center8 (pose B h hh) s := by
    intro heq
    apply hc
    apply e.injective
    rw [←show (e*g) (featureCenter r)=e (g (featureCenter r)) from rfl,
      ←show (e*h) (featureCenter s)=e (h (featureCenter s)) from rfl,
      placed_center (pose_frame B g hg) (pose_realizes B g hg),
      placed_center (pose_frame B h hh) (pose_realizes B h hh),heq]
  have hdist := site_separation hdiff hgx hhx
  norm_num at hdist

omit B -- [compile-fix: this native support fact is baseline-independent]

 theorem moved_preserves_support (g : RigidMotion) (r : Role) {x : E3}
    (hx : x∈g '' {z | featureTubeSupport r z}) :
    movedMap g r x∈g '' {z | featureTubeSupport r z} := by
  obtain ⟨z,hz,rfl⟩ := hx
  exact ⟨featureTubeMap r z,forward_support r hz,by simp⟩

include B -- [compile-fix: restore the assembly baseline for the all-owner statement]

/-- Full physical membership for every tile, not just the two selected
owners. The no-site case also excludes protrusions from another tube. -/
theorem all_owner_membership (g : RigidMotion) (hg : g∈A) (r : Role)
    {x : E3} (hx : x∈g '' {z | featureTubeSupport r z})
    (h : RigidMotion) (hh : h∈A) :
    movedMap g r x∈h '' Q ↔ x∈h '' P := by
  by_cases hs : ∃s : Role,h (featureCenter s)=g (featureCenter r)
  · obtain ⟨s,hs⟩ := hs
    rw [equal_site_maps B g h hg hh r s hs.symm]
    have hsup : x∈h '' {z | featureTubeSupport s z} := by
      rwa [←equal_site_supports B g h hg hh r s hs.symm]
    obtain ⟨z,hz,rfl⟩ := hsup
    simpa [movedMap_apply] using native_local_membership s hz
  · have hn : ∀s : Role,h (featureCenter s)≠g (featureCenter r) := by simpa using hs
    have hpempty := no_site_no_carrier B g h hg hh r hn
    have hxp : x∉h '' P := fun hhx => Set.disjoint_left.mp hpempty hx hhx
    have hfx := moved_preserves_support g r hx
    have hfp : movedMap g r x∉h '' P :=
      fun hhx => Set.disjoint_left.mp hpempty hfx hhx
    have hout : ∀s : Role,¬featureTubeSupport s (h.symm (movedMap g r x)) := by
      intro s hss
      have hdis := site_supports_disjoint B g h hg hh r s (Ne.symm (hn s))
      exact Set.disjoint_left.mp hdis hfx
        ⟨h.symm (movedMap g r x),hss,h.apply_symm_apply _⟩
    have hiff := mem_Q_iff_outside hout
    have hnotq : movedMap g r x∉h '' Q := by
      intro hhx
      have hxq : h.symm (movedMap g r x)∈Q :=
        (rigid_image_iff h Q _).mp hhx -- [compile-fix begin: transport image membership explicitly]
      exact hfp ((rigid_image_iff h P _).mpr (hiff.mp hxq))
    constructor
    · exact fun hbad => (hnotq hbad).elim
    · exact fun hbad => (hxp hbad).elim -- [compile-fix end]

end
end R44.DischargeCollarIncidence
