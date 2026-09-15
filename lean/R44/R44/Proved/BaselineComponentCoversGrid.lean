/- -- [compile-fix: promoted to Proved after exchange 7]
# Discharge: baseline_component_covers_grid

A-L6.1 in proof/ALIGNMENT_PROOF.md. Normalize one root, propagate certified
relative poses, and use compulsory feature companions to cross every grid
face. The resulting cell set is all Z^3 by integer induction. Erased-body
nonoverlap is proved using retained physical cores, not assumed from Q
nonoverlap. ERRATA E2 is respected: all cell coordinates below use the ONE
chosen root frame.

The frozen endpoint is unchanged. No admission is made in this file.
The local full-companion existence needed to cross a face is supplied by
ConcreteCompanions, whose two explicitly tracked bridge dependencies remain
if they have not yet been discharged. No Hypotheses record is used.
-/
import R44.Proved.ConcreteCompanions -- [compile-fix: promoted after exchange 7]
import R44.Proved.RegisteredCellGeometry -- [compile-fix: promoted dependency]

namespace R44.DischargeGridCover
open Set Generated DischargeConcrete DischargeRegistered DischargeCells
open DischargePyramid DischargeBoxes
open scoped R44.DischargeCollision
noncomputable section
set_option maxHeartbeats 0

private theorem neighbor_center_distance (a:V3) (i:Fin 3) (s:Int)
    (hs:s=1 ∨ s=-1) :
    dist (cellCenter a) (cellCenter (a.add (unitAxis i s)))=1 := by
  have he : dist (cellCenter a) (cellCenter (a.add (unitAxis i s)))^2=1 := by
    fin_cases i <;> rcases hs with rfl|rfl <;>
      simp [dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,
        cellCenter,cellCorner,scaledV3,unitAxis,V3.add,V3.get,v,Real.norm_eq_abs,sq_abs]
  nlinarith [dist_nonneg (x:=cellCenter a) (y:=cellCenter (a.add (unitAxis i s)))]

theorem component_cells_all (honly:OnlyRegisteredMates Q) (hatlas:atlasCheck=true)
    (T:Tiling Q) (g:RigidMotion) (hg:g∈T.placements) :
    ∀a:V3,∃h∈T.placements,SameFeatureComponent T g h ∧
      cellCenter a∈(g⁻¹*h) '' P := by
  let W : Set V3 := {a | ∃h∈T.placements,SameFeatureComponent T g h ∧
    cellCenter a∈(g⁻¹*h) '' P}
  have hzero : v 0 0 0∈W := by
    refine ⟨g,hg,Relation.ReflTransGen.refl,?_⟩
    simpa using (show cellCenter (v 0 0 0)∈P from
      ⟨v 0 0 0,by simp [chairCells,bits,v],
        interior_subset (cellCenter_mem_interior_unitCube _)⟩)
  apply grid_connected W hzero
  intro a ha i s hs
  obtain ⟨h,hh,hgh,ha⟩ := ha
  obtain ⟨R⟩ := component_registered honly hatlas hgh
  let p := poseOfRegistered R
  have hpf : p.frame∈allFrames := group_frame_mem (poseOfRegistered_mem R)
  have hreal : RealizesPose (g⁻¹*h) p := poseOfRegistered_realizes R
  have hbody : a∈body p := (center_in_carrier hpf hreal).mp ha
  obtain ⟨d,hd,ha⟩ := by simpa only [body,List.mem_eraseDups,List.mem_map] using hbody
  let b := a.add (unitAxis i s)
  let c := cellLower p.inverse.frame p.inverse.shift b
  have hif : p.inverse.frame∈allFrames := frame_transpose_member p.frame hpf
  have hir : RealizesPose (g⁻¹*h)⁻¹ p.inverse := inverse_realizes hpf hreal
  have hdc : (g⁻¹*h) (cellCenter d)=cellCenter a := by
    rw [realized_cellCenter hpf hreal,ha]
  have hbc : (g⁻¹*h) (cellCenter c)=cellCenter b := by
    have hc := realized_cellCenter (d:=b) hif hir
    change (g⁻¹*h)⁻¹ (cellCenter b)=cellCenter c at hc
    rw [←hc]; exact (g⁻¹*h).apply_symm_apply _
  have hdist : dist (cellCenter d) (cellCenter c)=1 := by
    rw [←(g⁻¹*h).isometry.dist_eq,hdc,hbc]
    exact neighbor_center_distance a i s hs
  obtain ⟨j,t,ht,hc⟩ := centers_distance_one hdist
  rcases native_neighbor d hd j t ht with hinside|hshell
  · have hcP : cellCenter c∈P := by
      refine ⟨c,?_,interior_subset (cellCenter_mem_interior_unitCube c)⟩
      simpa [hc] using hinside
    exact ⟨h,hh,hgh,⟨cellCenter c,hcP,hbc⟩⟩
  · have hcShell : c∈neighborShell := by simpa [hc] using hshell
    obtain ⟨r,hr⟩ := shell_role hcShell
    obtain ⟨k,hk,hkh,u,hmu,q,hq,hqr,hfar⟩ := far_owner T hh r
    have hqf : q.frame∈allFrames := group_frame_mem (legal_group_mem hatlas hq)
    have hcIn : cellCenter c∈relativeMotion h k '' P := by
      apply interior_subset
      apply body_cellCenter_mem_interior hqf hqr
      simpa [hr] using hfar
    have hcomp : SameFeatureComponent T g k := hgh.tail
      ⟨hh,hk,Ne.symm hkh,Or.inl ⟨r,u,hmu⟩⟩
    refine ⟨k,hk,hcomp,?_⟩
    obtain ⟨y,hy,he⟩ := hcIn
    refine ⟨y,hy,?_⟩
    have h := congrArg (g⁻¹*h) he
    rw [hbc] at h
    simpa [relativeMotion,mul_assoc] using h

private theorem integral_relative_eighth {A h k : RigidMotion}
    (hh:Nonempty (RegisteredPose (A*h))) (hk:Nonempty (RegisteredPose (A*k))) :
    EighthGridMotion (relativeMotion h k) := by
  obtain ⟨H⟩ := hh
  obtain ⟨K⟩ := hk
  let p := poseOfRegistered H
  let q := poseOfRegistered K
  have hp := group_frame_mem (poseOfRegistered_mem H)
  have hq := group_frame_mem (poseOfRegistered_mem K)
  have hr := PoseAlgebra.realizesPose_relative (poseOfRegistered_realizes H) -- [compile-fix: direct foundational namespace]
    (poseOfRegistered_realizes K) hp hq
  have he : relativeMotion (A*h) (A*k)=relativeMotion h k := by
    dsimp [relativeMotion]; group
  rw [he] at hr
  refine ⟨(p.relative q).frame,
    frame_mul_member _ _ (frame_transpose_member _ hp) hq,hr.1,?_⟩
  intro i
  refine ⟨8*(p.relative q).shift.get i,?_⟩
  rw [hr.2]; push_cast; ring

theorem component_baselines_disjoint (honly:OnlyRegisteredMates Q)
    (hatlas:atlasCheck=true) (T:Tiling Q) (g:RigidMotion)
    {h k:RigidMotion} (hh:h∈T.placements) (hk:k∈T.placements)
    (hgh:SameFeatureComponent T g h) (hgk:SameFeatureComponent T g k) (hne:h≠k) :
    Disjoint (interior ((g⁻¹*h) '' P)) (interior ((g⁻¹*k) '' P)) := by
  rw [Set.disjoint_left]
  intro x hxh hxk
  have ht (a:RigidMotion) :
      g '' interior ((g⁻¹*a) '' P)=interior (a '' P) := by
    change g.toHomeomorph '' interior ((g⁻¹*a) '' P) = _ -- [compile-fix begin: expose the homeomorphism coercion]
    rw [g.toHomeomorph.image_interior]
    change interior (g '' ((g⁻¹*a) '' P)) = _
    rw [Set.image_image] -- [compile-fix end]
    simp
  have hbase : (interior (h '' P)∩interior (k '' P)).Nonempty := by
    refine ⟨g x,?_,?_⟩
    · rw [←ht h]; exact ⟨x,hxh,rfl⟩
    · rw [←ht k]; exact ⟨x,hxk,rfl⟩
  have hgrid := integral_relative_eighth
    (component_registered honly hatlas hgh) (component_registered honly hatlas hgk)
  obtain ⟨y,hyh,hyk⟩ := -- [compile-fix]
    retained_core_overlap_holds DischargePolyhedral.Q_object mates_census h k hgrid hbase -- [compile-fix]
  exact Set.disjoint_left.mp (T.disjoint_interiors hh hk hne) hyh hyk

end
end R44.DischargeGridCover

namespace R44
open Set Generated DischargeGridCover DischargeRegistered DischargeCells
noncomputable section

theorem baseline_component_covers_grid_holds :
    OnlyRegisteredMates Q → atlasCheck = true → BaselineComponentCoversGrid Q := by
  intro honly hatlas T g hg
  refine ⟨g⁻¹,by group,?_,?_,?_⟩
  · intro h _ hcomp
    exact component_registered honly hatlas hcomp
  · intro x
    let a := v (Int.floor (x 0)) (Int.floor (x 1)) (Int.floor (x 2))
    have hx : x∈unitCube a := by
      intro i
      fin_cases i <;> exact ⟨Int.floor_le _,(Int.lt_floor_add_one _).le⟩
      -- API?: real floor inequalities: ↑⌊x⌋≤x and x<↑⌊x⌋+1.
    obtain ⟨h,hh,hcomp,hcenter⟩ := component_cells_all honly hatlas T g hg a
    obtain ⟨R⟩ := component_registered honly hatlas hcomp
    have hf := group_frame_mem (poseOfRegistered_mem R)
    have hr := poseOfRegistered_realizes R
    refine ⟨h,hh,hcomp,?_⟩
    rw [placed_carrier_cells hf hr]
    exact ⟨a,(center_in_carrier hf hr).mp hcenter,hx⟩
  · intro h k hh hk hgh hgk hne
    exact component_baselines_disjoint honly hatlas T g hh hk hgh hgk hne

end
end R44
