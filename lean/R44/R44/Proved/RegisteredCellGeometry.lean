/- -- [compile-fix]
# Integer-cell transport and grid connectivity

A-L6.1, proof/ALIGNMENT_PROOF.md. Cube images are derived from the accepted
coordinatewise open-cell formula. Cell-center transport is the already
proved hierarchy helper, reused under a public name in this namespace.
No shell/atlas census is re-executed. The remaining lattice argument is an
induction on integer coordinates, not an assumption of global grid coverage.
-/
import R44.Proved.RegisteredComponentGeometry -- [compile-fix: promoted dependency]
import R44.PoseAlgebra -- [compile-fix: foundational relative-pose transport]

namespace R44.DischargeCells
open Set Generated DischargeGeometry DischargeBoxes DischargePyramid
open DischargeRegistered DischargeCollision
open scoped R44.DischargeCollision
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem realized_cellCenter {m : RigidMotion} {p : Pose} {d : V3}
    (hpframe : p.frame ∈ allFrames) (hm : RealizesPose m p) :
    m (cellCenter d) = cellCenter (cellLower p.frame p.shift d) := by
  rcases hm with ⟨hlin, horigin⟩
  have hc (i : Fin 3) :
      (m (cellCenter d)) i =
        frameActReal p.frame (cellCenter d) i + (p.shift.get i : ℝ) := by
    have hmap := congrArg (fun y : E3 => y i)
      (m.map_vadd (0 : E3) (cellCenter d))
    simp only [vadd_eq_add, add_zero] at hmap
    rw [hmap]
    change (m.linearIsometryEquiv (cellCenter d)) i + (m 0) i = _
    rw [hlin, horigin]
  rcases p with ⟨pf, ⟨tx, ty, tz⟩⟩ -- [compile-fix begin: reduce by three coordinates and the two possible signs, not 48 literal frames]
  change pf ∈ allFrames at hpframe
  apply PiLp.ext
  intro i
  fin_cases i
  · have h := hc 0
    have hj := perm_lt_three hpframe (0 : Fin 3)
    rw [frameActReal,frameCoordinate_of_lt _ hj] at h
    rcases (allFrames_data hpframe).sx with hs | hs <;>
      simp [cellCenter,cellLower,V3.get,v,hs] at h ⊢ <;> linarith
  · have h := hc 1
    have hj := perm_lt_three hpframe (1 : Fin 3)
    rw [frameActReal,frameCoordinate_of_lt _ hj] at h
    rcases (allFrames_data hpframe).sy with hs | hs <;>
      simp [cellCenter,cellLower,V3.get,v,hs] at h ⊢ <;> linarith
  · have h := hc 2
    have hj := perm_lt_three hpframe (2 : Fin 3)
    rw [frameActReal,frameCoordinate_of_lt _ hj] at h
    rcases (allFrames_data hpframe).sz with hs | hs <;>
      simp [cellCenter,cellLower,V3.get,v,hs] at h ⊢ <;> linarith
  -- [compile-fix end]


private theorem lower8_integral (p : Pose) (a : V3) (i : Fin 3) :
    lower8 p.frame (fun j => 8*p.shift.get j) a i =
      8*(cellLower p.frame p.shift a).get i := by
  fin_cases i <;> simp [lower8,cellLower,V3.get,v] <;> split_ifs <;> ring

theorem integral_openCell_image {m : RigidMotion} {p : Pose}
    (hp : p.frame∈allFrames) (hm : RealizesPose m p) (a : V3) :
    m '' openCell a 0=openCell (cellLower p.frame p.shift a) 0 := by
  have he : ∀i : Fin 3,m 0 i=((8*p.shift.get i:Int):ℝ)/8 := by
    intro i; rw [hm.2]; push_cast; ring
  rw [image_openCell hp hm.1 he]
  ext x
  simp only [openCell,Set.mem_setOf_eq]
  apply forall_congr'
  intro i
  have hcoord : ((lower8 p.frame (fun j => 8*p.shift.get j) a i : Int) : ℝ) / 8 = -- [compile-fix begin: isolate the cast/division normalization]
      ((cellLower p.frame p.shift a).get i : ℝ) := by
    rw [lower8_integral]
    push_cast
    ring
  rw [hcoord] -- [compile-fix end]

theorem integral_cube_image {m : RigidMotion} {p : Pose}
    (hp : p.frame∈allFrames) (hm : RealizesPose m p) (a : V3) :
    m '' unitCube a=unitCube (cellLower p.frame p.shift a) := by
  have hcl (a:V3) : closure (openCell a 0)=unitCube a := by
    rw [openCell_zero,unitCube_regularClosed]
  change m.toHomeomorph '' unitCube a = _ -- [compile-fix begin: expose the homeomorphism coercion for image_closure]
  rw [← hcl a, m.toHomeomorph.image_closure]
  have himg : m.toHomeomorph '' openCell a 0 =
      openCell (cellLower p.frame p.shift a) 0 := by
    change m '' openCell a 0 = _
    exact integral_openCell_image hp hm a
  rw [himg, hcl] -- [compile-fix end]

theorem placed_carrier_cells {m : RigidMotion} {p : Pose}
    (hp : p.frame∈allFrames) (hm : RealizesPose m p) :
    m '' P={x | ∃a∈body p,x∈unitCube a} := by
  ext x
  constructor
  · rintro ⟨y,⟨a,ha,hya⟩,rfl⟩
    refine ⟨cellLower p.frame p.shift a,?_,?_⟩
    · simp only [body,List.mem_eraseDups,List.mem_map]
      exact ⟨a,ha,rfl⟩
    · rw [←integral_cube_image hp hm a]
      exact ⟨y,hya,rfl⟩
  · rintro ⟨b,hb,hx⟩ -- [compile-fix begin: retain distinct names across the dependent body witness]
    have hb' : ∃ a ∈ chairCells, cellLower p.frame p.shift a = b := by
      simpa only [body, List.mem_eraseDups, List.mem_map] using hb
    obtain ⟨a, ha, hab⟩ := hb'
    subst b
    rw [←integral_cube_image hp hm a] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨y,⟨a,ha,hy⟩,rfl⟩
    -- [compile-fix end]

theorem center_mem_cube {a b : V3} (h : cellCenter a∈unitCube b) : a=b := by
  have h0 := h (0:Fin 3)
  have h1 := h (1:Fin 3)
  have h2 := h (2:Fin 3)
  have hc (n m : Int) (hlo : (m:ℝ)≤(n:ℝ)+(2:ℝ)⁻¹) -- [compile-fix]
      (hhi : (n:ℝ)+(2:ℝ)⁻¹≤(m:ℝ)+1) : n=m := by -- [compile-fix]
    have hL : (m:ℝ)<(n:ℝ)+1 := by linarith
    have hR : (n:ℝ)<(m:ℝ)+1 := by linarith
    have hm : m < n + 1 := by exact_mod_cast hL -- [compile-fix]
    have hn : n < m + 1 := by exact_mod_cast hR -- [compile-fix]
    omega
  rcases a with ⟨ax,ay,az⟩; rcases b with ⟨bx,byv,bz⟩
  simp [unitCube,cellCenter,cellCorner,scaledV3,V3.get,v] at h0 h1 h2
  have hx := hc ax bx h0.1 h0.2
  have hy := hc ay byv h1.1 h1.2
  have hz := hc az bz h2.1 h2.2
  cases hx; cases hy; cases hz; rfl -- [compile-fix]

theorem center_in_carrier {m : RigidMotion} {p : Pose} {a : V3}
    (hp : p.frame∈allFrames) (hm : RealizesPose m p) :
    cellCenter a∈m '' P ↔ a∈body p := by
  rw [placed_carrier_cells hp hm]
  constructor
  · rintro ⟨b,hb,hbcenter⟩
    simpa [center_mem_cube hbcenter] using hb
  · intro ha
    exact ⟨a,ha,interior_subset (cellCenter_mem_interior_unitCube a)⟩

/-- A realized literal pose carries each baseline cell centre into the
interior of its moved carrier. -/ -- [compile-fix: direct proved dependency after cycle removal]
theorem body_cellCenter_mem_interior {m : RigidMotion} {p : Pose} {a : V3}
    (hpframe : p.frame ∈ allFrames) (hm : RealizesPose m p)
    (ha : a ∈ body p) : cellCenter a ∈ interior (m '' P) := by
  unfold body at ha
  rw [List.mem_eraseDups] at ha
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  change cellCenter (cellLower p.frame p.shift d) ∈
    interior (m.toHomeomorph '' P)
  rw [← m.toHomeomorph.image_interior]
  refine ⟨cellCenter d, ?_, realized_cellCenter hpframe hm⟩
  exact interior_mono (by intro x hx; exact ⟨d, hd, hx⟩)
    (cellCenter_mem_interior_unitCube d)

theorem inverse_realizes {m : RigidMotion} {p : Pose}
    (hp:p.frame∈allFrames) (hm:RealizesPose m p) :
    RealizesPose m⁻¹ p.inverse := by
  have hi : RealizesPose (1:RigidMotion) rootPose := by
    constructor
    · intro x i -- [compile-fix begin: normalize the identity affine action coordinatewise]
      change x i = frameActReal identityFrame x i
      fin_cases i <;>
        simp [frameActReal, frameCoordinate, identityFrame, fr, n3, v, N3.get, V3.get]
      -- [compile-fix end]
    · intro i; fin_cases i <;> norm_num [rootPose,po,v,V3.get]
  have h := PoseAlgebra.realizesPose_relative hm hi hp -- [compile-fix]
    (by simp [rootPose,po,identityFrame,allFrames,coordinatePermutations,signTriples,fr,n3,v])
  have he : p.relative rootPose=p.inverse := by -- [compile-fix begin: prove the missing right-identity law on the finite frame domain]
    unfold Pose.relative
    let q := p.inverse
    have hqf : q.frame ∈ allFrames := by
      exact frame_transpose_member p.frame hp
    have hframe : q.frame.mul identityFrame = q.frame := by
      have hcheck : allFrames.all
          (fun f => decide (f.mul identityFrame = f)) = true := by decide
      exact of_decide_eq_true (List.all_eq_true.mp hcheck q.frame hqf)
    change q.transform rootPose = q
    rcases q with ⟨qf, ⟨qx, qy, qz⟩⟩
    unfold Pose.transform rootPose
    simp only [po] at hframe ⊢
    rw [hframe]
    congr
    have zero_get (i : Nat) : (v 0 0 0).get i = 0 := by
      rcases i with _ | i
      · rfl
      rcases i with _ | i <;> rfl
    have hzero : qf.act (v 0 0 0) = v 0 0 0 := by
      rcases qf with ⟨⟨p0,p1,p2⟩,⟨s0,s1,s2⟩⟩
      change v (s0 * (v 0 0 0).get p0) (s1 * (v 0 0 0).get p1)
        (s2 * (v 0 0 0).get p2) = v 0 0 0
      rw [zero_get, zero_get, zero_get]
      simp -- [compile-fix]
    rw [hzero]
    simp [V3.add, v]
    -- [compile-fix end]
  simpa [relativeMotion,he] using h

/-- Unit-distance grid centers are coordinate-face neighbors. -/
-- API?: EuclideanSpace.norm_sq_eq below expands the Euclidean squared norm.
theorem centers_distance_one {a b : V3} (hd : dist (cellCenter a) (cellCenter b)=1) :
    ∃i : Fin 3,∃s : Int,(s=1 ∨ s=-1) ∧ b=a.add (unitAxis i s) := by
  have hsq : ((b.x-a.x:ℤ):ℝ)^2+((b.y-a.y:ℤ):ℝ)^2+
      ((b.z-a.z:ℤ):ℝ)^2=1 := by
    have h := congrArg (fun t:ℝ => t^2) hd
    simp [dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,
      cellCenter,cellCorner,scaledV3,V3.get,v,Real.norm_eq_abs,sq_abs] at h
    push_cast
    nlinarith [h]
  have hsqZ : (b.x-a.x)^2+(b.y-a.y)^2+(b.z-a.z)^2=1 := by exact_mod_cast hsq
  have bound (n m k : Int) (he : n^2+m^2+k^2=1) : -1≤n ∧ n≤1 := by
    constructor <;> nlinarith [sq_nonneg m,sq_nonneg k]
  have hx := bound _ _ _ hsqZ
  have hy := bound (b.y-a.y) (b.x-a.x) (b.z-a.z) (by nlinarith [hsqZ])
  have hz := bound (b.z-a.z) (b.x-a.x) (b.y-a.y) (by nlinarith [hsqZ])
  generalize hex : b.x-a.x=dx at *
  generalize hey : b.y-a.y=dy at *
  generalize hez : b.z-a.z=dz at *
  have hdx0 : -1 ≤ dx := by omega -- [compile-fix begin: give interval_cases explicit named bounds]
  have hdx1 : dx ≤ 1 := by omega
  have hdy0 : -1 ≤ dy := by omega
  have hdy1 : dy ≤ 1 := by omega
  have hdz0 : -1 ≤ dz := by omega
  have hdz1 : dz ≤ 1 := by omega -- [compile-fix end]
  interval_cases dx <;> interval_cases dy <;> interval_cases dz <;>
    norm_num at hsqZ
  all_goals
    have finish (i : Fin 3) (s : Int)
        (hx : b.x=(a.add (unitAxis i s)).x)
        (hy : b.y=(a.add (unitAxis i s)).y)
        (hz : b.z=(a.add (unitAxis i s)).z) : b=a.add (unitAxis i s) := by
      cases a; cases b; simp_all [V3.add,unitAxis,v] -- [compile-fix]
    first
    | exact ⟨0,1,Or.inl rfl,finish 0 1 (by simp [V3.add,unitAxis,v]; omega)
        (by simp [V3.add,unitAxis,v]; omega) (by simp [V3.add,unitAxis,v]; omega)⟩
    | exact ⟨0,-1,Or.inr rfl,finish 0 (-1) (by simp [V3.add,unitAxis,v]; omega)
        (by simp [V3.add,unitAxis,v]; omega) (by simp [V3.add,unitAxis,v]; omega)⟩
    | exact ⟨1,1,Or.inl rfl,finish 1 1 (by simp [V3.add,unitAxis,v]; omega)
        (by simp [V3.add,unitAxis,v]; omega) (by simp [V3.add,unitAxis,v]; omega)⟩
    | exact ⟨1,-1,Or.inr rfl,finish 1 (-1) (by simp [V3.add,unitAxis,v]; omega)
        (by simp [V3.add,unitAxis,v]; omega) (by simp [V3.add,unitAxis,v]; omega)⟩
    | exact ⟨2,1,Or.inl rfl,finish 2 1 (by simp [V3.add,unitAxis,v]; omega)
        (by simp [V3.add,unitAxis,v]; omega) (by simp [V3.add,unitAxis,v]; omega)⟩
    | exact ⟨2,-1,Or.inr rfl,finish 2 (-1) (by simp [V3.add,unitAxis,v]; omega)
        (by simp [V3.add,unitAxis,v]; omega) (by simp [V3.add,unitAxis,v]; omega)⟩

/-- A native face neighbor is either in the chair or in its declared shell. -/
theorem native_neighbor (a : V3) (ha:a∈chairCells) (i : Fin 3)
    (s : Int) (hs:s=1 ∨ s=-1) :
    a.add (unitAxis i s)∈chairCells ∨ a.add (unitAxis i s)∈neighborShell := by
  classical
  by_cases hb : a.add (unitAxis i s)∈chairCells
  · exact Or.inl hb
  · apply Or.inr
    simp only [neighborShell,diff,List.mem_filter,List.mem_eraseDups]
    refine ⟨?_,by simpa using hb⟩
    apply List.mem_flatMap.mpr
    refine ⟨a,ha,List.mem_map.mpr ?_⟩
    refine ⟨(i.val,s),?_,rfl⟩
    fin_cases i <;> rcases hs with rfl|rfl <;> simp

/-- Interpret the certified surjection of native feature roles onto shell cells. -/
theorem shell_role {c : V3} (hc : c∈neighborShell) :
    ∃r : Role,featureFarCell (nativeFeatureData r)=c := by
  have hat := atlas_44 -- [compile-fix]
  have he : setEq neighborShell shellCells=true := by -- [compile-fix]
    simp only [atlasCheck,Bool.and_eq_true] at hat -- [compile-fix begin: project the first atlas conjunct directly]
    exact hat.1.1.1.1.1.1.1 -- [compile-fix end]
  have hc' : c∈shellCells := -- [compile-fix]
    List.contains_iff_mem.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp he).1 c hc) -- [compile-fix]
  have hs := registered_shell_cell_controls
  simp only [registeredShellCellControlsCheck,Bool.and_eq_true] at hs
  have heq : setEq roleFarCells shellCells=true := -- [compile-fix begin: use the certified range-indexed list directly]
    hs.1.1.1.1.2
  simp only [setEq, Bool.and_eq_true, subset] at heq
  have hfar : c ∈ roleFarCells := by
    apply List.contains_iff_mem.mp
    exact List.all_eq_true.mp heq.2 c hc'
  obtain ⟨rn, hrn, hfc⟩ := List.mem_map.mp hfar
  have hrnlt : rn < 192 := List.mem_range.mp hrn
  exact ⟨⟨rn, hrnlt⟩, by
    simpa [roleFarCells, nativeFeatureData] using hfc⟩
  -- [compile-fix end]

/-- Connectivity of the cubical lattice, proved by integer induction. -/
theorem grid_connected (W : Set V3) (h0 : v 0 0 0∈W)
    (hstep : ∀a∈W,∀i:Fin 3,∀s:Int,(s=1 ∨ s=-1) → a.add (unitAxis i s)∈W) :
    ∀a : V3,a∈W := by
  have hx (x:Int) : v x 0 0∈W := by
    induction x using Int.induction_on with
    | zero => exact h0 -- [compile-fix begin: Lean 4.31 Int.induction_on constructor names]
    | succ n ih => simpa [unitAxis,V3.add,v] using hstep _ ih 0 1 (Or.inl rfl)
    | pred n ih => simpa [unitAxis,V3.add,v, sub_eq_add_neg] using hstep _ ih 0 (-1) (Or.inr rfl)
    -- [compile-fix end]
    -- API?: Int.induction_on has zero and steps for adding/subtracting one.
  have hxy (x y:Int) : v x y 0∈W := by
    induction y using Int.induction_on with
    | zero => exact hx x -- [compile-fix begin: Lean 4.31 Int.induction_on constructor names]
    | succ n ih => simpa [unitAxis,V3.add,v] using hstep _ ih 1 1 (Or.inl rfl)
    | pred n ih => simpa [unitAxis,V3.add,v, sub_eq_add_neg] using hstep _ ih 1 (-1) (Or.inr rfl)
    -- [compile-fix end]
  rintro ⟨x,y,z⟩
  induction z using Int.induction_on with
  | zero => exact hxy x y -- [compile-fix begin: Lean 4.31 Int.induction_on constructor names]
  | succ n ih => simpa [unitAxis,V3.add,v] using hstep _ ih 2 1 (Or.inl rfl)
  | pred n ih => simpa [unitAxis,V3.add,v, sub_eq_add_neg] using hstep _ ih 2 (-1) (Or.inr rfl)
  -- [compile-fix end]

end
end R44.DischargeCells
