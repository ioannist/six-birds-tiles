/- -- [compile-fix]
# Explicit collision witnesses for the frozen eighth-grid census

A-L5.1 and A-L5.3, proof/ALIGNMENT_PROOF.md. The first coordinate and core
lemmas are reused (with public names in a new namespace) from the accepted
F1 RetainedCoreOverlap implementation in the pinned tree. The additions
interpret boxes8 and produce points in actual physical interiors. No finite
search is performed and no certificate is re-evaluated.
-/
import R44.Proved.NativeGeometry -- [compile-fix]
import R44.Proved.CubicFrameAlgebra -- [compile-fix]

namespace R44.DischargeBoxes
open Set Generated DischargeGeometry DischargePyramid
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private local instance : LawfulBEq V3 where -- [compile-fix begin: expose the derived equality law needed by List.mem_eraseDups]
  eq_of_beq := by
    intro a b h
    rcases a with ⟨ax, ay, az⟩
    rcases b with ⟨bx, byv, bz⟩
    unfold instBEqV3 instBEqV3.beq at h
    simp at h
    simp_all
  rfl := by
    intro a
    rcases a with ⟨ax, ay, az⟩
    unfold instBEqV3 instBEqV3.beq
    simp -- [compile-fix end]

def openCell (a : V3) (δ : ℝ) : Set E3 :=
  {x | ∀ i : Fin 3, (a.get i : ℝ) + δ < x i ∧
    x i < (a.get i : ℝ) + 1 - δ}

theorem openCell_isOpen (a : V3) (δ : ℝ) : IsOpen (openCell a δ) := by
  rw [show openCell a δ = ⋂ i : Fin 3, {x : E3 | -- [compile-fix]
      (a.get i : ℝ) + δ < x i ∧ x i < (a.get i : ℝ) + 1 - δ} by -- [compile-fix]
    ext x; simp [openCell]] -- [compile-fix]
  -- API?: expected Mathlib lemma: finite intersections of open sets are open.
  apply isOpen_iInter_of_finite
  intro i
  have hcoord : Continuous (fun x : E3 => x i) := -- [compile-fix]
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i -- [compile-fix]
  exact (isOpen_lt continuous_const hcoord).inter -- [compile-fix]
    (isOpen_lt hcoord continuous_const) -- [compile-fix]

theorem openCell_zero (a : V3) : openCell a 0 = interior (unitCube a) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  let B : Set (Fin 3 → ℝ) :=
    Set.univ.pi fun i => Set.Icc (a.get i : ℝ) ((a.get i : ℝ) + 1)
  have hpre : unitCube a = e ⁻¹' B := by
    ext x
    simp only [unitCube, B, e, PiLp.homeomorph, WithLp.equiv, -- [compile-fix]
      Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, -- [compile-fix]
      true_implies, Set.mem_Icc] -- [compile-fix]
    rfl -- [compile-fix]
  rw [hpre, ← e.preimage_interior]
  have hInt : interior B =
      Set.univ.pi (fun i : Fin 3 => -- [compile-fix]
        Set.Ioo (a.get i : ℝ) ((a.get i : ℝ) + 1)) := by -- [compile-fix]
    dsimp [B]
    rw [interior_pi_set Set.finite_univ]
    simp
  rw [hInt]
  ext x
  simp [openCell, e, PiLp.homeomorph, WithLp.equiv]

/-- The core avoids every tube, because the normal plane of a tube has an
integer coordinate. This checks the actual set-defined Q, not an abstract
claim that a mesh has the right volume. -/
theorem core_avoids_tubes {a : V3} {x : E3}
    (hx : x ∈ openCell a eta) :
    ∀ r : Role, ¬ featureTubeSupport r x := by
  intro r hr
  obtain ⟨i, k, _, hc⟩ := normal_plane_integer r
  have hnear := featureTubeSupport_coordinate_bound hr i
  rw [hc] at hnear
  obtain ⟨hlo, hhi⟩ := hx i
  by_cases hka : k ≤ a.get i
  · have hkar : (k : ℝ) ≤ (a.get i : ℝ) := by exact_mod_cast hka
    have hupper := (abs_le.mp hnear).2
    linarith
  · have hak : a.get i + 1 ≤ k := by omega
    have hakr : (a.get i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hak
    have hlower := (abs_le.mp hnear).1
    linarith

theorem core_subset_interior_Q {a : V3} (ha : a ∈ chairCells) :
    openCell a eta ⊆ interior Q := by
  apply interior_maximal
  · intro x hx
    apply (mem_Q_iff_outside (core_avoids_tubes hx)).mpr
    refine ⟨a, ha, ?_⟩
    intro i
    have hi := hx i
    have heta : 0 < eta := by norm_num [eta]
    constructor <;> linarith
  · exact openCell_isOpen a eta

/-! Finite unions of *cell interiors* are dense in the carrier. This is used
to choose a point away from internal cube faces; interior does not distribute
over a finite union, and this proof does not make that invalid replacement. -/
def closedCells (xs : List V3) : Set E3 :=
  {x | ∃ a ∈ xs, x ∈ unitCube a}
def openCells (xs : List V3) : Set E3 :=
  {x | ∃ a ∈ xs, x ∈ interior (unitCube a)}

theorem closure_openCells (xs : List V3) :
    closure (openCells xs) = closedCells xs := by
  induction xs with
  | nil => simp [openCells, closedCells]
  | cons a xs ih =>
      have ho : openCells (a :: xs) = interior (unitCube a) ∪ openCells xs := by
        ext x; simp [openCells]
      have hc : closedCells (a :: xs) = unitCube a ∪ closedCells xs := by
        ext x; simp [closedCells]
      rw [ho, hc, closure_union, unitCube_regularClosed, ih]

theorem two_open_cells {m : RigidMotion}
    (h : (interior P ∩ interior (m '' P)).Nonempty) :
    ∃ a ∈ chairCells, ∃ b ∈ chairCells,
      (interior (unitCube a) ∩ (m '' interior (unitCube b))).Nonempty := by
  obtain ⟨x, hxP, hxm⟩ := h
  let O := interior P ∩ interior (m '' P)
  have hO : IsOpen O := isOpen_interior.inter isOpen_interior
  have hxcl : x ∈ closure (openCells chairCells) := by
    rw [closure_openCells]
    exact interior_subset hxP
  obtain ⟨y, hyO, hyI⟩ := mem_closure_iff.mp hxcl O hO ⟨hxP, hxm⟩
  obtain ⟨a, ha, hya⟩ := hyI
  let Oa := interior (unitCube a) ∩ interior (m '' P)
  have hOa : IsOpen Oa := isOpen_interior.inter isOpen_interior
  have hclm : closure (m '' openCells chairCells) = m '' P := by
    change closure (m.toHomeomorph '' openCells chairCells) = _
    rw [← m.toHomeomorph.image_closure, closure_openCells]
    rfl
  have hycl : y ∈ closure (m '' openCells chairCells) := by
    rw [hclm]
    exact interior_subset hyO.2
  obtain ⟨z, hzOa, hzI⟩ := mem_closure_iff.mp hycl Oa hOa ⟨hya, hyO.2⟩
  obtain ⟨w, ⟨b, hb, hwb⟩, hwz⟩ := hzI
  exact ⟨a, ha, b, hb, z, hzOa.1, w, hwb, hwz⟩

/-! Coordinate structure of a signed frame. These are structural proofs from
`allFrames`; no scan of the mate census is used. -/
theorem sign_pm {f : Frame} (hf : f ∈ allFrames) (i : Fin 3) :
    f.sign.get i = 1 ∨ f.sign.get i = -1 := by
  unfold allFrames at hf
  obtain ⟨p, _, hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf
  simp [signTriples] at hs -- [compile-fix]
  rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    fin_cases i <;> simp [fr, V3.get, R44.v]

theorem perm_surjective {f : Frame} (hf : f ∈ allFrames) (j : Fin 3) :
    ∃ i : Fin 3, f.perm.get i = j.val := by
  unfold allFrames at hf
  obtain ⟨p, hp, hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hf
  simp [coordinatePermutations] at hp -- [compile-fix]
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl) <;> fin_cases j
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩

def lower8 (f : Frame) (z : Fin 3 → Int) (a : V3) (i : Fin 3) : Int :=
  z i + 8 * (if f.sign.get i = 1 then a.get (f.perm.get i)
    else -a.get (f.perm.get i) - 1)

theorem eighth_apply {m : RigidMotion} {f : Frame} {z : Fin 3 → Int}
    (hf : f ∈ allFrames)
    (hlin : ∀ x i, (m.linearIsometryEquiv x) i = frameActReal f x i)
    (hzero : ∀ i, m 0 i = (z i : ℝ) / 8) (x : E3) (i : Fin 3) :
    m x i = (f.sign.get i : ℝ) * x ⟨f.perm.get i, perm_lt_three hf i⟩ +
      (z i : ℝ) / 8 := by
  have hmap := congrArg (fun y : E3 => y i) (m.map_vadd (0 : E3) x)
  simp only [vadd_eq_add, add_zero] at hmap
  rw [hmap] -- [compile-fix]
  change (m.linearIsometryEquiv x) i + (m 0) i = _ -- [compile-fix]
  rw [hlin x i, hzero i] -- [compile-fix]
  rw [frameActReal, frameCoordinate_of_lt x (perm_lt_three hf i)]

/-- Coordinate image of an eroded cube under an arbitrary eighth-grid signed
frame, with arbitrary real collar δ. -/
theorem image_openCell {m : RigidMotion} {f : Frame} {z : Fin 3 → Int}
    (hf : f ∈ allFrames)
    (hlin : ∀ x i, (m.linearIsometryEquiv x) i = frameActReal f x i)
    (hzero : ∀ i, m 0 i = (z i : ℝ) / 8)
    (a : V3) (δ : ℝ) :
    m '' openCell a δ =
      {y | ∀ i : Fin 3, (lower8 f z a i : ℝ) / 8 + δ < y i ∧
        y i < (lower8 f z a i : ℝ) / 8 + 1 - δ} := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩ i
    have hxi := hx ⟨f.perm.get i, perm_lt_three hf i⟩
    rw [eighth_apply hf hlin hzero]
    rcases sign_pm hf i with hs | hs <;>
      simp [lower8, hs, Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_sub] at * <;>
      constructor <;> linarith
  · intro y hy
    let x := m.symm y
    have hxy : m x = y := m.apply_symm_apply y
    refine ⟨x, ?_, hxy⟩
    intro j
    obtain ⟨i, hij⟩ := perm_surjective hf j
    have hi : (⟨f.perm.get i, perm_lt_three hf i⟩ : Fin 3) = j := Fin.ext hij
    have hcoord := eighth_apply hf hlin hzero x i
    rw [hxy, hi] at hcoord
    have hyi := hy i
    rcases sign_pm hf i with hs | hs <;>
      simp [lower8, hs, hij, Int.cast_add, Int.cast_mul, Int.cast_neg,
        Int.cast_sub] at hcoord hyi <;>
      constructor <;> linarith


def core8 (a : V3) : Set E3 :=
  {x | ∀ i : Fin 3,(a.get i : ℝ)/8+eta < x i ∧ x i < (a.get i : ℝ)/8+1-eta}

/-- Semantic interpretation of a boxes8 member. -/
theorem core8_inside {m : RigidMotion} {p : Pose} (hf : p.frame∈allFrames)
    (hm : RealizesEighthPose m p) {a : V3} (ha : a∈boxes8 p) :
    core8 a ⊆ interior (m '' Q) := by
  rw [boxes8] at ha -- [compile-fix begin: avoid dependent elimination through eraseDups]
  obtain ⟨b,hb,hba⟩ := List.mem_map.mp ha
  rw [body,List.mem_eraseDups] at hb
  obtain ⟨c,hc,hcb⟩ := List.mem_map.mp hb
  subst b
  subst a -- [compile-fix end]
  simp only [po] at hb ⊢ -- [compile-fix]
  have he : core8 (((cellLower p.frame (v 0 0 0) c).smul 8).add p.shift) =
      m '' openCell c eta := by
    rw [image_openCell hf hm.1 hm.2]
    ext x
    simp only [core8,Set.mem_setOf_eq]
    apply forall_congr'
    intro i
    have hcoord : (((cellLower p.frame (v 0 0 0) c).smul 8).add p.shift).get i =
        lower8 p.frame (fun j : Fin 3 => p.shift.get j) c i := by
      fin_cases i <;> simp [lower8,cellLower,V3.add,V3.smul,V3.get,v] <;> omega
    rw [hcoord]
  rw [he] -- [compile-fix begin: normalize the affine-isometry coercion before image_interior]
  rw [← AffineIsometryEquiv.coe_toHomeomorph m]
  rw [←m.toHomeomorph.image_interior] -- [compile-fix end]
  exact Set.image_mono (core_subset_interior_Q hc)

/-- Nonzero eighth-grid overlap contains a point in both eroded boxes. -/
theorem boxes_overlap_core {a b : V3} (hab : boxesOverlap a b = true) :
    (core8 a ∩ core8 b).Nonempty := by
  have hi (i : Fin 3) : a.get i < b.get i+8 ∧ b.get i < a.get i+8 := by
    simp only [boxesOverlap,intervalsOverlap,Bool.and_eq_true,decide_eq_true_eq] at hab -- [compile-fix begin: preserve Bool conjunction association]
    fin_cases i <;> simp only [V3.get] <;> tauto -- [compile-fix end]
  let lo : Fin 3 → Int := fun i => max (a.get i) (b.get i)
  let up : Fin 3 → Int := fun i => min (a.get i+8) (b.get i+8)
  have hw (i : Fin 3) : lo i+1≤up i := by
    have h := hi i
    dsimp [lo,up]
    omega
  let x : E3 := WithLp.toLp 2 fun i => ((lo i:ℝ)+(up i:ℝ))/16
  have hmid (i : Fin 3) : (lo i:ℝ)/8+eta < x i ∧ x i<(up i:ℝ)/8-eta := by
    have h : (lo i:ℝ)+1≤(up i:ℝ) := by exact_mod_cast hw i
    dsimp [x]; norm_num [eta]; constructor <;> linarith
  refine ⟨x,?_,?_⟩
  all_goals
    intro i
    have hm := hmid i
    have hla : a.get i≤lo i := le_max_left _ _
    have hlb : b.get i≤lo i := le_max_right _ _
    have hua : up i≤a.get i+8 := min_le_left _ _
    have hub : up i≤b.get i+8 := min_le_right _ _
    have hlar : (a.get i:ℝ)≤(lo i:ℝ) := by exact_mod_cast hla
    have hlbr : (b.get i:ℝ)≤(lo i:ℝ) := by exact_mod_cast hlb
    have huar : (up i:ℝ)≤(a.get i:ℝ)+8 := by exact_mod_cast hua
    have hubr : (up i:ℝ)≤(b.get i:ℝ)+8 := by exact_mod_cast hub
    constructor <;> linarith

/-- A baseline-overlap Boolean yields a physical interior intersection. -/
theorem baselineOverlap8_physical {g h : RigidMotion} {p q : Pose}
    (hp : p.frame∈allFrames) (hq : q.frame∈allFrames)
    (hg : RealizesEighthPose g p) (hh : RealizesEighthPose h q)
    (hov : baselineOverlap8 p q=true) :
    (interior (g '' Q)∩interior (h '' Q)).Nonempty := by
  obtain ⟨a,ha,b,hb,hab⟩ := by
    simpa only [baselineOverlap8,List.any_eq_true] using hov
  obtain ⟨x,hxa,hxb⟩ := boxes_overlap_core hab
  exact ⟨x,core8_inside hp hg ha hxa,core8_inside hq hh hb hxb⟩

/-- Interpret the overlap-box certificate without depending on its numeric
margin checksum: nonempty firstOverlapBox already supplies positive integer
width in all three directions, and hence the fixed retained-core margin. -/
theorem collision_implies_baselineOverlap {p q : Pose}
    (h : collisionOptionValid p q=true) : baselineOverlap8 p q=true := by
  unfold collisionOptionValid at h
  split at h
  next hn => simp_all
  next box hb =>
    have hmem : box∈(boxes8 p).flatMap (fun a => -- [compile-fix begin: derive head membership from the available iff]
        (boxes8 q).filterMap (fun b => overlapBox a b)) := by
      rw [firstOverlapBox] at hb
      obtain ⟨tail,htail⟩ := List.head?_eq_some_iff.mp hb
      rw [htail]
      simp -- [compile-fix end]
    obtain ⟨a,ha,b,hb,hbox⟩ := by
      simpa only [List.mem_flatMap,List.mem_filterMap] using hmem
    dsimp only [overlapBox] at hbox -- [compile-fix begin: reduce the local let bindings before splitting]
    split at hbox
    next hwidth =>
      have hw : boxesOverlap a b=true := by
        simp only [boxesOverlap,intervalsOverlap,Bool.and_eq_true,decide_eq_true_eq] -- [compile-fix]
        simp [maxInt,minInt,v,V3.get,Bool.and_eq_true,decide_eq_true_eq] at hwidth -- [compile-fix]
        split_ifs at hwidth <;> omega
      exact List.any_eq_true.mpr ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,hw⟩⟩
    next hwidth => contradiction -- [compile-fix end]

/-- Normalize both colliding physical copies by one owner. -/
theorem collision_contradicts_packing (T : Tiling Q)
    {o g h : RigidMotion} {p q : Pose}
    (hg : g∈T.placements) (hh : h∈T.placements) (hne : g≠h)
    (hp : p.frame∈allFrames) (hq : q.frame∈allFrames)
    (hgp : RealizesEighthPose (relativeMotion o g) p)
    (hhq : RealizesEighthPose (relativeMotion o h) q)
    (hov : baselineOverlap8 p q=true) : False := by
  obtain ⟨x,hxg,hxh⟩ := baselineOverlap8_physical hp hq hgp hhq hov
  have transport (k : RigidMotion) : -- [compile-fix begin: normalize affine-isometry coercions before image_interior]
      o '' interior (relativeMotion o k '' Q)=interior (k '' Q) := by
    rw [← AffineIsometryEquiv.coe_toHomeomorph o]
    rw [o.toHomeomorph.image_interior,Set.image_image]
    simp [relativeMotion] -- [compile-fix end]
  have hyG : o x∈interior (g '' Q) := by
    rw [←transport g]; exact Set.mem_image_of_mem o hxg
  have hyH : o x∈interior (h '' Q) := by
    rw [←transport h]; exact Set.mem_image_of_mem o hxh
  exact Set.disjoint_left.mp (T.disjoint_interiors hg hh hne) hyG hyH

end
end R44.DischargeBoxes
