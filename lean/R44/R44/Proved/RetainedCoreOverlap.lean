/-
# Discharge: retained_core_overlap (A-L5.1)

Follows proof/ALIGNMENT_PROOF.md §5, Lemma 5.1: a positive overlap of
integer/eighth-grid boxes has coordinate width at least 1/8; removing two
collars of width 1/100 still leaves an interior overlap. No ERRATA changes
this lemma. In particular, the proof does not use unrestricted alignment,
mesh tangent-cone semantics, an Einstein theorem, or a Hypotheses record.

The endpoint is copied verbatim from the frozen structure. Its two premises
are intentionally unused: direct cubical geometry proves the stronger fact.
No finite census or decide/native_decide computation is repeated.

This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.NativeGeometry -- [compile-fix]

namespace R44
open Set
open Generated
open DischargeGeometry
noncomputable section
set_option maxRecDepth 100000

private def openCell (a : V3) (δ : ℝ) : Set E3 :=
  {x | ∀ i : Fin 3, (a.get i : ℝ) + δ < x i ∧
    x i < (a.get i : ℝ) + 1 - δ}

private theorem openCell_isOpen (a : V3) (δ : ℝ) : IsOpen (openCell a δ) := by
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

private theorem openCell_zero (a : V3) : openCell a 0 = interior (unitCube a) := by
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
private theorem core_avoids_tubes {a : V3} {x : E3}
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

private theorem core_subset_interior_Q {a : V3} (ha : a ∈ chairCells) :
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
private def closedCells (xs : List V3) : Set E3 :=
  {x | ∃ a ∈ xs, x ∈ unitCube a}
private def openCells (xs : List V3) : Set E3 :=
  {x | ∃ a ∈ xs, x ∈ interior (unitCube a)}

private theorem closure_openCells (xs : List V3) :
    closure (openCells xs) = closedCells xs := by
  induction xs with
  | nil => simp [openCells, closedCells]
  | cons a xs ih =>
      have ho : openCells (a :: xs) = interior (unitCube a) ∪ openCells xs := by
        ext x; simp [openCells]
      have hc : closedCells (a :: xs) = unitCube a ∪ closedCells xs := by
        ext x; simp [closedCells]
      rw [ho, hc, closure_union, unitCube_regularClosed, ih]

private theorem two_open_cells {m : RigidMotion}
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
private theorem sign_pm {f : Frame} (hf : f ∈ allFrames) (i : Fin 3) :
    f.sign.get i = 1 ∨ f.sign.get i = -1 := by
  unfold allFrames at hf
  obtain ⟨p, _, hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf
  simp [signTriples] at hs -- [compile-fix]
  rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    fin_cases i <;> simp [fr, V3.get, R44.v]

private theorem perm_surjective {f : Frame} (hf : f ∈ allFrames) (j : Fin 3) :
    ∃ i : Fin 3, f.perm.get i = j.val := by
  unfold allFrames at hf
  obtain ⟨p, hp, hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hf
  simp [coordinatePermutations] at hp -- [compile-fix]
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl) <;> fin_cases j
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩

private def lower8 (f : Frame) (z : Fin 3 → Int) (a : V3) (i : Fin 3) : Int :=
  z i + 8 * (if f.sign.get i = 1 then a.get (f.perm.get i)
    else -a.get (f.perm.get i) - 1)

private theorem eighth_apply {m : RigidMotion} {f : Frame} {z : Fin 3 → Int}
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
private theorem image_openCell {m : RigidMotion} {f : Frame} {z : Fin 3 → Int}
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

/-- The precise one-dimensional grid margin. The interval length need not be
one: all that matters is distinct integer eighth-grid endpoints. -/
private theorem midpoint_margin (l u : Int) (h : l < u) :
    (l : ℝ) / 8 + eta < ((l : ℝ) + (u : ℝ)) / 16 ∧
    ((l : ℝ) + (u : ℝ)) / 16 < (u : ℝ) / 8 - eta := by
  have hu : l + 1 ≤ u := by omega
  have hu' : (l : ℝ) + 1 ≤ (u : ℝ) := by exact_mod_cast hu
  norm_num [eta]
  constructor <;> linarith

private theorem overlapping_cells_have_core_overlap
    {m : RigidMotion} {f : Frame} {z : Fin 3 → Int}
    (hf : f ∈ allFrames)
    (hlin : ∀ x i, (m.linearIsometryEquiv x) i = frameActReal f x i)
    (hzero : ∀ i, m 0 i = (z i : ℝ) / 8)
    (a b : V3)
    (hov : (interior (unitCube a) ∩ (m '' interior (unitCube b))).Nonempty) :
    (openCell a eta ∩ (m '' openCell b eta)).Nonempty := by
  obtain ⟨y, hya, hym⟩ := hov
  rw [← openCell_zero a] at hya
  rw [← openCell_zero b, image_openCell hf hlin hzero] at hym
  let l : Fin 3 → Int := fun i => max (8 * a.get i) (lower8 f z b i)
  let u : Fin 3 → Int := fun i => min (8 * a.get i + 8) (lower8 f z b i + 8)
  have hwidth : ∀ i, l i < u i := by
    intro i
    have ha := hya i
    have hb := hym i
    simp only [add_zero, sub_zero] at ha hb
    have hab : 8 * a.get i < lower8 f z b i + 8 := by
      have hreal : 8 * (a.get i : ℝ) < (lower8 f z b i : ℝ) + 8 := by
        linarith
      exact_mod_cast hreal
    have hba : lower8 f z b i < 8 * a.get i + 8 := by
      have hreal : (lower8 f z b i : ℝ) < 8 * (a.get i : ℝ) + 8 := by
        linarith
      exact_mod_cast hreal
    change max (8 * a.get i) (lower8 f z b i) <
      min (8 * a.get i + 8) (lower8 f z b i + 8)
    exact lt_min (max_lt (by omega) hba) (max_lt hab (by omega))
  let w : E3 := WithLp.toLp 2 fun i => ((l i : ℝ) + (u i : ℝ)) / 16
  refine ⟨w, ?_, ?_⟩
  · intro i
    have hmid := midpoint_margin (l i) (u i) (hwidth i)
    have hlow : 8 * a.get i ≤ l i := le_max_left _ _
    have hhigh : u i ≤ 8 * a.get i + 8 := min_le_left _ _
    have hl : 8 * (a.get i : ℝ) ≤ (l i : ℝ) := by exact_mod_cast hlow
    have hu : (u i : ℝ) ≤ 8 * (a.get i : ℝ) + 8 := by exact_mod_cast hhigh
    change _ < ((l i : ℝ) + (u i : ℝ)) / 16 ∧
      ((l i : ℝ) + (u i : ℝ)) / 16 < _
    constructor <;> linarith
  · rw [image_openCell hf hlin hzero]
    intro i
    have hmid := midpoint_margin (l i) (u i) (hwidth i)
    have hlow : lower8 f z b i ≤ l i := le_max_right _ _
    have hhigh : u i ≤ lower8 f z b i + 8 := min_le_right _ _
    have hl : (lower8 f z b i : ℝ) ≤ (l i : ℝ) := by exact_mod_cast hlow
    have hu : (u i : ℝ) ≤ (lower8 f z b i : ℝ) + 8 := by exact_mod_cast hhigh
    change _ < ((l i : ℝ) + (u i : ℝ)) / 16 ∧
      ((l i : ℝ) + (u i : ℝ)) / 16 < _
    constructor <;> linarith

private theorem normalized_overlap {m : RigidMotion} (hm : EighthGridMotion m)
    (hov : (interior P ∩ interior (m '' P)).Nonempty) :
    (interior Q ∩ interior (m '' Q)).Nonempty := by
  obtain ⟨f, hf, hlin, hz⟩ := hm
  choose z hz using hz
  obtain ⟨a, ha, b, hb, hab⟩ := two_open_cells hov
  obtain ⟨w, hwa, hwb⟩ :=
    overlapping_cells_have_core_overlap hf hlin hz a b hab
  refine ⟨w, core_subset_interior_Q ha hwa, ?_⟩
  change w ∈ interior (m.toHomeomorph '' Q) -- [compile-fix]
  rw [← m.toHomeomorph.image_interior]
  exact Set.image_mono (core_subset_interior_Q hb) hwb

/-- A-L5.1, with exactly the frozen field proposition. There are no admitted
lemmas in this theorem's dependency chain. -/
theorem retained_core_overlap_holds :
    CompactRegularClosedBall Q → matesCensusCheck = true → RetainedCoreOverlap Q := by
  intro _hball _hcensus g h hgrid hov
  let m : RigidMotion := relativeMotion g h
  have himage (S : Set E3) : g '' (m '' S) = h '' S := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      simp [m, relativeMotion]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨m z, ⟨z, hz, rfl⟩, ?_⟩
      simp [m, relativeMotion]
  obtain ⟨x, hxg, hxh⟩ := hov
  change x ∈ interior (g.toHomeomorph '' P) at hxg -- [compile-fix]
  rw [← g.toHomeomorph.image_interior] at hxg
  obtain ⟨y, hyP, hgy⟩ := hxg
  have hym : y ∈ interior (m '' P) := by
    rw [← himage P] at hxh -- [compile-fix]
    change x ∈ interior (g.toHomeomorph '' (m '' P)) at hxh -- [compile-fix]
    rw [← g.toHomeomorph.image_interior] at hxh -- [compile-fix]
    obtain ⟨z, hzm, hgz⟩ := hxh
    have hzy : z = y := g.injective (hgz.trans hgy.symm)
    simpa [hzy] using hzm
  obtain ⟨w, hwQ, hwm⟩ := normalized_overlap hgrid ⟨y, hyP, hym⟩
  refine ⟨g w, ?_, ?_⟩
  · change g w ∈ interior (g.toHomeomorph '' Q) -- [compile-fix]
    rw [← g.toHomeomorph.image_interior] -- [compile-fix]
    exact ⟨w, hwQ, rfl⟩
  · rw [← himage Q] -- [compile-fix]
    change g w ∈ interior (g.toHomeomorph '' (m '' Q)) -- [compile-fix]
    rw [← g.toHomeomorph.image_interior] -- [compile-fix]
    exact ⟨w, hwm, rfl⟩

end
end R44
