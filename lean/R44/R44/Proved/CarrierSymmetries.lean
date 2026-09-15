/-
# The six symmetries of the recovered bare carrier

Written source: proof/PROOFS_registered.md §6, Native asymmetry; ERRATA E5.
This supplies the sentence that the recovered seven-cube carrier has only
coordinate-permutation symmetries. It does not assume carrier recovery from
Q. The elementary metric proof below expands that sentence: diameter pairs
recover the center; their six endpoints recover the three unsigned axes;
the missing corner rules out simultaneous reversal.

There are no admitted lemmas in this file and no call to a finite certificate
checker. The six alternatives are elementary carrier geometry, not the
already certified 192-row feature-symmetry calculation.

This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.NativeGeometry -- [compile-fix]

namespace R44.DischargeGeometry
open Set
open R44.Generated
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def ctr : E3 := WithLp.toLp 2 fun _ => 1
private def a0 : E3 := cellCorner (v 2 0 0)
private def a1 : E3 := cellCorner (v 0 2 0)
private def a2 : E3 := cellCorner (v 0 0 2)
private def b0 : E3 := cellCorner (v 0 2 2)
private def b1 : E3 := cellCorner (v 2 0 2)
private def b2 : E3 := cellCorner (v 2 2 0)

private theorem dist_sq_coords (x y : E3) :
    dist x y ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 + (x 2 - y 2)^2 := by
  simp [dist_eq_norm, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ,
    Real.norm_eq_abs, sq_abs, add_assoc]

/-- Coordinate form with a quantified notch, convenient under permutation. -/
theorem mem_P_iff_box_notch (x : E3) :
    x ∈ P ↔ (∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 2) ∧
      ∃ i : Fin 3, x i ≤ 1 := by
  rw [mem_P_iff_coordinates]
  constructor
  · rintro ⟨h0, h0', h1, h1', h2, h2', hn⟩
    constructor
    · intro i
      fin_cases i
      · exact ⟨h0, h0'⟩
      · exact ⟨h1, h1'⟩
      · exact ⟨h2, h2'⟩
    · rcases hn with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
  · rintro ⟨hb, i, hi⟩
    refine ⟨(hb 0).1, (hb 0).2, (hb 1).1, (hb 1).2,
      (hb 2).1, (hb 2).2, ?_⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)

private theorem coord_extreme {a b : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 2) (hb : 0 ≤ b ∧ b ≤ 2)
    (h : (a-b)^2 = 4) :
    (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by
  have hf : (a-b-2)*(a-b+2) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h' | h'
  · right; constructor <;> linarith
  · left; constructor <;> linarith

private theorem coord_sq_le {a b : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 2) (hb : 0 ≤ b ∧ b ≤ 2) : (a-b)^2 ≤ 4 := by
  have hminus : 0 ≤ 2-(a-b) := by linarith
  have hplus : 0 ≤ 2+(a-b) := by linarith
  nlinarith [mul_nonneg hminus hplus]

private theorem diameter_coordinate_extremes {x y : E3}
    (hx : x ∈ P) (hy : y ∈ P) (hd : dist x y ^ 2 = 12) :
    ∀ i : Fin 3, (x i = 0 ∧ y i = 2) ∨ (x i = 2 ∧ y i = 0) := by
  have hxb := (mem_P_iff_box_notch x).mp hx |>.1
  have hyb := (mem_P_iff_box_notch y).mp hy |>.1
  have h0 := coord_sq_le (hxb 0) (hyb 0)
  have h1 := coord_sq_le (hxb 1) (hyb 1)
  have h2 := coord_sq_le (hxb 2) (hyb 2)
  rw [dist_sq_coords] at hd
  have hs0 : (x 0 - y 0) ^ 2 = 4 := by linarith -- [compile-fix]
  have hs1 : (x 1 - y 1) ^ 2 = 4 := by linarith -- [compile-fix]
  have hs2 : (x 2 - y 2) ^ 2 = 4 := by linarith -- [compile-fix]
  intro i
  fin_cases i -- [compile-fix]
  · simpa using coord_extreme (hxb 0) (hyb 0) hs0 -- [compile-fix]
  · simpa using coord_extreme (hxb 1) (hyb 1) hs1 -- [compile-fix]
  · simpa using coord_extreme (hxb 2) (hyb 2) hs2 -- [compile-fix]

private theorem diameter_pair_sum {x y : E3}
    (hx : x ∈ P) (hy : y ∈ P) (hd : dist x y ^ 2 = 12) :
    x + y = (2 : ℝ) • ctr := by
  have h := diameter_coordinate_extremes hx hy hd
  apply PiLp.ext
  intro i
  rcases h i with h | h <;> simp [ctr, h.1, h.2]

private theorem diameter_endpoint {x y : E3}
    (hx : x ∈ P) (hy : y ∈ P) (hd : dist x y ^ 2 = 12) :
    x = a0 ∨ x = a1 ∨ x = a2 ∨ x = b0 ∨ x = b1 ∨ x = b2 := by
  have h := diameter_coordinate_extremes hx hy hd
  have hxnot := (mem_P_iff_box_notch x).mp hx |>.2
  have hynot := (mem_P_iff_box_notch y).mp hy |>.2
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  all_goals
    solve
    | (exfalso
       obtain ⟨i, hi⟩ := hxnot
       fin_cases i <;> simp_all)
    | (exfalso
       obtain ⟨i, hi⟩ := hynot
       fin_cases i <;> simp_all)
    | (apply Or.inl; apply PiLp.ext; intro i; fin_cases i <;>
        simp [a0, cellCorner, V3.get, v, h0.1, h1.1, h2.1])
    | (apply Or.inr; apply Or.inl; apply PiLp.ext; intro i; fin_cases i <;>
        simp [a1, cellCorner, V3.get, v, h0.1, h1.1, h2.1])
    | (apply Or.inr; apply Or.inr; apply Or.inl; apply PiLp.ext; intro i; fin_cases i <;>
        simp [a2, cellCorner, V3.get, v, h0.1, h1.1, h2.1])
    | (apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl;
        apply PiLp.ext; intro i; fin_cases i <;>
        simp [b0, cellCorner, V3.get, v, h0.1, h1.1, h2.1])
    | (apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl;
        apply PiLp.ext; intro i; fin_cases i <;>
        simp [b1, cellCorner, V3.get, v, h0.1, h1.1, h2.1])
    | (apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr;
        apply PiLp.ext; intro i; fin_cases i <;>
        simp [b2, cellCorner, V3.get, v, h0.1, h1.1, h2.1])

private theorem rigid_apply (g : RigidMotion) (x : E3) :
    g x = g.linearIsometryEquiv x + g 0 := by
  simpa only [vadd_eq_add, add_zero] using g.map_vadd (0 : E3) x

private theorem three_anchor_sum (g : RigidMotion) :
    g a0 + g a1 + g a2 = (2 : ℝ) • g ctr + g 0 := by
  have ha : a0 + a1 + a2 = (2 : ℝ) • ctr := by
    apply PiLp.ext; intro i; fin_cases i <;>
      norm_num [a0, a1, a2, ctr, cellCorner, V3.get, v]
  calc
    _ = g.linearIsometryEquiv (a0 + a1 + a2) + (3 : ℝ) • g 0 := by
      rw [rigid_apply g a0, rigid_apply g a1, rigid_apply g a2, -- [compile-fix]
        map_add, map_add] -- [compile-fix]
      module -- [compile-fix]
    _ = (2 : ℝ) • g ctr + g 0 := by
      rw [ha, map_smul, rigid_apply g ctr, smul_add]
      module -- [compile-fix]

private theorem center_fixed {g : RigidMotion} (hg : g '' P = P) : g ctr = ctr := by
  have ha : a0 ∈ P := by norm_num [mem_P_iff_coordinates, a0, cellCorner, V3.get, v]
  have hb : b0 ∈ P := by norm_num [mem_P_iff_coordinates, b0, cellCorner, V3.get, v]
  have hdist : dist a0 b0 ^ 2 = 12 := by
    norm_num [dist_sq_coords, a0, b0, cellCorner, V3.get, v]
  have hga : g a0 ∈ P := by rw [← hg]; exact ⟨a0, ha, rfl⟩
  have hgb : g b0 ∈ P := by rw [← hg]; exact ⟨b0, hb, rfl⟩
  have hgsum := diameter_pair_sum hga hgb (by simpa only [g.isometry.dist_eq] using hdist)
  have hsum : a0 + b0 = (2 : ℝ) • ctr := diameter_pair_sum ha hb hdist
  rw [rigid_apply g a0, rigid_apply g b0] at hgsum
  have hlin : g.linearIsometryEquiv a0 + g.linearIsometryEquiv b0 =
      (2 : ℝ) • g.linearIsometryEquiv ctr := by
    rw [← map_add, hsum, map_smul]
  apply PiLp.ext
  intro i
  have hs := congrArg (fun z : E3 => z i) hgsum
  have hl := congrArg (fun z : E3 => z i) hlin
  rw [rigid_apply g ctr]
  change (g.linearIsometryEquiv ctr) i + (g 0) i = ctr i -- [compile-fix]
  change (g.linearIsometryEquiv a0) i + (g 0) i +
    ((g.linearIsometryEquiv b0) i + (g 0) i) = 2 * ctr i at hs
  change (g.linearIsometryEquiv a0) i + (g.linearIsometryEquiv b0) i =
    2 * (g.linearIsometryEquiv ctr) i at hl
  linarith

/-- After its carrier is recovered, a self-isometry has one of the six
ordinary coordinate permutations, fixes zero, and has no hidden translation.
-/
theorem carrier_self_isometry_frame {g : RigidMotion} (hg : g '' P = P) :
    ∃ p ∈ coordinatePermutations,
      RealizesPose g (po (fr p.x p.y p.z 1 1 1) (v 0 0 0)) := by
  have hsend : ∀ x ∈ P, g x ∈ P := by
    intro x hx; rw [← hg]; exact ⟨x, hx, rfl⟩
  have hc := center_fixed hg
  have hpair (a b : E3) (ha : a ∈ P) (hb : b ∈ P)
      (hd : dist a b ^ 2 = 12) :
      g a = a0 ∨ g a = a1 ∨ g a = a2 ∨ g a = b0 ∨ g a = b1 ∨ g a = b2 :=
    diameter_endpoint (hsend a ha) (hsend b hb) (by simpa only [g.isometry.dist_eq] using hd)
  have hm0 := hpair a0 b0
    (by norm_num [mem_P_iff_coordinates, a0, cellCorner, V3.get, v])
    (by norm_num [mem_P_iff_coordinates, b0, cellCorner, V3.get, v])
    (by norm_num [dist_sq_coords, a0, b0, cellCorner, V3.get, v])
  have hm1 := hpair a1 b1
    (by norm_num [mem_P_iff_coordinates, a1, cellCorner, V3.get, v])
    (by norm_num [mem_P_iff_coordinates, b1, cellCorner, V3.get, v])
    (by norm_num [dist_sq_coords, a1, b1, cellCorner, V3.get, v])
  have hm2 := hpair a2 b2
    (by norm_num [mem_P_iff_coordinates, a2, cellCorner, V3.get, v])
    (by norm_num [mem_P_iff_coordinates, b2, cellCorner, V3.get, v])
    (by norm_num [dist_sq_coords, a2, b2, cellCorner, V3.get, v])
  have hd01 : dist (g a0) (g a1)^2 = 8 := by
    rw [g.isometry.dist_eq]; norm_num [dist_sq_coords, a0, a1, cellCorner, V3.get, v]
  have hd02 : dist (g a0) (g a2)^2 = 8 := by
    rw [g.isometry.dist_eq]; norm_num [dist_sq_coords, a0, a2, cellCorner, V3.get, v]
  have hd12 : dist (g a1) (g a2)^2 = 8 := by
    rw [g.isometry.dist_eq]; norm_num [dist_sq_coords, a1, a2, cellCorner, V3.get, v]
  have hs := three_anchor_sum g
  rw [hc] at hs
  have hg0P : g 0 ∈ P := hsend 0 (by norm_num [mem_P_iff_coordinates])
  have hsumcoords := fun i : Fin 3 => congrArg (fun z : E3 => z i) hs
  -- Choose the images of the three positive anchors. The distance equations
  -- remove mixed signs and duplicate axes. The notch removes the simultaneous
  -- reversal. No search/decide theorem about feature data is recomputed here.
  -- [compile-fix begin: replace the elaboration-heavy anchor product with indexed six-anchor cases]
  let anchors : Fin 6 → E3 := ![a0, a1, a2, b0, b1, b2] -- [compile-fix]
  obtain ⟨i0, hi0⟩ : ∃ i : Fin 6, g a0 = anchors i := by -- [compile-fix]
    rcases hm0 with h | h | h | h | h | h -- [compile-fix]
    · exact ⟨0, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨1, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨2, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨3, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨4, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨5, by simpa [anchors] using h⟩ -- [compile-fix]
  obtain ⟨i1, hi1⟩ : ∃ i : Fin 6, g a1 = anchors i := by -- [compile-fix]
    rcases hm1 with h | h | h | h | h | h -- [compile-fix]
    · exact ⟨0, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨1, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨2, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨3, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨4, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨5, by simpa [anchors] using h⟩ -- [compile-fix]
  obtain ⟨i2, hi2⟩ : ∃ i : Fin 6, g a2 = anchors i := by -- [compile-fix]
    rcases hm2 with h | h | h | h | h | h -- [compile-fix]
    · exact ⟨0, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨1, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨2, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨3, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨4, by simpa [anchors] using h⟩ -- [compile-fix]
    · exact ⟨5, by simpa [anchors] using h⟩ -- [compile-fix]
  rw [hi0, hi1] at hd01 -- [compile-fix]
  rw [hi0, hi2] at hd02 -- [compile-fix]
  rw [hi1, hi2] at hd12 -- [compile-fix]
  have pair_side (i j : Fin 6) (hd : dist (anchors i) (anchors j) ^ 2 = 8) : -- [compile-fix]
      (((i : Nat) < 3 ∧ (j : Nat) < 3) ∨ -- [compile-fix]
       (3 ≤ (i : Nat) ∧ 3 ≤ (j : Nat))) ∧ i ≠ j := by -- [compile-fix]
    fin_cases i <;> fin_cases j -- [compile-fix]
    all_goals norm_num [anchors, dist_sq_coords, a0, a1, a2, b0, b1, b2, -- [compile-fix]
      cellCorner, V3.get, v] at hd -- [compile-fix]
    all_goals norm_num -- [compile-fix]
  have hp01 := pair_side i0 i1 hd01 -- [compile-fix]
  have hp02 := pair_side i0 i2 hd02 -- [compile-fix]
  have hp12 := pair_side i1 i2 hd12 -- [compile-fix]
  have hne01 := hp01.2 -- [compile-fix]
  have hne02 := hp02.2 -- [compile-fix]
  have hne12 := hp12.2 -- [compile-fix]
  have hside : -- [compile-fix]
      ((i0 : Nat) < 3 ∧ (i1 : Nat) < 3 ∧ (i2 : Nat) < 3) ∨ -- [compile-fix]
      (3 ≤ (i0 : Nat) ∧ 3 ≤ (i1 : Nat) ∧ 3 ≤ (i2 : Nat)) := by -- [compile-fix]
    rcases hp01.1 with h01 | h01 <;> rcases hp02.1 with h02 | h02 -- [compile-fix]
    · exact Or.inl ⟨h01.1, h01.2, h02.2⟩ -- [compile-fix]
    · omega -- [compile-fix]
    · omega -- [compile-fix]
    · exact Or.inr ⟨h01.1, h01.2, h02.2⟩ -- [compile-fix]
  have hlinear (x : E3) : -- [compile-fix]
      g.linearIsometryEquiv x = -- [compile-fix]
        (x 0 / 2) • g.linearIsometryEquiv a0 + -- [compile-fix]
        (x 1 / 2) • g.linearIsometryEquiv a1 + -- [compile-fix]
        (x 2 / 2) • g.linearIsometryEquiv a2 := by -- [compile-fix]
    rw [← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add] -- [compile-fix]
    congr 1 -- [compile-fix]
    apply PiLp.ext -- [compile-fix]
    intro i -- [compile-fix]
    fin_cases i <;> -- [compile-fix]
      simp [a0, a1, a2, cellCorner, V3.get, v] <;> ring -- [compile-fix]
  rcases hside with hsmall | hlarge -- [compile-fix]
  · fin_cases i0 -- [compile-fix]
    all_goals norm_num at hsmall -- [compile-fix]
    all_goals fin_cases i1 -- [compile-fix]
    all_goals norm_num at hsmall -- [compile-fix]
    all_goals try norm_num at hne01 -- [compile-fix]
    all_goals fin_cases i2 -- [compile-fix]
    all_goals norm_num at hsmall -- [compile-fix]
    all_goals try norm_num at hne02 -- [compile-fix]
    all_goals try norm_num at hne12 -- [compile-fix]
    all_goals simp [anchors] at hi0 hi1 hi2 -- [compile-fix]
    all_goals
      have hz0 := hsumcoords 0
      have hz1 := hsumcoords 1
      have hz2 := hsumcoords 2
      rw [hi0, hi1, hi2] at hz0 hz1 hz2 -- [compile-fix]
      norm_num [a0, a1, a2, ctr, cellCorner, V3.get, v]
        at hz0 hz1 hz2 -- [compile-fix]
    all_goals
      have hzero : g 0 = 0 := by
        apply PiLp.ext
        intro i
        change g 0 i = 0
        fin_cases i -- [compile-fix]
        · simpa using hz0 -- [compile-fix]
        · simpa using hz1 -- [compile-fix]
        · simpa using hz2 -- [compile-fix]
      have hA0 := rigid_apply g a0
      have hA1 := rigid_apply g a1
      have hA2 := rigid_apply g a2
      rw [hzero, add_zero, hi0] at hA0 -- [compile-fix]
      rw [hzero, add_zero, hi1] at hA1 -- [compile-fix]
      rw [hzero, add_zero, hi2] at hA2 -- [compile-fix]
    all_goals first -- [compile-fix]
      | (refine ⟨n3 0 1 2, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
      | (refine ⟨n3 0 2 1, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
      | (refine ⟨n3 1 0 2, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
      | (refine ⟨n3 1 2 0, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
      | (refine ⟨n3 2 0 1, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
      | (refine ⟨n3 2 1 0, by simp [coordinatePermutations], ?_⟩
         constructor
         · intro x i
           rw [hlinear x, ← hA0, ← hA1, ← hA2]
           fin_cases i <;>
             simp [frameActReal, frameCoordinate, a0, a1, a2, b0, b1, b2,
               po, fr, n3, cellCorner, V3.get, N3.get, v] <;> ring
         · intro i; fin_cases i <;> simp [hzero, po, v, V3.get]) -- [compile-fix]
  · fin_cases i0 -- [compile-fix]
    all_goals norm_num at hlarge -- [compile-fix]
    all_goals fin_cases i1 -- [compile-fix]
    all_goals norm_num at hlarge -- [compile-fix]
    all_goals try norm_num at hne01 -- [compile-fix]
    all_goals fin_cases i2 -- [compile-fix]
    all_goals norm_num at hlarge -- [compile-fix]
    all_goals try norm_num at hne02 -- [compile-fix]
    all_goals try norm_num at hne12 -- [compile-fix]
    all_goals simp [anchors] at hi0 hi1 hi2 -- [compile-fix]
    all_goals
      have hz0 := hsumcoords 0
      have hz1 := hsumcoords 1
      have hz2 := hsumcoords 2
      rw [hi0, hi1, hi2] at hz0 hz1 hz2 -- [compile-fix]
      norm_num [b0, b1, b2, ctr, cellCorner, V3.get, v]
        at hz0 hz1 hz2 -- [compile-fix]
      rw [mem_P_iff_coordinates] at hg0P
      exfalso
      rcases hg0P.2.2.2.2.2.2 with h | h | h <;> linarith
  -- [compile-fix end]

end
end R44.DischargeGeometry
