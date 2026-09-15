import R44.LogicalSpineFoundation
-- [compile-fix: factor the unchanged pose lemmas needed by promoted helpers]

namespace R44.PoseAlgebra

open R44 Generated

noncomputable section

private theorem v3_eq (a b : V3) (hx : a.x = b.x) (hy : a.y = b.y)
    (hz : a.z = b.z) : a = b := by
  rcases a with ⟨ax, ay, az⟩
  rcases b with ⟨bx, byv, bz⟩
  simp_all

private local instance lawfulBEqFrame : LawfulBEq Frame where
  rfl := by
    intro g
    rcases g with ⟨⟨px, py, pz⟩, sx, sy, sz⟩
    unfold instBEqFrame instBEqFrame.beq instBEqN3 instBEqN3.beq
      instBEqV3 instBEqV3.beq
    simp
  eq_of_beq := frame_eq_of_beq

private theorem frame_mul_sign_get (f f' : Frame) (i : Fin 3) :
    (f.mul f').sign.get i = f.sign.get i * f'.sign.get (f.perm.get i) := by
  fin_cases i <;> rfl

private theorem frame_mul_perm_get (f f' : Frame) (i : Fin 3) :
    (f.mul f').perm.get i = f'.perm.get (f.perm.get i) := by
  fin_cases i <;> rfl

def frameActRealVector (f : Frame) (x : E3) : E3 :=
  WithLp.toLp 2 fun i : Fin 3 => frameActReal f x i

@[simp] private theorem frameActRealVector_apply (f : Frame) (x : E3)
    (i : Fin 3) : frameActRealVector f x i = frameActReal f x i := rfl

private theorem frameActReal_mul (f f' : Frame)
    (hf : ∀ i : Fin 3, f.perm.get i < 3)
    (hf' : ∀ i : Fin 3, f'.perm.get i < 3)
    (x : E3) (i : Fin 3) :
    frameActReal (f.mul f') x i =
      frameActReal f (frameActRealVector f' x) i := by
  let j : Fin 3 := ⟨f.perm.get i, hf i⟩
  have hj' : f'.perm.get j < 3 := hf' j
  rw [frameActReal, frame_mul_sign_get, frame_mul_perm_get,
    frameCoordinate_of_lt x hj']
  rw [frameActReal, frameCoordinate_of_lt (frameActRealVector f' x) (hf i)]
  simp only [frameActRealVector_apply]
  rw [frameActReal, frameCoordinate_of_lt x hj']
  change ((f.sign.get i * f'.sign.get (f.perm.get i) : Int) : Real) *
      x ⟨f'.perm.get j, hj'⟩ =
    (f.sign.get i : Real) * ((f'.sign.get (f.perm.get i) : Real) *
      x ⟨f'.perm.get j, hj'⟩)
  push_cast
  ring

private theorem allFrames_transpose_mem (f : Frame) (hf : f ∈ allFrames) :
    f.transpose ∈ allFrames := by
  have hcheck :
      allFrames.all (fun f => allFrames.contains f.transpose) = true := by decide
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hcheck f hf)

private theorem allFrames_transpose_mul (f : Frame) (hf : f ∈ allFrames) :
    f.transpose.mul f = identityFrame := by
  have hcheck :
      allFrames.all (fun f => f.transpose.mul f == identityFrame) = true := by decide
  exact frame_eq_of_beq (List.all_eq_true.mp hcheck f hf)

private theorem frameActReal_identity (x : E3) (i : Fin 3) :
    frameActReal identityFrame x i = x i := by
  fin_cases i <;> simp [frameActReal, frameCoordinate, identityFrame, fr, n3, v,
    N3.get, V3.get]

theorem frameActReal_transpose (f : Frame) (hf : f ∈ allFrames) (x : E3) :
    frameActRealVector f.transpose (frameActRealVector f x) = x := by
  apply PiLp.ext
  intro i
  have hm := frameActReal_mul f.transpose f
    (fun j => perm_lt_three (allFrames_transpose_mem f hf) j)
    (fun j => perm_lt_three hf j) x i
  rw [allFrames_transpose_mul f hf, frameActReal_identity] at hm
  exact hm.symm

private theorem allFrames_mul_transpose (f : Frame) (hf : f ∈ allFrames) :
    f.mul f.transpose = identityFrame := by
  have hcheck :
      allFrames.all (fun f => f.mul f.transpose == identityFrame) = true := by decide
  exact frame_eq_of_beq (List.all_eq_true.mp hcheck f hf)

private theorem frameActReal_transpose_right (f : Frame)
    (hf : f ∈ allFrames) (x : E3) :
    frameActRealVector f (frameActRealVector f.transpose x) = x := by
  apply PiLp.ext
  intro i
  have hm := frameActReal_mul f f.transpose
    (fun j => perm_lt_three hf j)
    (fun j => perm_lt_three (allFrames_transpose_mem f hf) j) x i
  rw [allFrames_mul_transpose f hf, frameActReal_identity] at hm
  exact hm.symm

private theorem frame_sign_pm {f : Frame} (hf : f ∈ allFrames) (i : Fin 3) :
    f.sign.get i = 1 ∨ f.sign.get i = -1 := by
  fin_cases i
  · exact (allFrames_data hf).sx
  · exact (allFrames_data hf).sy
  · exact (allFrames_data hf).sz

private theorem frame_row_eq_of_action_eq {f f' : Frame}
    (hf : f ∈ allFrames) (hf' : f' ∈ allFrames)
    (haction : ∀ x : E3, ∀ i : Fin 3,
      frameActReal f x i = frameActReal f' x i)
    (i : Fin 3) :
    f.perm.get i = f'.perm.get i ∧ f.sign.get i = f'.sign.get i := by
  let j : Nat := f.perm.get i
  have hj : j < 3 := perm_lt_three hf i
  have hj' : f'.perm.get i < 3 := perm_lt_three hf' i
  have heq := haction (coordinateVector j) i
  rw [frameActReal, frameCoordinate_of_lt (coordinateVector j) hj] at heq
  rw [frameActReal, frameCoordinate_of_lt (coordinateVector j) hj'] at heq
  have hsi : f.sign.get i = 1 ∨ f.sign.get i = -1 := frame_sign_pm hf i
  have hperm : f'.perm.get i = j := by
    by_contra hne
    have hcoord0 : coordinateVector j ⟨f'.perm.get i, hj'⟩ = 0 := by
      simp [coordinateVector, hne]
    have hcoord1 : coordinateVector j ⟨j, hj⟩ = 1 := by
      simp [coordinateVector]
    rw [hcoord0, hcoord1] at heq
    rcases hsi with hs | hs <;> rw [hs] at heq <;> norm_num at heq
  have hcoord : coordinateVector j ⟨f'.perm.get i, hj'⟩ = 1 := by
    simp [coordinateVector, hperm]
  have hcoord' : coordinateVector j ⟨j, hj⟩ = 1 := by
    simp [coordinateVector]
  rw [hcoord, hcoord'] at heq
  norm_num at heq
  exact ⟨hperm.symm, Int.cast_injective heq⟩

private theorem frame_eq_of_rows (f f' : Frame)
    (h : ∀ i : Fin 3,
      f.perm.get i = f'.perm.get i ∧ f.sign.get i = f'.sign.get i) :
    f = f' := by
  rcases f with ⟨⟨p0, p1, p2⟩, s0, s1, s2⟩
  rcases f' with ⟨⟨q0, q1, q2⟩, t0, t1, t2⟩
  have h0 := h (0 : Fin 3)
  have h1 := h (1 : Fin 3)
  have h2 := h (2 : Fin 3)
  simp [N3.get, V3.get] at h0 h1 h2
  simp_all

theorem realizesPose_pose_unique {m : RigidMotion} {p q : Pose}
    (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames)
    (hrealp : RealizesPose m p) (hrealq : RealizesPose m q) : p = q := by
  have haction : ∀ x : E3, ∀ i : Fin 3,
      frameActReal p.frame x i = frameActReal q.frame x i := by
    intro x i
    rw [← hrealp.1 x i, ← hrealq.1 x i]
  have h0 := frame_row_eq_of_action_eq hp hq haction (0 : Fin 3)
  have h1 := frame_row_eq_of_action_eq hp hq haction (1 : Fin 3)
  have h2 := frame_row_eq_of_action_eq hp hq haction (2 : Fin 3)
  have hframe : p.frame = q.frame := by
    apply frame_eq_of_rows
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hshift : p.shift = q.shift := by
    apply v3_eq
    · exact Int.cast_injective ((hrealp.2 0).symm.trans (hrealq.2 0))
    · exact Int.cast_injective ((hrealp.2 1).symm.trans (hrealq.2 1))
    · exact Int.cast_injective ((hrealp.2 2).symm.trans (hrealq.2 2))
  cases p
  cases q
  simp_all

private theorem frameActReal_scaledV3_one (f : Frame)
    (hf : ∀ i : Fin 3, f.perm.get i < 3) (a : V3) :
    frameActRealVector f (scaledV3 1 a) = scaledV3 1 (f.act a) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · have hp := hf (0 : Fin 3)
    change f.perm.x < 3 at hp
    simp only [frameActRealVector_apply]
    unfold frameActReal Frame.act scaledV3
    simp only [V3.get, N3.get]
    interval_cases f.perm.x <;> simp [frameCoordinate, v]
  · have hp := hf (1 : Fin 3)
    change f.perm.y < 3 at hp
    simp only [frameActRealVector_apply]
    unfold frameActReal Frame.act scaledV3
    simp only [V3.get, N3.get]
    interval_cases f.perm.y <;> simp [frameCoordinate, v]
  · have hp := hf (2 : Fin 3)
    change f.perm.z < 3 at hp
    simp only [frameActRealVector_apply]
    unfold frameActReal Frame.act scaledV3
    simp only [V3.get, N3.get]
    interval_cases f.perm.z <;> simp [frameCoordinate, v]

private theorem realizesPose_linear_vector {g : RigidMotion} {p : Pose}
    (hg : RealizesPose g p) (x : E3) :
    g.linearIsometryEquiv x = frameActRealVector p.frame x := by
  apply PiLp.ext
  intro i
  exact hg.1 x i

private theorem realizesPose_origin_vector {g : RigidMotion} {p : Pose}
    (hg : RealizesPose g p) : g 0 = scaledV3 1 p.shift := by
  apply PiLp.ext
  intro i
  simpa [scaledV3] using hg.2 i

private theorem v3_get_sub (a b : V3) (j : Nat) :
    (a.sub b).get j = a.get j - b.get j := by
  rcases j with (_ | j)
  · rfl
  rcases j with (_ | j)
  · rfl
  rfl

private theorem frame_act_sub (f : Frame) (a b : V3) :
    f.act (a.sub b) = (f.act a).sub (f.act b) := by
  apply v3_eq
  · change f.sign.x * (a.sub b).get f.perm.x =
      f.sign.x * a.get f.perm.x - f.sign.x * b.get f.perm.x
    rw [v3_get_sub]
    ring
  · change f.sign.y * (a.sub b).get f.perm.y =
      f.sign.y * a.get f.perm.y - f.sign.y * b.get f.perm.y
    rw [v3_get_sub]
    ring
  · change f.sign.z * (a.sub b).get f.perm.z =
      f.sign.z * a.get f.perm.z - f.sign.z * b.get f.perm.z
    rw [v3_get_sub]
    ring

private theorem pose_relative_shift (p q : Pose) :
    (p.relative q).shift = p.frame.transpose.act (q.shift.sub p.shift) := by
  unfold Pose.relative Pose.inverse Pose.transform
  change (p.frame.transpose.act p.shift).neg.add
      (p.frame.transpose.act q.shift) =
        p.frame.transpose.act (q.shift.sub p.shift)
  rw [frame_act_sub]
  apply v3_eq <;>
    simp [V3.add, V3.sub, V3.neg, V3.smul, v] <;> ring

/-- Foundational relative-pose transport used by promoted cell geometry. -/
theorem realizesPose_relative {g h : RigidMotion} {p q : Pose}
    (hg : RealizesPose g p) (hh : RealizesPose h q)
    (hpf : p.frame ∈ allFrames) (hqf : q.frame ∈ allFrames) :
    RealizesPose (relativeMotion g h) (p.relative q) := by
  constructor
  · intro x i
    have hlin :
        (relativeMotion g h).linearIsometryEquiv x =
          frameActRealVector (p.relative q).frame x := by
      apply g.linearIsometryEquiv.injective
      have hcomp :
          g.linearIsometryEquiv ((relativeMotion g h).linearIsometryEquiv x) =
            h.linearIsometryEquiv x := by
        change g.linearIsometryEquiv
            (g.linearIsometryEquiv.symm (h.linearIsometryEquiv x)) = _
        exact g.linearIsometryEquiv.apply_symm_apply _
      rw [hcomp, realizesPose_linear_vector hh]
      rw [realizesPose_linear_vector hg]
      unfold Pose.relative Pose.inverse Pose.transform
      change frameActRealVector q.frame x =
        frameActRealVector p.frame
          (frameActRealVector (p.frame.transpose.mul q.frame) x)
      have hmul := frameActReal_mul p.frame.transpose q.frame
        (fun j => perm_lt_three (allFrames_transpose_mem p.frame hpf) j)
        (fun j => perm_lt_three hqf j) x
      have hvecmul :
          frameActRealVector (p.frame.transpose.mul q.frame) x =
            frameActRealVector p.frame.transpose
              (frameActRealVector q.frame x) := by
        apply PiLp.ext
        intro j
        exact hmul j
      rw [hvecmul, frameActReal_transpose_right p.frame hpf]
    exact congrArg (fun y : E3 => y i) hlin
  · intro i
    have horigin :
        relativeMotion g h 0 = scaledV3 1 (p.relative q).shift := by
      apply g.injective
      have hcomp : g (relativeMotion g h 0) = h 0 := by
        change g (g⁻¹ (h 0)) = h 0
        exact g.apply_symm_apply _
      rw [hcomp, realizesPose_origin_vector hh]
      have hmap := g.map_vadd (0 : E3) (scaledV3 1 (p.relative q).shift)
      simp only [vadd_eq_add, add_zero] at hmap
      rw [hmap, realizesPose_linear_vector hg,
        realizesPose_origin_vector hg]
      rw [pose_relative_shift]
      change scaledV3 1 q.shift =
        frameActRealVector p.frame
          (scaledV3 1 (p.frame.transpose.act (q.shift.sub p.shift))) +
            scaledV3 1 p.shift
      rw [← frameActReal_scaledV3_one p.frame.transpose
        (fun j => perm_lt_three (allFrames_transpose_mem p.frame hpf) j)]
      rw [frameActReal_transpose_right p.frame hpf]
      symm
      apply PiLp.ext
      intro j
      fin_cases j <;> norm_num [scaledV3, V3.sub, V3.get, v]
    simpa [scaledV3] using congrArg (fun y : E3 => y i) horigin

/-- Foundational copy of pose composition used by promoted registration proofs. -/
theorem realizesPose_transform {g h : RigidMotion} {p q : Pose}
    (hg : RealizesPose g p) (hh : RealizesPose h q)
    (hpf : p.frame ∈ allFrames) (hqf : q.frame ∈ allFrames) :
    RealizesPose (g * h) (p.transform q) := by
  constructor
  · intro x i
    change (g.linearIsometryEquiv (h.linearIsometryEquiv x)) i = _
    rw [hg.1, realizesPose_linear_vector hh]
    unfold Pose.transform
    exact (frameActReal_mul p.frame q.frame
      (fun j => perm_lt_three hpf j)
      (fun j => perm_lt_three hqf j) x i).symm
  · intro i
    have hmap := congrArg (fun y : E3 => y i) (g.map_vadd 0 (h 0))
    simp only [vadd_eq_add, add_zero] at hmap
    change (g (h 0)) i = _
    rw [hmap]
    change (g.linearIsometryEquiv (h 0)) i + (g 0) i = _
    rw [realizesPose_origin_vector hh, hg.1]
    have hscaled := congrArg (fun y : E3 => y i)
      (frameActReal_scaledV3_one p.frame
        (fun j => perm_lt_three hpf j) q.shift)
    simp only [frameActRealVector_apply] at hscaled
    rw [hscaled, hg.2]
    unfold Pose.transform
    simp only [scaledV3, div_one, po]
    change ((p.frame.act q.shift).get i : ℝ) + (p.shift.get i : ℝ) =
      ((p.shift.add (p.frame.act q.shift)).get i : ℝ)
    rcases i with ⟨i, hi⟩
    interval_cases i <;> simp [scaledV3, V3.add, V3.get, v] <;> ring

end
end R44.PoseAlgebra
