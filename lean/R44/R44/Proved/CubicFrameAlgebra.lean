/- -- [compile-fix]
# Real/literal cubic-frame algebra

Used for A-C4.4. This file proves the representation bridge by coordinate
algebra and reads the six possible native normal directions. It does not
recompute a mate census, contact atlas, or a profile certificate.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.PyramidGeometry -- [compile-fix]
import R44.LogicalSpineFoundation -- [compile-fix]

namespace R44.DischargePyramid
open Set R44.Generated R44.DischargeGeometry R44.DischargeCharts
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- [compile-fix begin: promotion no longer inherits LogicalSpine's private lawful frame equality]
private local instance : LawfulBEq Frame where
  rfl := by
    intro g
    rcases g with ⟨⟨px, py, pz⟩, sx, sy, sz⟩
    unfold instBEqFrame instBEqFrame.beq instBEqN3 instBEqN3.beq
      instBEqV3 instBEqV3.beq
    simp
  eq_of_beq := frame_eq_of_beq
-- [compile-fix end]

/-- A real linear isometry has one of the 48 literal coordinate frames. -/
def CubicLinear (A : E3 ≃ₗᵢ[ℝ] E3) : Prop :=
  ∃f∈allFrames,∀x i,A x i=frameActReal f x i

-- [compile-fix begin: promotion cannot import the later LogicalSpine module; retain its structural frame calculation locally]
private def frameAction (f : Frame) (x : E3) : E3 :=
  WithLp.toLp 2 fun i : Fin 3 => frameActReal f x i

@[simp] private theorem frameAction_apply (f : Frame) (x : E3) (i : Fin 3) :
    frameAction f x i = frameActReal f x i := rfl

private theorem frame_mul_sign_get (f g : Frame) (i : Fin 3) :
    (f.mul g).sign.get i = f.sign.get i * g.sign.get (f.perm.get i) := by
  fin_cases i <;> rfl

private theorem frame_mul_perm_get (f g : Frame) (i : Fin 3) :
    (f.mul g).perm.get i = g.perm.get (f.perm.get i) := by
  fin_cases i <;> rfl

private theorem frameAction_mul (f g : Frame)
    (hf : ∀ i : Fin 3, f.perm.get i < 3)
    (hg : ∀ i : Fin 3, g.perm.get i < 3)
    (x : E3) (i : Fin 3) :
    frameActReal (f.mul g) x i = frameActReal f (frameAction g x) i := by
  let j : Fin 3 := ⟨f.perm.get i, hf i⟩
  have hj : g.perm.get j < 3 := hg j
  rw [frameActReal, frame_mul_sign_get, frame_mul_perm_get,
    frameCoordinate_of_lt x hj]
  rw [frameActReal, frameCoordinate_of_lt (frameAction g x) (hf i)]
  simp only [frameAction_apply]
  rw [frameActReal, frameCoordinate_of_lt x hj]
  change ((f.sign.get i * g.sign.get (f.perm.get i) : Int) : Real) *
      x ⟨g.perm.get j, hj⟩ =
    (f.sign.get i : Real) * ((g.sign.get (f.perm.get i) : Real) *
      x ⟨g.perm.get j, hj⟩)
  push_cast
  ring
-- [compile-fix end]

theorem frame_transpose_member (f : Frame) (hf : f∈allFrames) :
    f.transpose∈allFrames := by
  -- [compile-fix begin: use the same finite Boolean closure check instead of brittle list destructuring]
  have hcheck : allFrames.all (fun g => decide (g.transpose ∈ allFrames)) = true := by decide -- [compile-fix]
  exact of_decide_eq_true (List.all_eq_true.mp hcheck f hf) -- [compile-fix]
  -- [compile-fix end]

theorem frame_mul_member (f g : Frame) (hf : f∈allFrames) (hg : g∈allFrames) :
    f.mul g∈allFrames := by
  -- [compile-fix begin: use the finite Boolean multiplication-closure check]
  have hcheck : allFrames.all (fun a => -- [compile-fix]
      allFrames.all (fun b => decide (a.mul b ∈ allFrames))) = true := by decide -- [compile-fix]
  exact of_decide_eq_true -- [compile-fix]
    (List.all_eq_true.mp (List.all_eq_true.mp hcheck f hf) g hg) -- [compile-fix]
  -- [compile-fix end]

-- [compile-fix begin: local inverse calculation replacing the promotion-time LogicalSpine dependency]
private theorem frame_transpose_mul_identity (f : Frame) (hf : f ∈ allFrames) :
    f.transpose.mul f = identityFrame := by
  have hcheck : allFrames.all
      (fun g => decide (g.transpose.mul g = identityFrame)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hcheck f hf)

private theorem frameAction_identity (x : E3) (i : Fin 3) :
    frameActReal identityFrame x i = x i := by
  fin_cases i <;>
    simp [frameActReal, frameCoordinate, identityFrame, fr, n3, v, N3.get, V3.get]

private theorem frameAction_transpose (f : Frame) (hf : f ∈ allFrames) (x : E3) :
    frameAction f.transpose (frameAction f x) = x := by
  apply PiLp.ext
  intro i
  have hm := frameAction_mul f.transpose f
    (fun j => perm_lt_three (frame_transpose_member f hf) j)
    (fun j => perm_lt_three hf j) x i
  rw [frame_transpose_mul_identity f hf, frameAction_identity] at hm
  exact hm.symm
-- [compile-fix end]

theorem cubic_mul {A B : E3 ≃ₗᵢ[ℝ] E3} (ha : CubicLinear A) (hb : CubicLinear B) :
    CubicLinear (A*B) := by
  obtain ⟨f,hf,hfa⟩ := ha
  obtain ⟨g,hg,hgb⟩ := hb
  refine ⟨f.mul g,frame_mul_member f g hf hg,?_⟩
  intro x i
  change (A (B x)) i = frameActReal (f.mul g) x i -- [compile-fix]
  rw [hfa] -- [compile-fix]
  have hx : B x=frameAction g x := by ext j; exact hgb x j -- [compile-fix]
  rw [hx,← frameAction_mul f g (perm_lt_three hf) (perm_lt_three hg)] -- [compile-fix]

theorem cubic_inv {A : E3 ≃ₗᵢ[ℝ] E3} (ha : CubicLinear A) : CubicLinear A⁻¹ := by
  obtain ⟨f,hf,hfA⟩ := ha
  refine ⟨f.transpose,frame_transpose_member f hf,?_⟩
  intro x i
  have hAx : A (A.symm x)=frameAction f (A.symm x) := by -- [compile-fix]
    ext j; exact hfA _ j
  have hh := congrArg (frameAction f.transpose) hAx -- [compile-fix]
  rw [A.apply_symm_apply,frameAction_transpose f hf] at hh -- [compile-fix]
  exact congrArg (fun w : E3 => w i) hh.symm

private theorem chart_normal_cases (r : Role) :
    (nativeFeatureData r).normal=v 1 0 0 ∨
    (nativeFeatureData r).normal=v (-1) 0 0 ∨
    (nativeFeatureData r).normal=v 0 1 0 ∨
    (nativeFeatureData r).normal=v 0 (-1) 0 ∨
    (nativeFeatureData r).normal=v 0 0 1 ∨
    (nativeFeatureData r).normal=v 0 0 (-1) := by
  -- [compile-fix begin: read the accepted finite axis classifier instead of expanding all 192 roles]
  obtain ⟨i, hi⟩ := R44.DischargeGeometry.native_feature_chart_classification r
  dsimp at hi
  rcases hi with hi | hi | hi
  · rcases hi with ⟨hn, _⟩ -- [compile-fix]
    fin_cases i -- [compile-fix]
    · exact Or.inr (Or.inl (by simpa [unitAxis, V3.get, R44.v] using hn)) -- [compile-fix]
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa [unitAxis, V3.get, R44.v] using hn)))) -- [compile-fix]
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa [unitAxis, V3.get, R44.v] using hn))))) -- [compile-fix]
  · rcases hi with ⟨hn, _⟩ -- [compile-fix]
    fin_cases i -- [compile-fix]
    · exact Or.inl (by simpa [unitAxis, V3.get, R44.v] using hn) -- [compile-fix]
    · exact Or.inr (Or.inr (Or.inl (by simpa [unitAxis, V3.get, R44.v] using hn))) -- [compile-fix]
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [unitAxis, V3.get, R44.v] using hn))))) -- [compile-fix]
  · rcases hi with ⟨hn, _⟩ -- [compile-fix]
    fin_cases i -- [compile-fix]
    · exact Or.inl (by simpa [unitAxis, V3.get, R44.v] using hn) -- [compile-fix]
    · exact Or.inr (Or.inr (Or.inl (by simpa [unitAxis, V3.get, R44.v] using hn))) -- [compile-fix]
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa [unitAxis, V3.get, R44.v] using hn))))) -- [compile-fix]
  -- [compile-fix end]

theorem chart_cubic (r : Role) : CubicLinear (chartEquiv r) := by
  rcases chart_normal_cases r with h | h | h | h | h | h
  · refine ⟨fr 2 0 1 1 1 1,?_,?_⟩
    · norm_num [allFrames,coordinatePermutations,signTriples,fr,n3,v]
    · intro w i
      fin_cases i <;>
        simp [chartEquiv_apply,chartLinear_apply,featureTangent₁,featureTangent₂,
          featureTangentAxes,featureAxis,featureAxisOf,h,featureNormal,
          coordinateVector,scaledV3,frameActReal,frameCoordinate,fr,n3,v,N3.get,V3.get]
  · refine ⟨fr 2 0 1 (-1) 1 1,?_,?_⟩
    · norm_num [allFrames,coordinatePermutations,signTriples,fr,n3,v]
    · intro w i
      fin_cases i <;>
        simp [chartEquiv_apply,chartLinear_apply,featureTangent₁,featureTangent₂,
          featureTangentAxes,featureAxis,featureAxisOf,h,featureNormal,
          coordinateVector,scaledV3,frameActReal,frameCoordinate,fr,n3,v,N3.get,V3.get]
  · refine ⟨fr 0 2 1 1 1 1,?_,?_⟩
    · norm_num [allFrames,coordinatePermutations,signTriples,fr,n3,v]
    · intro w i
      fin_cases i <;>
        simp [chartEquiv_apply,chartLinear_apply,featureTangent₁,featureTangent₂,
          featureTangentAxes,featureAxis,featureAxisOf,h,featureNormal,
          coordinateVector,scaledV3,frameActReal,frameCoordinate,fr,n3,v,N3.get,V3.get]
  · refine ⟨fr 0 2 1 1 (-1) 1,?_,?_⟩
    · norm_num [allFrames,coordinatePermutations,signTriples,fr,n3,v]
    · intro w i
      fin_cases i <;>
        simp [chartEquiv_apply,chartLinear_apply,featureTangent₁,featureTangent₂,
          featureTangentAxes,featureAxis,featureAxisOf,h,featureNormal,
          coordinateVector,scaledV3,frameActReal,frameCoordinate,fr,n3,v,N3.get,V3.get]
  · refine ⟨fr 0 1 2 1 1 1,?_,?_⟩
    · norm_num [allFrames,coordinatePermutations,signTriples,fr,n3,v]
    · intro w i
      fin_cases i <;>
        simp [chartEquiv_apply,chartLinear_apply,featureTangent₁,featureTangent₂,
          featureTangentAxes,featureAxis,featureAxisOf,h,featureNormal,
          coordinateVector,scaledV3,frameActReal,frameCoordinate,fr,n3,v,N3.get,V3.get]
  · refine ⟨fr 0 1 2 1 1 (-1),?_,?_⟩
    · norm_num [allFrames,coordinatePermutations,signTriples,fr,n3,v]
    · intro w i
      fin_cases i <;>
        simp [chartEquiv_apply,chartLinear_apply,featureTangent₁,featureTangent₂,
          featureTangentAxes,featureAxis,featureAxisOf,h,featureNormal,
          coordinateVector,scaledV3,frameActReal,frameCoordinate,fr,n3,v,N3.get,V3.get]

/-- The literal frame obtained from the images of corners 0 and 1. -/
def squareFrame (i j : Fin 4) : Frame :=
  match i.val,j.val with
  | 0,1 => fr 0 1 2 1 1 (-1)
  | 0,3 => fr 1 0 2 1 1 (-1)
  | 1,0 => fr 0 1 2 1 (-1) (-1)
  | 1,2 => fr 1 0 2 1 (-1) (-1)
  | 2,1 => fr 1 0 2 (-1) (-1) (-1)
  | 2,3 => fr 0 1 2 (-1) (-1) (-1)
  | 3,0 => fr 1 0 2 (-1) 1 (-1)
  | 3,2 => fr 0 1 2 (-1) 1 (-1)
  | _,_ => identityFrame

/-- Whole graph equality forces the square frame; no geometric alignment
premise is used in this lemma. -/
theorem graph_eq_cubic {a : ℝ} (ha : SmallHeight a)
    (m : RigidMotion) (heq : m '' G a=G (-a)) : CubicLinear m.linearIsometryEquiv := by
  have hb : SmallHeight (-a) := ⟨neg_ne_zero.mpr ha.1,by simpa using ha.2⟩
  have hz := graph_eq_center ha hb m heq
  obtain ⟨p,hp⟩ := graph_eq_corners ha hb m heq
  have hadj := corner_adjacency ha hb m heq p hp 0
  have hadj' : p 1 = nextCorner (p 0) ∨ p 0 = nextCorner (p 1) := by -- [compile-fix]
    simpa [nextCorner] using hadj -- [compile-fix]
  have he2 := graph_eq_normal ha m heq
  have hlin (w : E3) : m w=m.linearIsometryEquiv w := by
    simpa [vadd_eq_add,hz] using m.map_vadd (0:E3) w
  have h0 := hp 0
  have h1 := hp 1
  rw [hlin] at h0 h1
  let e0 := pt 1 0 0
  let e1 := pt 0 1 0
  let e2 := pt 0 0 1
  have hb0 : B 0=(-eta) • e0+(-eta) • e1 := by
    ext k; fin_cases k <;> simp [B,e0,e1,pt]
  have hb1 : B 1=(-eta) • e0+eta • e1 := by
    ext k; fin_cases k <;> simp [B,e0,e1,pt]
  rw [hb0,map_add,map_smul,map_smul] at h0
  rw [hb1,map_add,map_smul,map_smul] at h1
  have hc0 : m.linearIsometryEquiv e0 =
      -(1/(2*eta)) • (B (p 0)+B (p 1)) := by
    ext k
    have h0k := congrArg (fun w:E3 => w k) h0
    have h1k := congrArg (fun w:E3 => w k) h1
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at h0k h1k ⊢
    norm_num [eta] at h0k h1k ⊢
    linarith
  have hc1 : m.linearIsometryEquiv e1 =
      (1/(2*eta)) • (B (p 1)-B (p 0)) := by
    ext k
    have h0k := congrArg (fun w:E3 => w k) h0
    have h1k := congrArg (fun w:E3 => w k) h1
    simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] at h0k h1k ⊢
    norm_num [eta] at h0k h1k ⊢
    linarith
  have hdecomp (w : E3) : w=w 0 • e0+w 1 • e1+w 2 • e2 := by
    ext k; fin_cases k <;> simp [e0,e1,e2,pt]
  refine ⟨squareFrame (p 0) (p 1),?_,?_⟩
  · generalize hpi : p 0 = i -- [compile-fix]
    generalize hpj : p 1 = j -- [compile-fix]
    simp only [hpi, hpj] at hadj' -- [compile-fix]
    fin_cases i <;> fin_cases j -- [compile-fix]
    all_goals norm_num [nextCorner] at hadj' -- [compile-fix]
    all_goals norm_num [squareFrame,allFrames,coordinatePermutations,signTriples,fr,n3,v] -- [compile-fix]
  · intro w k
    have he : m.linearIsometryEquiv w =
        w 0 • (-(1/(2*eta)) • (B (p 0)+B (p 1))) +
        w 1 • ((1/(2*eta)) • (B (p 1)-B (p 0))) +
        w 2 • -(pt 0 0 1) := by
      conv_lhs => rw [hdecomp w]
      rw [map_add,map_add,map_smul,map_smul,map_smul,hc0,hc1,he2]
    rw [he]
    generalize hpi : p 0 = i -- [compile-fix]
    generalize hpj : p 1 = j -- [compile-fix]
    rw [hpi, hpj] at he -- [compile-fix]
    simp only [hpi, hpj] at hadj' -- [compile-fix]
    fin_cases i <;> fin_cases j -- [compile-fix]
    all_goals norm_num [nextCorner] at hadj' -- [compile-fix]
    all_goals fin_cases k <;> -- [compile-fix]
      simp [squareFrame,B,pt,eta,frameActReal,frameCoordinate,fr,n3,v,N3.get,V3.get] <;> ring -- [compile-fix]

end
end R44.DischargePyramid
