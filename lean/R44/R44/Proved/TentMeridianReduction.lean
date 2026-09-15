/- -- [compile-fix: promoted to Proved after exchange 7]
# Explicit orthogonal meridians of the canonical tent cones

A-L3.1. This is the SET-level step between TentTangentCharts and the polar
area calculation. In particular the ridge axis is slanted; simply dropping
one of the original horizontal coordinates would compute the wrong angle.
The normalizations below treat both positive and negative heights uniformly.
No claim about the remaining full native mesh-edge assignment is made here.
No mathematical admissions.
-/
import R44.Proved.TentTangentCharts -- [compile-fix: promoted after exchange 7]
import R44.Proved.PlanarSectorArea -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeMeridianFrames
open Set DischargeTentCones DischargeWedge DischargePyramid
noncomputable section
set_option maxHeartbeats 0

private theorem lin_surjective (L : E3 →ₗᵢ[ℝ] E3) : Function.Surjective L := by
  exact (LinearMap.injective_iff_surjective).mp L.injective
  -- API?: for a linear endomorphism of a finite-dimensional vector space,
  -- injectivity and surjectivity are equivalent. Pass L.toLinearMap if needed.

private def swapYZLinear : E3 →ₗ[ℝ] E3 where
  toFun := fun w => pt (w 0) (w 2) (w 1)
  map_add' := by intros; ext i; fin_cases i <;> simp [pt]
  map_smul' := by intros; ext i; fin_cases i <;> simp [pt]

private def swapYZIso : E3 →ₗᵢ[ℝ] E3 where
  toLinearMap := swapYZLinear
  norm_map' := by
    intro w
    have he : ‖swapYZLinear w‖^2=‖w‖^2 := by
      simp [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,swapYZLinear,pt,
        Real.norm_eq_abs,sq_abs]; ring
    nlinarith [norm_nonneg (swapYZLinear w),norm_nonneg w]

def baseAxes : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.ofSurjective swapYZIso (lin_surjective swapYZIso)

def baseSection (a : ℝ) : Set E2 :=
  {u | u 1≤(a/eta)*max 0 (u 0)}

 theorem base_meridian (a : ℝ) :
    baseCone a=baseAxes '' prism (baseSection a) := by
  ext d
  constructor
  · intro hd
    exact ⟨pt (d 0) (d 2) (d 1),by simpa [baseCone,prism,baseSection,axisSplit_snd,pt] using hd, -- [compile-fix: unfold the source cone]
      by ext i; fin_cases i <;> rfl⟩
  · rintro ⟨w,hw,rfl⟩
    simpa [baseCone,baseAxes,swapYZIso,swapYZLinear,prism,baseSection,axisSplit_snd,pt] using hw

private def ridgeLinear (a sx sy : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun := fun w =>
    let t := a/eta
    let e := Real.sqrt 2
    let d := Real.sqrt (2+t^2)
    pt (sx*(w 0/e+t*w 1/(e*d)+w 2/d))
       (sy*(-w 0/e+t*w 1/(e*d)+w 2/d))
       (e*w 1/d-t*w 2/d)
  map_add' := by intros; ext i; fin_cases i <;> simp [pt] <;> ring
  map_smul' := by intros; ext i; fin_cases i <;> simp [pt] <;> ring

private theorem ridge_norm (a sx sy : ℝ) (hx : sx=1 ∨ sx= -1)
    (hy : sy=1 ∨ sy= -1) (w : E3) : ‖ridgeLinear a sx sy w‖=‖w‖ := by
  let t := a/eta
  let e := Real.sqrt 2
  let d := Real.sqrt (2+t^2)
  have he0 : 0<e := Real.sqrt_pos.mpr (by norm_num)
  have hd0 : 0<d := Real.sqrt_pos.mpr (by positivity)
  have he2 : e^2=2 := Real.sq_sqrt (by norm_num)
  have hd2 : d^2=2+t^2 := Real.sq_sqrt (by positivity)
  have hx2 : sx^2=1 := by rcases hx with rfl|rfl <;> norm_num
  have hy2 : sy^2=1 := by rcases hy with rfl|rfl <;> norm_num
  have hsum :
      (sx*(w 0/e+t*w 1/(e*d)+w 2/d))^2+
      (sy*(-w 0/e+t*w 1/(e*d)+w 2/d))^2+
      (e*w 1/d-t*w 2/d)^2=(w 0)^2+(w 1)^2+(w 2)^2 := by
    simp only [mul_pow,hx2,hy2,one_mul]
    have hpair :
        (w 0/e+t*w 1/(e*d)+w 2/d)^2+
        (-w 0/e+t*w 1/(e*d)+w 2/d)^2=
        2*(w 0)^2/e^2+2*(t*w 1+e*w 2)^2/(e^2*d^2) := by
      field_simp [ne_of_gt he0,ne_of_gt hd0]
      ring
    rw [hpair,he2]
    calc
      _ = (w 0)^2+((t*w 1+e*w 2)^2+(e*w 1-t*w 2)^2)/d^2 := by
        field_simp [ne_of_gt hd0]; ring
      _ = (w 0)^2+((t^2+e^2)*((w 1)^2+(w 2)^2))/d^2 := by
        congr 2; ring
      _ = (w 0)^2+(w 1)^2+(w 2)^2 := by
        rw [show t^2+e^2=d^2 by linarith [he2,hd2]]
        field_simp [ne_of_gt hd0]; ring
  have hn : ‖ridgeLinear a sx sy w‖^2=‖w‖^2 := by
    calc -- [compile-fix begin: compare the two norm expansions through the delivered coordinate identity]
      ‖ridgeLinear a sx sy w‖^2 =
          (sx*(w 0/e+t*w 1/(e*d)+w 2/d))^2+
          (sy*(-w 0/e+t*w 1/(e*d)+w 2/d))^2+
          (e*w 1/d-t*w 2/d)^2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp [Fin.sum_univ_succ, ridgeLinear, pt, PiLp.toLp_apply,
          Real.norm_eq_abs, sq_abs, hx2, hy2]
        ring
      _ = (w 0)^2+(w 1)^2+(w 2)^2 := hsum
      _ = ‖w‖^2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
        ring -- [compile-fix end]
  nlinarith [norm_nonneg (ridgeLinear a sx sy w),norm_nonneg w]

private def ridgeIso (a sx sy : ℝ) (hx : sx=1 ∨ sx= -1)
    (hy : sy=1 ∨ sy= -1) : E3 →ₗᵢ[ℝ] E3 where
  toLinearMap := ridgeLinear a sx sy
  norm_map' := ridge_norm a sx sy hx hy

def ridgeAxes (a sx sy : ℝ) (hx : sx=1 ∨ sx= -1)
    (hy : sy=1 ∨ sy= -1) : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.ofSurjective (ridgeIso a sx sy hx hy)
    (lin_surjective (ridgeIso a sx sy hx hy))

def ridgeSection (a : ℝ) : Set E2 :=
  {u | u 1≤-((a/eta)/Real.sqrt (2+(a/eta)^2))*|u 0|}

/-- Orthogonal reduction, not an oblique coordinate projection. -/
theorem ridge_meridian (a sx sy : ℝ) (hx : sx=1 ∨ sx= -1)
    (hy : sy=1 ∨ sy= -1) :
    ridgeCone a sx sy=(ridgeAxes a sx sy hx hy) '' prism (ridgeSection a) := by
  let t := a/eta
  let e := Real.sqrt 2
  let d := Real.sqrt (2+t^2)
  have he0 : 0<e := Real.sqrt_pos.mpr (by norm_num)
  have hd0 : 0<d := Real.sqrt_pos.mpr (by positivity)
  have he2 : e^2=2 := Real.sq_sqrt (by norm_num)
  have hd2 : d^2=2+t^2 := Real.sq_sqrt (by positivity)
  have hpoint (w : E3) :
      ridgeAxes a sx sy hx hy w∈ridgeCone a sx sy ↔ w∈prism (ridgeSection a) := by
    have hmax :
      max (w 0/e+t*w 1/(e*d)+w 2/d)
        (-w 0/e+t*w 1/(e*d)+w 2/d)=
        |w 0|/e+t*w 1/(e*d)+w 2/d := by
      rw [max_add_add_right,max_add_add_right,max_div_div_right he0.le,
        ←abs_eq_max_neg] -- [compile-fix: current name/orientation of the absolute-value max lemma]
        -- API?: max_div_div_right for a positive denominator and
        -- max x (-x)=|x|. Both are elementary order identities.
    change (ridgeLinear a sx sy w) 2≤
      -(a/eta)*max (sx*(ridgeLinear a sx sy w) 0)
        (sy*(ridgeLinear a sx sy w) 1) ↔ _
    have hx2 : sx*sx=1 := by rcases hx with rfl|rfl <;> norm_num
    have hy2 : sy*sy=1 := by rcases hy with rfl|rfl <;> norm_num
    simp [ridgeLinear,pt,PiLp.toLp_apply,←mul_assoc,hx2,hy2,
      prism,ridgeSection,axisSplit_snd] -- [compile-fix: unfold applications and the meridian membership predicate]
    rw [hmax]
    have hdifference :
        (e*w 1/d-t*w 2/d)-
          (-t*(|w 0|/e+t*w 1/(e*d)+w 2/d))=
        (d/e)*(w 1+(t/d)*|w 0|) := by
      calc
        _ = ((e^2+t^2)*w 1+t*d*|w 0|)/(e*d) := by
          field_simp [ne_of_gt he0,ne_of_gt hd0]; ring
        _ = (d^2*w 1+t*d*|w 0|)/(e*d) := by
          rw [show e^2+t^2=d^2 by linarith [he2,hd2]]
        _ = (d/e)*(w 1+(t/d)*|w 0|) := by
          field_simp [ne_of_gt he0,ne_of_gt hd0] -- [compile-fix: field_simp now closes this normalization]
    have hde : 0 < d/e := div_pos hd0 he0
    constructor -- [compile-fix begin: normalize the delivered equivalent inequalities explicitly]
    · intro h
      have hz :
          (e*w 1/d-t*w 2/d)-
            (-t*(|w 0|/e+t*w 1/(e*d)+w 2/d)) ≤ 0 := by
        linarith
      rw [hdifference] at hz
      have hinner : w 1+(t/d)*|w 0| ≤ 0 := by nlinarith
      linarith
    · intro h
      have hz : w 1+(t/d)*|w 0| ≤ 0 := by linarith
      have hz' :
          (e*w 1/d-t*w 2/d)-
            (-t*(|w 0|/e+t*w 1/(e*d)+w 2/d)) ≤ 0 := by
        rw [hdifference]
        exact mul_nonpos_of_nonneg_of_nonpos hde.le hz
      linarith -- [compile-fix end]
  ext x
  constructor
  · intro hxC
    exact ⟨(ridgeAxes a sx sy hx hy).symm x,
      (hpoint _).mp (by simpa using hxC),by simp⟩
  · rintro ⟨w,hw,rfl⟩
    exact (hpoint w).mpr hw

end
end R44.DischargeMeridianFrames
