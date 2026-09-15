/- -- [compile-fix: promoted to Proved after exchange 7]
# Principal, oriented angular normal forms for the two signed tent sections

Written source: proof/ALIGNMENT_PROOF.md A-L3.1 and A-L2.2. This supplies
SET equalities, with both bounding rays retained, not just equalities of
normal dot products. The aperture can exceed pi (negative ridge / positive
base). No mesh enumeration, tiling assumption, or solid-angle conclusion is
used here. The angularSector and volume normalizations are imported without
change from exchange 6.

No mathematical admissions. The compiler is not available to this author;
Mathlib-name-sensitive calls are explicitly marked API?.
-/
import R44.Proved.TentMeridianReduction -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeAngular
open Set Complex DischargeWedge DischargePlanar DischargePyramid
open DischargeMeridianFrames
noncomputable section
set_option maxHeartbeats 0

@[simp] theorem baseAxes_apply (w : E3) : baseAxes w=pt (w 0) (w 2) (w 1) := rfl

/-- A rotation in the meridian plane, leaving its third coordinate fixed. -/
def turnLinear (b : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun := fun w => pt (Real.cos b*w 0-Real.sin b*w 1)
    (Real.sin b*w 0+Real.cos b*w 1) (w 2)
  map_add' := by intros; ext i; fin_cases i <;> simp [pt] <;> ring
  map_smul' := by intros; ext i; fin_cases i <;> simp [pt] <;> ring

private theorem turn_norm (b : ℝ) (w : E3) : ‖turnLinear b w‖=‖w‖ := by
  have ht := Real.sin_sq_add_cos_sq b
  have he : ‖turnLinear b w‖^2=‖w‖^2 := by
    -- [compile-fix begin: current WithLp/vector simplification]
    simp [DischargePyramid.norm_sq, turnLinear, pt]
    ring_nf
    nlinarith [ht]
    -- [compile-fix end]
  nlinarith [norm_nonneg (turnLinear b w), norm_nonneg w]

private def turnIso (b : ℝ) : E3 →ₗᵢ[ℝ] E3 where
  toLinearMap := turnLinear b
  norm_map' := turn_norm b

def turn (b : ℝ) : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.ofSurjective (turnIso b) (by
    intro w
    refine ⟨turnLinear (-b) w, ?_⟩
    have h := Real.sin_sq_add_cos_sq b
    ext i; fin_cases i <;>
      simp [turnIso,turnLinear,pt,Real.sin_neg,Real.cos_neg] <;>
      nlinarith [congrArg (fun z : ℝ => z*w 0) h,
        congrArg (fun z : ℝ => z*w 1) h])

@[simp] theorem turn_apply (b : ℝ) (w : E3) :
    turn b w=pt (Real.cos b*w 0-Real.sin b*w 1)
      (Real.sin b*w 0+Real.cos b*w 1) (w 2) := rfl

theorem set_image_of_test (A : E3 ≃ₗᵢ[ℝ] E3) (S T : Set E3)
    (h : ∀w,A w∈S ↔ w∈T) : S=A '' T := by
  ext x
  constructor
  · intro hx
    exact ⟨A.symm x,(h _).mp (by simpa using hx),by simp⟩
  · rintro ⟨w,hw,rfl⟩
    exact (h w).mpr hw

private theorem sin_sign {u : ℝ} (hl : -Real.pi<u) (hu : u<Real.pi) :
    0≤Real.sin u ↔ 0≤u := by
  constructor
  · intro h
    by_contra hn
    have hn' : u<0 := lt_of_not_ge hn
    have hp := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr hn') (by linarith : -u<Real.pi)
    rw [Real.sin_neg] at hp
    linarith
  · intro h
    exact Real.sin_nonneg_of_nonneg_of_le_pi h hu.le

/-- Cartesian description on the principal branch. theta=0 is intentionally
excluded: its degenerate sector would require an extra right-ray condition. -/
theorem angularSector_cartesian (theta : ℝ)
    (ht : 0<theta) (hu : theta<2*Real.pi) (w : E2) :
    w∈angularSector theta ↔
      Real.cos (theta/2)*|w 1|≤Real.sin (theta/2)*w 0 := by
  let z : ℂ := complexCoordinates w
  let a := z.arg
  let b := theta/2
  have hb0 : 0<b := by dsimp [b]; linarith
  have hbπ : b<Real.pi := by dsimp [b]; linarith
  have ha : |a|≤Real.pi := by
    apply abs_le.mpr
    exact ⟨(Complex.neg_pi_lt_arg z).le,Complex.arg_le_pi z⟩
    -- API?: Complex.neg_pi_lt_arg and Complex.arg_le_pi are the principal
    -- argument bounds -pi < arg z <= pi, also for z=0.
  have habsSin : |Real.sin a|=Real.sin |a| := by
    exact Real.abs_sin_eq_sin_abs_of_abs_le_pi ha -- [compile-fix: current trig API]
  have habsCos : Real.cos a=Real.cos |a| := by
    rcases le_total 0 a with h|h <;> simp [abs_of_nonneg,abs_of_nonpos,h]
  by_cases hz : z=0
  · have h0 : w 0=0 := by
      have hh := congrArg Complex.re hz
      simpa [z,complexCoordinates_apply] using hh
    have h1 : w 1=0 := by
      have hh := congrArg Complex.im hz
      simpa [z,complexCoordinates_apply] using hh
    -- [compile-fix begin: expose the residual nonnegative half-angle]
    simp [angularSector,complexSector,z,hz,h0,h1]
    exact div_nonneg ht.le (by norm_num)
    -- [compile-fix end]
  · have hn : 0<‖z‖ := norm_pos_iff.mpr hz
    have hx : w 0=‖z‖*Real.cos a := by
      have hh := Complex.norm_mul_cos_arg z
      -- API?: Complex.norm_mul_cos_arg : norm z * cos(arg z) = z.re.
      simpa [z,a,complexCoordinates_apply] using hh.symm
    have hy : w 1=‖z‖*Real.sin a := by
      have hh := Complex.norm_mul_sin_arg z
      -- API?: Complex.norm_mul_sin_arg : norm z * sin(arg z) = z.im.
      simpa [z,a,complexCoordinates_apply] using hh.symm
    have hid : Real.sin b*w 0-Real.cos b*|w 1|=
        ‖z‖*Real.sin (b-|a|) := by
      rw [hx,hy,abs_mul,abs_of_pos hn,habsSin,habsCos,Real.sin_sub]
      ring
    have hl : -Real.pi<b-|a| := by linarith
    have hu' : b-|a|<Real.pi := by linarith [abs_nonneg a]
    simp only [angularSector, complexSector, Set.mem_preimage, Set.mem_setOf_eq]
    change (-(theta/2)≤a ∧ a≤theta/2) ↔ _ -- [compile-fix: unfold set membership]
    -- [compile-fix begin: target the Cartesian inequality explicitly]
    rw [← abs_le]
    constructor
    · intro hab
      have hsin : 0 ≤ Real.sin (b - |a|) :=
        (sin_sign hl hu').2 (sub_nonneg.mpr (by simpa [b] using hab))
      have hprod : 0 ≤ ‖z‖ * Real.sin (b - |a|) := mul_nonneg hn.le hsin
      rw [← hid] at hprod
      linarith
    · intro hcart
      have hdiff : 0 ≤ Real.sin b*w 0-Real.cos b*|w 1| := by linarith
      rw [hid, mul_nonneg_iff_of_pos_left hn, sin_sign hl hu', sub_nonneg] at hdiff
      simpa [b] using hdiff
    -- [compile-fix end]

/-- The V-shaped hypograph points downward. This exact rotation retains
both the convex and the reentrant aperture cases. -/
theorem lowerV_angular (k : ℝ) :
    let theta := Real.pi-2*Real.arctan k
    0<theta ∧ theta<2*Real.pi ∧
      {w:E3 | w 1≤-k*|w 0|}=
        turn (-Real.pi/2) '' prism (angularSector theta) := by
  dsimp only
  have hbL := Real.neg_pi_div_two_lt_arctan k
  have hbU := Real.arctan_lt_pi_div_two k
  have ht : 0<Real.pi-2*Real.arctan k := by linarith
  have hu : Real.pi-2*Real.arctan k<2*Real.pi := by linarith
  refine ⟨ht,hu,?_⟩
  apply set_image_of_test
  intro w
  have hθ : (Real.pi-2*Real.arctan k)/2=Real.pi/2-Real.arctan k := by ring
  have hc : 0<Real.cos (Real.arctan k) := by
    rw [Real.cos_arctan]; positivity
    -- API?: Real.cos_arctan k = 1 / sqrt(1+k^2).
  have hs : Real.sin (Real.arctan k)=k*Real.cos (Real.arctan k) := by
    rw [Real.sin_arctan,Real.cos_arctan]; ring
    -- API?: Real.sin_arctan k = k / sqrt(1+k^2).
  change (turn (-Real.pi/2) w) 1 ≤ -k * |(turn (-Real.pi/2) w) 0| ↔
    (axisSplit w).2∈angularSector (Real.pi-2*Real.arctan k) -- [compile-fix: expose image membership]
  rw [angularSector_cartesian _ ht hu,hθ]
  have hangle : -Real.pi/2 = -(Real.pi/2) := by ring -- [compile-fix]
  rw [hangle]
  simp only [axisSplit_snd,turn_apply,pt,Real.cos_neg,Real.sin_neg,
    Real.cos_pi_div_two,Real.sin_pi_div_two,Real.sin_sub,Real.cos_sub,
    zero_mul,one_mul,neg_one_mul,sub_zero,zero_sub,add_zero,
    Matrix.cons_val_zero,Matrix.cons_val_one] -- [compile-fix: obsolete WithLp lemma]
  rw [hs]
  -- [compile-fix begin: cancel the positive cosine explicitly]
  constructor
  · intro h
    simp only [neg_neg, abs_neg] at h -- [compile-fix]
    have hk : k * |w 1| ≤ w 0 := by linarith
    have hcanceled : Real.cos (Real.arctan k) * (k * |w 1|) ≤
        Real.cos (Real.arctan k) * w 0 :=
      (mul_le_mul_iff_right₀ hc).2 hk
    convert hcanceled using 1 <;> simp <;> ring
  · intro h
    have h' : Real.cos (Real.arctan k) * (k * |w 1|) ≤
        Real.cos (Real.arctan k) * w 0 := by
      convert h using 1 <;> simp <;> ring
    have hk := (mul_le_mul_iff_right₀ hc).mp h'
    simp only [neg_neg, abs_neg] -- [compile-fix]
    linarith
  -- [compile-fix end]

-- [compile-fix begin: parser and ordered-field API]
private theorem le_signed_abs (m u v : ℝ) :
    v ≤ m * |u| ↔ (if 0 ≤ m then (v ≤ m*u ∨ v ≤ -m*u) else (v ≤ m*u ∧ v ≤ -m*u)) := by
  by_cases hm : 0 ≤ m <;> by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu, if_pos hm]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · have hmu : 0 ≤ m*u := mul_nonneg hm hu
        nlinarith
  · have hu' : u ≤ 0 := le_of_not_ge hu
    rw [abs_of_nonpos hu', if_pos hm]
    constructor
    · intro h
      right
      convert h using 1 <;> ring
    · rintro (h | h)
      · have hmu : m*u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm hu'
        nlinarith
      · convert h using 1 <;> ring
  · have hm' : m ≤ 0 := le_of_not_ge hm
    rw [abs_of_nonneg hu, if_neg hm]
    constructor
    · intro h
      refine ⟨h, ?_⟩
      have hmu : m*u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hm' hu
      nlinarith
    · exact fun h => h.1
  · have hm' : m ≤ 0 := le_of_not_ge hm
    have hu' : u ≤ 0 := le_of_not_ge hu
    rw [abs_of_nonpos hu', if_neg hm]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have hmu : 0 ≤ m*u := mul_nonneg_of_nonpos_of_nonpos hm' hu'
        nlinarith
      · convert h using 1 <;> ring
    · intro h
      convert h.2 using 1 <;> ring

/-- Pure ordered-field core of the asymmetric base-sector rotation. -/
private theorem base_rotation_algebra (c s t u v : ℝ)
    (hc : 0<c) (hcs : c^2+s^2=1) (hd : 0<c^2-s^2)
    (ht : t*(c^2-s^2)=2*s*c) :
    s*u+c*v≤t*max 0 (c*u-s*v) ↔ v≤(s/c)*|u| := by
  have he0 : s*u+c*v=c*(v+(s/c)*u) := by
    field_simp [ne_of_gt hc]; ring
  have he1 : (s*u+c*v)-t*(c*u-s*v)=
      (c/(c^2-s^2))*(v-(s/c)*u) := by
    field_simp [ne_of_gt hc,ne_of_gt hd]
    linear_combination -(u*c-s*v)*ht + (c*v-s*u)*hcs -- [compile-fix: normalize polynomial identity]
  have h0 : s*u+c*v≤0 ↔ v≤-(s/c)*u := by
    rw [he0]
    constructor <;> intro h
    · have : v + (s / c) * u ≤ 0 := by nlinarith
      linarith
    · have : v + (s / c) * u ≤ 0 := by linarith
      nlinarith
  have h1 : s*u+c*v≤t*(c*u-s*v) ↔ v≤(s/c)*u := by
    rw [← sub_nonpos, he1]
    have hfactor : 0 < c / (c ^ 2 - s ^ 2) := div_pos hc hd
    constructor <;> intro h
    · have : v - (s / c) * u ≤ 0 := by nlinarith
      exact sub_nonpos.mp this
    · have : v - (s / c) * u ≤ 0 := sub_nonpos.mpr h
      nlinarith
  by_cases hs : 0 ≤ s
  · have htp : 0 ≤ t := by nlinarith
    have hm : 0 ≤ s/c := div_nonneg hs hc.le
    rw [mul_max_of_nonneg _ _ htp,mul_zero,le_max_iff,h0,h1,
      le_signed_abs,if_pos hm]
    tauto
  · have hsn : s < 0 := lt_of_not_ge hs
    have htn : t < 0 := by nlinarith
    have hm : ¬ 0 ≤ s/c := not_le_of_gt (div_neg_of_neg_of_pos hsn hc)
    have hmul : t * max 0 (c*u-s*v) = min (t*0) (t*(c*u-s*v)) := by
      by_cases hB : 0 ≤ c*u-s*v
      · rw [max_eq_right hB, min_eq_right]
        simpa using mul_nonpos_of_nonpos_of_nonneg htn.le hB
      · have hB' : c*u-s*v ≤ 0 := le_of_not_ge hB
        rw [max_eq_left hB', min_eq_left]
        simpa using mul_nonneg_of_nonpos_of_nonpos htn.le hB'
    rw [hmul,mul_zero,le_min_iff,h0,h1,
      le_signed_abs,if_neg hm]
    tauto
-- [compile-fix end]

/-- Canonical base section and its signed aperture pi+atan(t), t=a/eta. -/
theorem base_section_angular (a : ℝ) :
    let theta := Real.pi+Real.arctan (a/eta)
    0<theta ∧ theta<2*Real.pi ∧
      prism (baseSection a)=
        (turn (Real.arctan (a/eta)/2)*turn (-Real.pi/2)) ''
          prism (angularSector theta) := by
  let t := a/eta
  let b := Real.arctan t/2
  have hbL : -(Real.pi/2)<b := by -- [compile-fix: match principal-interval syntax]
    dsimp [b]; linarith [Real.neg_pi_div_two_lt_arctan t,Real.pi_pos]
  have hbU : b<Real.pi/2 := by
    dsimp [b]; linarith [Real.arctan_lt_pi_div_two t,Real.pi_pos]
  have hc : 0<Real.cos b := Real.cos_pos_of_mem_Ioo ⟨hbL,hbU⟩
    -- API?: Real.cos_pos_of_mem_Ioo : -pi/2 < b and b < pi/2 imply cos b > 0.
  have htwo : 2*b=Real.arctan t := by dsimp [b]; ring
  have hcs : (Real.cos b)^2+(Real.sin b)^2=1 := by
    nlinarith [Real.sin_sq_add_cos_sq b]
  have hdEq : (Real.cos b)^2-(Real.sin b)^2=Real.cos (Real.arctan t) := by
    rw [←htwo,Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq b]
  have hd : 0<(Real.cos b)^2-(Real.sin b)^2 := by
    rw [hdEq,Real.cos_arctan]; positivity
  have htEq : t*((Real.cos b)^2-(Real.sin b)^2)=2*Real.sin b*Real.cos b := by
    rw [hdEq,←Real.sin_two_mul,htwo,Real.sin_arctan,Real.cos_arctan]
    ring
  have htan : Real.tan b=Real.sin b/Real.cos b := Real.tan_eq_sin_div_cos b
  have hset : prism (baseSection a)=turn b ''
      {w:E3 | w 1≤Real.tan b*|w 0|} := by
    apply set_image_of_test
    intro w
    simpa [prism,baseSection,axisSplit_snd,turn_apply,pt,t,htan] using
      base_rotation_algebra (Real.cos b) (Real.sin b) t (w 0) (w 1) hc hcs hd htEq
  obtain ⟨hθl,hθu,hV⟩ := lowerV_angular (-Real.tan b)
  have hθ : Real.pi-2*Real.arctan (-Real.tan b)=Real.pi+Real.arctan t := by
    rw [Real.arctan_neg,Real.arctan_tan hbL hbU]
    -- API?: Real.arctan_tan has the two strict principal-branch bounds.
    dsimp [b]; ring
  rw [hθ] at hV hθl hθu
  refine ⟨hθl,hθu,?_⟩
  rw [hset,show {w:E3 | w 1≤Real.tan b*|w 0|}=
      {w:E3 | w 1≤-(-Real.tan b)*|w 0|} by simp,hV,Set.image_image]
  rfl

/-- Principal-branch identity. The sign is determined BEFORE arccos is used. -/
theorem ridge_principal (t : ℝ) (ht : t≠0) :
    2*Real.arctan (t/Real.sqrt (2+t^2))=
      if 0<t then Real.arccos (1/(1+t^2)) else -Real.arccos (1/(1+t^2)) := by
  let d := Real.sqrt (2+t^2)
  let k := t/d
  have hd : 0<d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d^2=2+t^2 := Real.sq_sqrt (by positivity)
  have hs : 0<Real.sqrt (1+k^2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : (Real.sqrt (1+k^2))^2=1+k^2 := Real.sq_sqrt (by positivity)
  have hcos : Real.cos (2*Real.arctan k)=1/(1+t^2) := by
    rw [two_mul,Real.cos_add,Real.cos_arctan,Real.sin_arctan]
    have he : (1/Real.sqrt (1+k^2))^2-(k/Real.sqrt (1+k^2))^2=
        (1-k^2)/(1+k^2) := by
      field_simp [ne_of_gt hs,ne_of_gt (show 0<1+k^2 by positivity)]
      nlinarith [hs2]
    calc
      _ = (1-k^2)/(1+k^2) := by convert he using 1 <;> ring
      _ = 1/(1+t^2) := by
        dsimp [k]
        field_simp [ne_of_gt hd,ne_of_gt (show 0<1+t^2 by positivity)]
        nlinarith [hd2]
  have hbL := Real.neg_pi_div_two_lt_arctan k
  have hbU := Real.arctan_lt_pi_div_two k
  by_cases hp : 0<t
  · have hk : 0<k := div_pos hp hd
    have ha : 0<Real.arctan k := Real.arctan_pos.mpr hk
      -- API?: Real.arctan_pos : 0 < arctan x iff 0 < x.
    have he := Real.arccos_cos (by linarith : 0≤2*Real.arctan k)
      (by linarith : 2*Real.arctan k≤Real.pi)
      -- API?: Real.arccos_cos on [0,pi].
    rw [hcos] at he
    simpa [hp,k,d] using he.symm
  · have hn : t<0 := lt_of_le_of_ne (le_of_not_gt hp) ht
    have hk : k<0 := div_neg_of_neg_of_pos hn hd
    have ha : Real.arctan k<0 := by
      simpa using Real.arctan_strictMono hk
      -- API?: Real.arctan_strictMono : StrictMono Real.arctan,
      -- the same API used in accepted CompleteDihedralList.
    have he := Real.arccos_cos (by linarith : 0≤-(2*Real.arctan k))
      (by linarith : -(2*Real.arctan k)≤Real.pi)
    rw [Real.cos_neg,hcos] at he
    simpa [hp,k,d] using congrArg Neg.neg he.symm

end
end R44.DischargeAngular
