/- -- [compile-fix]
# Scalar calculus for the R44 tube maps

Written proof: proof/ALIGNMENT_PROOF.md A§1; the explicit inverse was also
spelled out in the round-1 external review. ERRATA E6 concerns ownership in
assemblies, not the one-native-tube calculation here.

The inverse is written with continuous clamps, rather than using a piecewise
function and leaving its seam continuity implicit. This file imports neither
MeshSemantics nor an admitted field. It has no mathematical admissions.
API-sensitive topology calls not checked against a local Mathlib checkout are
marked at their use sites. Lean compilation is delegated to the recipient.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.NativeGeometry -- [compile-fix]

namespace R44.DischargeTube
open Set
noncomputable section

/-- The clipped linear ramp. -/
def clip (t : ℝ) : ℝ := min 1 (max 0 t)

def forward (ρ b z : ℝ) : ℝ := z + max 0 (1 - |z| / ρ) * b

/-- Inverse of the normal-line map, for |b| < ρ.
In the middle intervals it is ρ(y-b)/(ρ+b) and ρ(y-b)/(ρ-b).
The formula is continuous without testing y against a moving breakpoint. -/
def backward (ρ b y : ℝ) : ℝ :=
  y - b * clip ((y + ρ) / (ρ + b)) + b * clip ((y - b) / (ρ - b))

@[simp] theorem clip_of_nonpos {t : ℝ} (ht : t ≤ 0) : clip t = 0 := by
  simp [clip, max_eq_left ht]

@[simp] theorem clip_of_ge_one {t : ℝ} (ht : 1 ≤ t) : clip t = 1 := by
  rw [clip, max_eq_right (by linarith), min_eq_left ht]

theorem clip_of_mem {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) : clip t = t := by
  rw [clip, max_eq_right ht.1, min_eq_right ht.2]

theorem backward_low {ρ b y : ℝ} (hb : |b| < ρ) (hy : y ≤ -ρ) :
    backward ρ b y = y := by
  have hρ := lt_of_le_of_lt (abs_nonneg b) hb
  rcases abs_lt.mp hb with ⟨hbl, hbu⟩
  have hd₁ : 0 < ρ + b := by linarith
  have hd₂ : 0 < ρ - b := by linarith
  have h₁ : (y + ρ) / (ρ + b) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd₁.le
  have h₂ : (y - b) / (ρ - b) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd₂.le
  simp [backward, clip_of_nonpos h₁, clip_of_nonpos h₂]

theorem backward_left {ρ b y : ℝ} (hb : |b| < ρ)
    (hy : -ρ ≤ y ∧ y ≤ b) :
    backward ρ b y = ρ * (y - b) / (ρ + b) := by
  rcases abs_lt.mp hb with ⟨hbl, hbu⟩
  have hd₁ : 0 < ρ + b := by linarith
  have hd₂ : 0 < ρ - b := by linarith
  have h₁ : 0 ≤ (y + ρ) / (ρ + b) ∧ (y + ρ) / (ρ + b) ≤ 1 := by
    exact ⟨div_nonneg (by linarith [hy.1]) hd₁.le,
      (div_le_one hd₁).mpr (by linarith [hy.2])⟩
  have h₂ : (y - b) / (ρ - b) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith [hy.2]) hd₂.le
  rw [backward, clip_of_mem h₁, clip_of_nonpos h₂]
  field_simp [ne_of_gt hd₁]
  <;> ring

theorem backward_right {ρ b y : ℝ} (hb : |b| < ρ)
    (hy : b ≤ y ∧ y ≤ ρ) :
    backward ρ b y = ρ * (y - b) / (ρ - b) := by
  rcases abs_lt.mp hb with ⟨hbl, hbu⟩
  have hd₁ : 0 < ρ + b := by linarith
  have hd₂ : 0 < ρ - b := by linarith
  have h₁ : 1 ≤ (y + ρ) / (ρ + b) :=
    (one_le_div hd₁).mpr (by linarith [hy.1])
  have h₂ : 0 ≤ (y - b) / (ρ - b) ∧ (y - b) / (ρ - b) ≤ 1 := by
    exact ⟨div_nonneg (by linarith [hy.1]) hd₂.le,
      (div_le_one hd₂).mpr (by linarith [hy.2])⟩
  rw [backward, clip_of_ge_one h₁, clip_of_mem h₂]
  field_simp [ne_of_gt hd₂]
  <;> ring

theorem backward_high {ρ b y : ℝ} (hb : |b| < ρ) (hy : ρ ≤ y) :
    backward ρ b y = y := by
  rcases abs_lt.mp hb with ⟨hbl, hbu⟩
  have hd₁ : 0 < ρ + b := by linarith
  have hd₂ : 0 < ρ - b := by linarith
  have h₁ : 1 ≤ (y + ρ) / (ρ + b) :=
    (one_le_div hd₁).mpr (by linarith)
  have h₂ : 1 ≤ (y - b) / (ρ - b) :=
    (one_le_div hd₂).mpr (by linarith)
  simp [backward, clip_of_ge_one h₁, clip_of_ge_one h₂]
  <;> ring

theorem forward_outside {ρ b z : ℝ} (hρ : 0 < ρ) (hz : ρ ≤ |z|) :
    forward ρ b z = z := by
  have hcut : 1 - |z| / ρ ≤ 0 := by
    have h := (one_le_div hρ).mpr hz
    linarith
  simp [forward, max_eq_left hcut]

theorem forward_left {ρ b z : ℝ} (hρ : 0 < ρ)
    (hz : -ρ ≤ z ∧ z ≤ 0) :
    forward ρ b z = b + z * (ρ + b) / ρ := by
  have habs : |z| = -z := abs_of_nonpos hz.2
  have hcut : 0 ≤ 1 - |z| / ρ := by
    rw [habs]
    have h := (div_le_one hρ).mpr (show -z ≤ ρ by linarith [hz.1])
    linarith
  rw [forward, max_eq_right hcut, habs]
  field_simp [ne_of_gt hρ]
  <;> ring

theorem forward_right {ρ b z : ℝ} (hρ : 0 < ρ)
    (hz : 0 ≤ z ∧ z ≤ ρ) :
    forward ρ b z = b + z * (ρ - b) / ρ := by
  have hcut : 0 ≤ 1 - |z| / ρ := by
    rw [abs_of_nonneg hz.1]
    have h := (div_le_one hρ).mpr hz.2
    linarith
  rw [forward, max_eq_right hcut, abs_of_nonneg hz.1]
  field_simp [ne_of_gt hρ]
  <;> ring

theorem forward_left_range {ρ b z : ℝ} (hb : |b| < ρ)
    (hz : -ρ ≤ z ∧ z ≤ 0) :
    -ρ ≤ forward ρ b z ∧ forward ρ b z ≤ b := by
  have hρ := lt_of_le_of_lt (abs_nonneg b) hb
  rcases abs_lt.mp hb with ⟨hbl, hbu⟩
  have hd : 0 < ρ + b := by linarith
  rw [forward_left hρ hz]
  constructor
  · have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hz.1 hd.le) hρ.le
    have hs : (-ρ) * (ρ + b) / ρ = -(ρ + b) := by
      field_simp [ne_of_gt hρ]
      <;> ring
    rw [hs] at hm
    linarith
  · have hm : z * (ρ + b) / ρ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hz.2 hd.le) hρ.le
    linarith

theorem forward_right_range {ρ b z : ℝ} (hb : |b| < ρ)
    (hz : 0 ≤ z ∧ z ≤ ρ) :
    b ≤ forward ρ b z ∧ forward ρ b z ≤ ρ := by
  have hρ := lt_of_le_of_lt (abs_nonneg b) hb
  rcases abs_lt.mp hb with ⟨hbl, hbu⟩
  have hd : 0 < ρ - b := by linarith
  rw [forward_right hρ hz]
  constructor
  · have hm := div_nonneg (mul_nonneg hz.1 hd.le) hρ.le
    linarith
  · have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hz.2 hd.le) hρ.le
    have hs : ρ * (ρ - b) / ρ = ρ - b := by field_simp [ne_of_gt hρ]
    rw [hs] at hm
    linarith

/-- The left inverse holds also at all four seam points. -/
theorem backward_forward {ρ b : ℝ} (hb : |b| < ρ) (z : ℝ) :
    backward ρ b (forward ρ b z) = z := by
  have hρ := lt_of_le_of_lt (abs_nonneg b) hb
  have hd₁ : ρ + b ≠ 0 := ne_of_gt (by linarith [(abs_lt.mp hb).1])
  have hd₂ : ρ - b ≠ 0 := ne_of_gt (by linarith [(abs_lt.mp hb).2])
  by_cases hz₀ : z ≤ -ρ
  · rw [forward_outside hρ (by rw [abs_of_nonpos (by linarith)]; linarith),
      backward_low hb hz₀]
  by_cases hz₁ : z ≤ 0
  · have hz : -ρ ≤ z ∧ z ≤ 0 := ⟨by linarith, hz₁⟩
    rw [backward_left hb (forward_left_range hb hz), forward_left hρ hz]
    field_simp [ne_of_gt hρ, hd₁]
    <;> ring
  by_cases hz₂ : z ≤ ρ
  · have hz : 0 ≤ z ∧ z ≤ ρ := ⟨by linarith, hz₂⟩
    rw [backward_right hb (forward_right_range hb hz), forward_right hρ hz]
    field_simp [ne_of_gt hρ, hd₂]
    <;> ring
  · have hz : ρ ≤ z := by linarith
    rw [forward_outside hρ (by rw [abs_of_nonneg (by linarith)]; exact hz),
      backward_high hb hz]

/-- Surjectivity is proved by the same four explicit intervals; it is not
inferred from a merely left-invertible continuous map. -/
theorem forward_backward {ρ b : ℝ} (hb : |b| < ρ) (y : ℝ) :
    forward ρ b (backward ρ b y) = y := by
  have hρ := lt_of_le_of_lt (abs_nonneg b) hb
  rcases abs_lt.mp hb with ⟨hbl, hbu⟩
  have hd₁ : 0 < ρ + b := by linarith
  have hd₂ : 0 < ρ - b := by linarith
  by_cases hy₀ : y ≤ -ρ
  · rw [backward_low hb hy₀,
      forward_outside hρ (by rw [abs_of_nonpos (by linarith)]; linarith)]
  by_cases hy₁ : y ≤ b
  · rw [backward_left hb ⟨by linarith, hy₁⟩]
    have hz : -ρ ≤ ρ * (y-b) / (ρ+b) ∧ ρ * (y-b) / (ρ+b) ≤ 0 := by
      constructor
      · apply (le_div_iff₀ hd₁).mpr
        nlinarith
      · exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos hρ.le (sub_nonpos.mpr hy₁)) hd₁.le
    rw [forward_left hρ hz]
    field_simp [ne_of_gt hρ, ne_of_gt hd₁]
    <;> ring
  by_cases hy₂ : y ≤ ρ
  · rw [backward_right hb ⟨by linarith, hy₂⟩]
    have hz : 0 ≤ ρ * (y-b) / (ρ-b) ∧ ρ * (y-b) / (ρ-b) ≤ ρ := by
      constructor
      · exact div_nonneg (mul_nonneg hρ.le
          (sub_nonneg.mpr (le_of_not_ge hy₁))) hd₂.le
      · apply (div_le_iff₀ hd₂).mpr
        nlinarith
    rw [forward_right hρ hz]
    field_simp [ne_of_gt hρ, ne_of_gt hd₂]
    <;> ring
  · rw [backward_high hb (by linarith),
      forward_outside hρ (by rw [abs_of_nonneg (by linarith)]; linarith)]

/-- Image of the planar dividing point: the lower half-line maps precisely
onto the lower side of the displaced graph. -/
theorem forward_le_height_iff {ρ b : ℝ} (hb : |b| < ρ) (z : ℝ) :
    forward ρ b z ≤ b ↔ z ≤ 0 := by
  have hρ := lt_of_le_of_lt (abs_nonneg b) hb
  rcases abs_lt.mp hb with ⟨hbl, hbu⟩
  by_cases hz₀ : z ≤ -ρ
  · rw [forward_outside hρ (by rw [abs_of_nonpos (by linarith)]; linarith)]
    exact iff_of_true (by linarith) (by linarith)
  by_cases hz₁ : z ≤ 0
  · exact iff_of_true (forward_left_range hb ⟨by linarith, hz₁⟩).2 hz₁
  by_cases hz₂ : z ≤ ρ
  · rw [forward_right hρ ⟨by linarith, hz₂⟩]
    have hpos : 0 < z * (ρ-b) / ρ :=
      div_pos (mul_pos (by linarith) (by linarith)) hρ
    constructor <;> intro h <;> linarith
  · rw [forward_outside hρ (by rw [abs_of_nonneg (by linarith)]; linarith)]
    constructor <;> intro h <;> linarith

theorem forward_mem_interval {ρ b z : ℝ} (hb : |b| < ρ) (hz : |z| ≤ ρ) :
    |forward ρ b z| ≤ ρ := by
  rcases abs_le.mp hz with ⟨hzl,hzu⟩
  rcases abs_lt.mp hb with ⟨hbl,hbu⟩
  apply abs_le.mpr
  by_cases h : z ≤ 0
  · have hf := forward_left_range hb ⟨hzl,h⟩
    exact ⟨hf.1, hf.2.trans hbu.le⟩
  · have hf := forward_right_range hb ⟨by linarith,hzu⟩
    exact ⟨hbl.le.trans hf.1, hf.2⟩

/-- Continuity of the parameter-dependent inverse. Denominators never vanish
because the parameter has |b|<ρ at every input, not only at a single point. -/
theorem backward_continuous {X : Type*} [TopologicalSpace X]
    {ρ : ℝ} {b y : X → ℝ} (hb : Continuous b) (hy : Continuous y)
    (hsmall : ∀ x, |b x| < ρ) :
    Continuous (fun x => backward ρ (b x) (y x)) := by
  have hp : ∀ x, ρ + b x ≠ 0 := by
    intro x
    exact ne_of_gt (by linarith [(abs_lt.mp (hsmall x)).1])
  have hm : ∀ x, ρ - b x ≠ 0 := by
    intro x
    exact ne_of_gt (by linarith [(abs_lt.mp (hsmall x)).2])
  have hc₁ : Continuous (fun x => clip ((y x+ρ)/(ρ+b x))) := by
    unfold clip
    exact continuous_const.min
      (continuous_const.max ((hy.add continuous_const).div
        (continuous_const.add hb) hp))
  have hc₂ : Continuous (fun x => clip ((y x-b x)/(ρ-b x))) := by
    unfold clip
    exact continuous_const.min
      (continuous_const.max ((hy.sub hb).div
        (continuous_const.sub hb) hm))
  exact (hy.sub (hb.mul hc₁)).add (hb.mul hc₂)

end
end R44.DischargeTube
