/-
# Discharge: circular_cone_solid_angle

Written proof: proof/ALIGNMENT_PROOF.md A-L4.1, the circular-cone integral.
No ERRATA changes this formula. We follow the volume calculation, using
horizontal circular slices instead of introducing spherical coordinates.
This is the same Cavalieri/Fubini integral: the cutoff is L/sqrt(1+L²),
and the slice is limited either by the unit sphere or by the cone.

The frozen definition solidAngle = 3 * volume(C ∩ closedBall 0 1) is retained.
In particular no real-valued formula is substituted for that definition.
There are no mathematical admissions and no dependencies on MeshSemantics,
Hypotheses, or another residual field. New/unconfirmed pinned-library calls
are marked API? inline. The scripts have not been locally compiled.

This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.LogicalSpineFoundation -- [compile-fix]

namespace R44
open Set MeasureTheory
open scoped ENNReal Interval
noncomputable section

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private def ell : ℝ := 3 / 25
private def cut : ℝ := ell / Real.sqrt (1 + ell ^ 2)

private theorem cut_pos : 0 < cut := by
  unfold cut ell
  positivity

private theorem cut_sq : cut ^ 2 = 9 / 634 := by
  unfold cut ell
  rw [div_pow, Real.sq_sqrt (by positivity)]
  norm_num

private theorem cut_lt_one : cut < 1 := by
  have hp := cut_pos
  have hs := cut_sq
  nlinarith

/-- Split off the last coordinate without changing the product Lebesgue
measure. The remaining two coordinates use the Euclidean norm, not max norm.
-/
private def axisSplit : E3 ≃ᵐ (ℝ × E2) :=
  (((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))
    -- API?: expected measurable equivalence: piFinSuccAbove splits coordinate i and its complement; prodCongr acts on each product factor.

private theorem axisSplit_fst (x : E3) : (axisSplit x).1 = x 2 := by
  rfl

private theorem axisSplit_snd (x : E3) (i : Fin 2) :
    (axisSplit x).2 i = x i.castSucc := by
  fin_cases i <;> rfl

private theorem axisSplit_preserves : MeasurePreserving axisSplit volume volume := by
  change @MeasurePreserving _ _ _ (@Prod.instMeasurableSpace ℝ E2 _ _) -- [compile-fix]
    axisSplit volume ((volume : Measure ℝ).prod volume) -- [compile-fix]
  have h3 : MeasurePreserving -- [compile-fix]
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm -- [compile-fix]
      (volume : Measure E3) volume := -- [compile-fix]
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3) -- [compile-fix]
    -- API?: expected lemma: ofLp from EuclideanSpace ℝ ι to ι → ℝ preserves volume.
  have h2back : MeasurePreserving -- [compile-fix]
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm -- [compile-fix]
      (volume : Measure E2) volume := -- [compile-fix]
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2) -- [compile-fix]
    -- API?: same lemma in dimension two.
  have h2 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) volume volume := by
    simpa using MeasurePreserving.symm
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm h2back
      -- API?: expected symm(e,h): measure preservation of a measurable equivalence passes to its inverse.
  have hp := (MeasurePreserving.id (volume : Measure ℝ)).prod h2
    -- API?: expected MeasurePreserving.prod: product maps preserve product measures.
  have hc := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
    -- API?: expected coordinate-splitting volume-preservation theorem, explicit family and index.
  apply (hp.comp (hc.comp h3)).congr axisSplit.measurable -- [compile-fix]
  exact Filter.Eventually.of_forall fun _ => rfl -- [compile-fix]

private def coneSlice (z : ℝ) : Set E2 :=
  {u | z < -ell * ‖u‖ ∧ z ^ 2 + ‖u‖ ^ 2 ≤ 1}

private def splitBody : Set (ℝ × E2) :=
  {p | p.1 < -ell * ‖p.2‖ ∧ p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ 1}

private theorem splitBody_measurable : MeasurableSet splitBody := by
  apply MeasurableSet.inter
  · exact (isOpen_lt continuous_fst -- [compile-fix]
      (continuous_const.mul continuous_snd.norm)).measurableSet -- [compile-fix]
  · exact (isClosed_le ((continuous_fst.pow 2).add -- [compile-fix]
      (continuous_snd.norm.pow 2)) continuous_const).measurableSet -- [compile-fix]

private theorem split_norm_sq (x : E3) :
    ‖x‖ ^ 2 = x 2 ^ 2 + ‖(axisSplit x).2‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, axisSplit_snd,
    Real.norm_eq_abs, sq_abs]
  ring

private theorem split_tangent_norm (x : E3) :
    Real.sqrt (x 0 ^ 2 + x 1 ^ 2) = ‖(axisSplit x).2‖ := by
  have h : ‖(axisSplit x).2‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, axisSplit_snd,
      Real.norm_eq_abs, sq_abs]
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

private theorem splitBody_preimage :
    axisSplit ⁻¹' splitBody = circularCone ell ∩ Metric.closedBall (0 : E3) 1 := by
  ext x
  change (x 2 < -ell * ‖(axisSplit x).2‖ ∧
      x 2 ^ 2 + ‖(axisSplit x).2‖ ^ 2 ≤ 1) ↔ _
  simp only [Set.mem_inter_iff, circularCone, Set.mem_setOf_eq,
    Metric.mem_closedBall, dist_zero_right]
  rw [split_tangent_norm, ← split_norm_sq]
  have hn := norm_nonneg x
  constructor
  · rintro ⟨hc, hb⟩
    exact ⟨hc, by nlinarith⟩
  · rintro ⟨hc, hb⟩
    exact ⟨hc, by nlinarith⟩

/-- Tonelli with the actual ambient volume normalization. -/
private theorem cone_volume_by_slices :
    volume (circularCone ell ∩ Metric.closedBall (0 : E3) 1) =
      ∫⁻ z : ℝ, volume (coneSlice z) := by
  rw [← splitBody_preimage]
  rw [axisSplit_preserves.measure_preimage splitBody_measurable.nullMeasurableSet]
    -- API?: expected measure_preimage accepts a null-measurable set; a measurable set provides it.
  rw [Measure.volume_eq_prod, Measure.prod_apply splitBody_measurable]
    -- API?: expected prod_apply: product measure of a measurable set equals the integral of section measures.
  rfl

/-- Squeezing between an open disk and its closed disk suffices even where
the strict cone removes a circular boundary. No boundary point is silently
turned into a member of the open cone. -/
private theorem disk_squeeze {S : Set E2} {r : ℝ}
    (hr : 0 ≤ r) (hlo : Metric.ball (0 : E2) r ⊆ S)
    (hhi : S ⊆ Metric.closedBall (0 : E2) r) :
    volume S = ENNReal.ofReal (Real.pi * r ^ 2) := by
  have hb := EuclideanSpace.volume_ball_fin_two (0 : E2) r
    -- API?: expected volume of a Euclidean 2-ball: ofReal r ^ 2 * ofReal π.
  have hc := EuclideanSpace.volume_closedBall_fin_two (0 : E2) r
    -- API?: expected the same formula for the closed ball, including r = 0.
  have he : ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi =
      ENNReal.ofReal (Real.pi * r ^ 2) := by
    rw [ENNReal.ofReal_mul Real.pi_pos.le]
    simp only [pow_two, ENNReal.ofReal_mul hr]
    ring
  exact le_antisymm
    ((measure_mono hhi).trans (hc.trans he).le)
    ((hb.trans he).ge.trans (measure_mono hlo))

private theorem sphere_limited_slice {z : ℝ} (hz : -1 ≤ z ∧ z ≤ -cut) :
    volume (coneSlice z) = ENNReal.ofReal (Real.pi * (1 - z ^ 2)) := by
  have hcut0 := cut_pos
  have hcuteq := cut_sq
  have hz0 : z < 0 := by linarith
  have hzs : 0 ≤ 1 - z ^ 2 := by
    have hp : 0 ≤ (1 + z) * (1 - z) :=
      mul_nonneg (by linarith [hz.1]) (by linarith [hz.2])
    nlinarith
  let r := Real.sqrt (1 - z ^ 2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 - z ^ 2 := Real.sq_sqrt hzs
  have hza : cut ^ 2 ≤ z ^ 2 := by
    have hp : 0 ≤ (-z - cut) * (-z + cut) :=
      mul_nonneg (by linarith [hz.2]) (by linarith [hz.2])
    nlinarith
  have hprod : (ell * r) ^ 2 ≤ z ^ 2 := by
    dsimp [ell]
    nlinarith [hr2]
  have hrcone : ell * r ≤ -z := by
    have he : 0 ≤ ell * r := mul_nonneg (by norm_num [ell]) hr0
    nlinarith
  have hvol : volume (coneSlice z) = ENNReal.ofReal (Real.pi * r ^ 2) := by
    apply disk_squeeze hr0
    · intro u hu
      have hu' : ‖u‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hu
      have hmul : ell * ‖u‖ < ell * r := mul_lt_mul_of_pos_left hu' (by norm_num [ell])
      have hn := norm_nonneg u
      exact ⟨by linarith, by nlinarith⟩
    · intro u hu
      have hn := norm_nonneg u
      have hs := hu.2
      simp only [Metric.mem_closedBall, dist_zero_right]
      nlinarith
  simpa only [hr2] using hvol

private theorem cone_limited_slice {z : ℝ} (hz : -cut ≤ z ∧ z ≤ 0) :
    volume (coneSlice z) = ENNReal.ofReal (Real.pi * z ^ 2 / ell ^ 2) := by
  have hcut0 := cut_pos
  have hcuteq := cut_sq
  have hza : z ^ 2 ≤ cut ^ 2 := by
    have hp : 0 ≤ (cut + z) * (cut - z) :=
      mul_nonneg (by linarith [hz.1]) (by linarith [hz.2])
    nlinarith
  let r : ℝ := -z / ell
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by norm_num [ell])
  have hr2 : r ^ 2 = (625 / 9 : ℝ) * z ^ 2 := by dsimp [r, ell]; ring
  have hball : z ^ 2 + r ^ 2 ≤ 1 := by nlinarith
  have heq : ell * r = -z := by dsimp [r, ell]; ring
  have hvol : volume (coneSlice z) = ENNReal.ofReal (Real.pi * r ^ 2) := by
    apply disk_squeeze hr0
    · intro u hu
      have hu' : ‖u‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hu
      have hmul : ell * ‖u‖ < ell * r := mul_lt_mul_of_pos_left hu' (by norm_num [ell])
      have hn := norm_nonneg u
      exact ⟨by linarith, by nlinarith⟩
    · intro u hu
      have hmul : ell * ‖u‖ < ell * r := by linarith [hu.1]
      have hnorm : ‖u‖ < r := -- [compile-fix]
        (mul_lt_mul_iff_of_pos_left (by norm_num [ell] : 0 < ell)).mp hmul -- [compile-fix]
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm.le
  convert hvol using 1 <;> congr 1
  dsimp [r]
  ring

private theorem outside_slice_zero {z : ℝ} (hz : z ≤ -1 ∨ 0 < z) :
    volume (coneSlice z) = 0 := by
  have hs : coneSlice z ⊆ ({0} : Set E2) := by
    intro u hu
    rcases hz with hz | hz
    · have hsq := hu.2
      have hn := norm_nonneg u
      have hn0 : ‖u‖ = 0 := by nlinarith
      exact by simpa using norm_eq_zero.mp hn0
    · have hc := hu.1
      have hn : 0 ≤ ell * ‖u‖ := mul_nonneg (by norm_num [ell]) (norm_nonneg _)
      exfalso; linarith
  exact le_antisymm ((measure_mono hs).trans (by simp)) bot_le -- [compile-fix]

private def lowerArea (z : ℝ) : ℝ := Real.pi * (1 - z ^ 2)
private def upperArea (z : ℝ) : ℝ := Real.pi * z ^ 2 / ell ^ 2

private theorem slice_as_indicators (z : ℝ) :
    volume (coneSlice z) =
      (Ioc (-1) (-cut)).indicator (fun z => ENNReal.ofReal (lowerArea z)) z +
      (Ioc (-cut) 0).indicator (fun z => ENNReal.ofReal (upperArea z)) z := by
  by_cases hlo : z ∈ Ioc (-1) (-cut)
  · have hhi : z ∉ Ioc (-cut) 0 := by intro h; exact (not_lt_of_ge hlo.2) h.1
    simp only [Set.indicator_of_mem hlo, Set.indicator_of_notMem hhi, add_zero]
    exact sphere_limited_slice ⟨hlo.1.le, hlo.2⟩
  · by_cases hhi : z ∈ Ioc (-cut) 0
    · simp only [Set.indicator_of_notMem hlo, Set.indicator_of_mem hhi, zero_add]
      exact cone_limited_slice ⟨hhi.1.le, hhi.2⟩
    · have hout : z ≤ -1 ∨ 0 < z := by
        simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hlo hhi
        rcases hlo with h | h
        · exact Or.inl h
        · rcases hhi with h' | h'
          · exfalso; linarith
          · exact Or.inr h'
      simp only [Set.indicator_of_notMem hlo, Set.indicator_of_notMem hhi, zero_add]
      exact outside_slice_zero hout

private theorem lowerArea_nonneg {z : ℝ} (hz : z ∈ Icc (-1) (-cut)) :
    0 ≤ lowerArea z := by
  have hc := cut_pos
  unfold lowerArea
  apply mul_nonneg Real.pi_pos.le
  have hp : 0 ≤ (1 + z) * (1 - z) :=
    mul_nonneg (by linarith [hz.1]) (by linarith [hz.2])
  nlinarith

private theorem upperArea_nonneg (z : ℝ) : 0 ≤ upperArea z := by
  unfold upperArea
  positivity

private theorem lower_integral :
    (∫ z in (-1 : ℝ)..(-cut), lowerArea z) =
      Real.pi * (2/3 - cut + cut ^ 3 / 3) := by
  unfold lowerArea
  rw [intervalIntegral.integral_const_mul]
  congr 1 -- [compile-fix]
  calc -- [compile-fix]
    (∫ z in (-1 : ℝ)..(-cut), 1 - z ^ 2) = -- [compile-fix]
        (∫ z in (-1 : ℝ)..(-cut), (1 : ℝ)) - -- [compile-fix]
          ∫ z in (-1 : ℝ)..(-cut), z ^ 2 := -- [compile-fix]
      intervalIntegral.integral_sub -- [compile-fix]
        (continuous_const.intervalIntegrable _ _) -- [compile-fix]
        ((continuous_id.pow 2).intervalIntegrable _ _) -- [compile-fix]
        -- API?: expected integral_sub: interval integrability of both real functions permits subtraction. -- [compile-fix]
    _ = _ := by -- [compile-fix]
      rw [intervalIntegral.integral_const, integral_pow] -- [compile-fix]
        -- API?: integral_pow (n : Nat) is a ROOT theorem, with value (b^(n+1)-a^(n+1))/(n+1). -- [compile-fix]
      norm_num -- [compile-fix]
      ring -- [compile-fix]

private theorem upper_integral :
    (∫ z in (-cut)..(0 : ℝ), upperArea z) =
      Real.pi * (625 / 9) * cut ^ 3 / 3 := by
  unfold upperArea ell
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    -- API?: expected integral_div f c = integral(f) / c, with no sign restriction.
  norm_num
  ring

private theorem integral_sum :
    (∫ z in (-1 : ℝ)..(-cut), lowerArea z) +
      (∫ z in (-cut)..(0 : ℝ), upperArea z) =
      (2 * Real.pi / 3) * (1 - cut) := by
  have hc3 : cut ^ 3 = (9 / 634 : ℝ) * cut := by
    calc
      cut ^ 3 = cut ^ 2 * cut := by ring
      _ = _ := by rw [cut_sq]
  rw [lower_integral, upper_integral, hc3]
  ring

private theorem interval_ofReal (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : Continuous f) (hnn : ∀ z ∈ Icc a b, 0 ≤ f z) :
    (∫⁻ z in Ioc a b, ENNReal.ofReal (f z)) =
      ENNReal.ofReal (∫ z in a..b, f z) := by
  have hi : IntegrableOn f (Ioc a b) := (hf.intervalIntegrable a b).1
  have hn : 0 ≤ᵐ[volume.restrict (Ioc a b)] f := by
    apply (ae_restrict_iff' measurableSet_Ioc).2
      -- API?: expected ae_restrict_iff': a.e. on a measurable restriction iff a.e. implications on the original space.
    exact Filter.Eventually.of_forall (fun z hz => hnn z ⟨hz.1.le, hz.2⟩)
  rw [intervalIntegral.integral_of_le hab]
  exact (ofReal_integral_eq_lintegral_ofReal hi hn).symm
    -- API?: expected ofReal_integral_eq_lintegral_ofReal h_integrable h_nonneg_ae.

private theorem lower_integral_nonneg :
    0 ≤ ∫ z in (-1 : ℝ)..(-cut), lowerArea z := by
  rw [intervalIntegral.integral_of_le (by linarith [cut_lt_one])]
  apply integral_nonneg_of_ae
  apply (ae_restrict_iff' measurableSet_Ioc).2
    -- API?: same restriction equivalence as interval_ofReal above.
  exact Filter.Eventually.of_forall fun z hz => lowerArea_nonneg ⟨hz.1.le, hz.2⟩

private theorem upper_integral_nonneg :
    0 ≤ ∫ z in (-cut)..(0 : ℝ), upperArea z := by
  rw [intervalIntegral.integral_of_le (by linarith [cut_pos])]
  exact integral_nonneg (fun z => upperArea_nonneg z)

/-- The full measure calculation, including Tonelli, circle-boundary
squeezing and the explicit polynomial integrals. -/
private theorem native_cone_ball_volume :
    volume (circularCone ell ∩ Metric.closedBall (0 : E3) 1) =
      ENNReal.ofReal ((2 * Real.pi / 3) * (1 - cut)) := by
  rw [cone_volume_by_slices]
  have hfun : (fun z : ℝ => volume (coneSlice z)) =
      fun z => (Ioc (-1) (-cut)).indicator (fun z => ENNReal.ofReal (lowerArea z)) z +
        (Ioc (-cut) 0).indicator (fun z => ENNReal.ofReal (upperArea z)) z :=
    funext slice_as_indicators
  rw [hfun]
  have hlc : Continuous lowerArea := by unfold lowerArea; fun_prop
  have huc : Continuous upperArea := by unfold upperArea; fun_prop
  have hlm : Measurable
      ((Ioc (-1) (-cut)).indicator (fun z => ENNReal.ofReal (lowerArea z))) := by
    exact (ENNReal.measurable_ofReal.comp hlc.measurable).indicator measurableSet_Ioc
      -- API?: expected measurable_ofReal and Measurable.indicator for measurable interval supports.
  rw [lintegral_add_left hlm, lintegral_indicator measurableSet_Ioc,
    lintegral_indicator measurableSet_Ioc]
    -- API?: expected lintegral_add_left hf g and lintegral_indicator hs.
  rw [interval_ofReal lowerArea (-1) (-cut) (by linarith [cut_lt_one]) hlc
      (fun z hz => lowerArea_nonneg hz),
    interval_ofReal upperArea (-cut) 0 (by linarith [cut_pos]) huc
      (fun z _ => upperArea_nonneg z)]
  rw [← ENNReal.ofReal_add lower_integral_nonneg upper_integral_nonneg, integral_sum]
    -- API?: expected ofReal_add ha hb: ofReal(a+b)=ofReal a+ofReal b for nonnegative a,b.

/-- Exact frozen field proposition. In particular the endpoint contains no
new geometric or measure premise. -/
theorem circular_cone_solid_angle_holds : R44ConeSolidAngleFormula := by
  change 3 * volume (circularCone ell ∩ Metric.closedBall (0 : E3) 1) =
    ENNReal.ofReal (coneAngle ell)
  rw [native_cone_ball_volume]
  have hthree : (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [hthree, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  unfold coneAngle cut
  ring

end
end R44
