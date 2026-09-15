/- -- [compile-fix: promoted to Proved after exchange 7]
# The actual three-dimensional wedge volume from planar sector sections

Sources: A-L2.2 and A-L3.1, proof/ALIGNMENT_PROOF.md. This completes the
Cavalieri step for an arbitrary measurable planar angular sector W: once its
disk area is theta*r^2/2, the PRISM over W cuts unit-ball volume 2*theta/3.
Orthogonal transport is also proved for the frozen volume-based solidAngle.

-- [compile-fix begin: exchange 7 closed the former mesh bridge]
This lemma does not silently claim a polar sector-area theorem. Exchange 7
proves the oriented sectors, planar disk law, and complete mesh-edge chart
interpretation. The exact normalizations are those of ambient Lebesgue volume.
-- [compile-fix end]
-/
import R44.LogicalSpineFoundation -- [compile-fix: break promotion cycle; all used frozen definitions live in the foundation]

namespace R44.DischargeWedge
open Set MeasureTheory
open scoped ENNReal Interval
noncomputable section
set_option maxHeartbeats 0

abbrev E2 := EuclideanSpace ℝ (Fin 2)

def axisSplit : E3 ≃ᵐ (ℝ × E2) :=
  (((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))
    -- API?: expected measurable equivalence: piFinSuccAbove splits coordinate i and its complement; prodCongr acts on each product factor.

theorem axisSplit_fst (x : E3) : (axisSplit x).1 = x 2 := by
  rfl

theorem axisSplit_snd (x : E3) (i : Fin 2) :
    (axisSplit x).2 i = x i.castSucc := by
  fin_cases i <;> rfl

theorem axisSplit_preserves : MeasurePreserving axisSplit volume volume := by
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


/-- The wedge axis is coordinate 2; W is its actual planar section. -/
def prism (W:Set E2) : Set E3 := {x | (axisSplit x).2∈W}

def «section» (W:Set E2) (z:ℝ) : Set E2 := -- [compile-fix]
  {u | u∈W ∧ z^2+‖u‖^2≤1}

private theorem split_norm_sq (x:E3) :
    ‖x‖^2=x 2^2+‖(axisSplit x).2‖^2 := by
  simp [EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,axisSplit_snd,
    Real.norm_eq_abs,sq_abs]
  ring

theorem prism_measurable {W:Set E2} (hW:MeasurableSet W) : MeasurableSet (prism W) :=
  hW.preimage (measurable_snd.comp axisSplit.measurable)

/-- Tonelli uses the product Euclidean volume normalization, not a
new angle-dependent measure. -/
theorem prism_volume_by_slices {W:Set E2} (hW:MeasurableSet W) :
    volume (prism W∩Metric.closedBall (0:E3) 1)=
      ∫⁻z:ℝ,volume («section» W z) := by -- [compile-fix]
  let S : Set (ℝ×E2) := {p | p.2∈W ∧ p.1^2+‖p.2‖^2≤1}
  have hS : MeasurableSet S :=
    (hW.preimage measurable_snd).inter
      (isClosed_le ((continuous_fst.pow 2).add (continuous_snd.norm.pow 2))
        continuous_const).measurableSet
  have hp : axisSplit ⁻¹' S=prism W∩Metric.closedBall (0:E3) 1 := by
    ext x
    simp only [S,prism,Set.mem_preimage,Set.mem_setOf_eq,Set.mem_inter_iff,
      Metric.mem_closedBall,dist_zero_right,axisSplit_fst]
    rw [←split_norm_sq]
    constructor
    · rintro ⟨hw,hb⟩
      exact ⟨hw,by nlinarith [norm_nonneg x]⟩
    · rintro ⟨hw,hb⟩
      exact ⟨hw,by nlinarith [norm_nonneg x]⟩
  rw [←hp,axisSplit_preserves.measure_preimage hS.nullMeasurableSet,
    Measure.volume_eq_prod,Measure.prod_apply hS]
  rfl

/-- The only two-dimensional geometric input to the volume lemma. It is
ordinary area of W cut by a closed disk, for every nonnegative radius. -/
def SectorDiskLaw (W:Set E2) (theta:ℝ) : Prop :=
  ∀r:ℝ,0≤r → volume (W∩Metric.closedBall (0:E2) r)=
    ENNReal.ofReal (theta*r^2/2)

private theorem section_inside {W:Set E2} {z:ℝ} (hz:-1≤z ∧ z≤1) :
    «section» W z=W∩Metric.closedBall (0:E2) (Real.sqrt (1-z^2)) := by -- [compile-fix]
  have hnonneg : 0≤1-z^2 := by nlinarith [sq_nonneg z]
  ext u
  simp only [«section»,Set.mem_setOf_eq,Set.mem_inter_iff, -- [compile-fix]
    Metric.mem_closedBall,dist_zero_right]
  constructor
  · rintro ⟨hu,hb⟩
    refine ⟨hu,?_⟩
    nlinarith [norm_nonneg u,Real.sqrt_nonneg (1-z^2),Real.sq_sqrt hnonneg]
  · rintro ⟨hu,hb⟩
    refine ⟨hu,?_⟩
    nlinarith [norm_nonneg u,Real.sqrt_nonneg (1-z^2),Real.sq_sqrt hnonneg]

private theorem section_outside {W:Set E2} {z:ℝ} (hz:z< -1 ∨ 1<z) :
    «section» W z=∅ := by -- [compile-fix]
  ext u
  simp only [«section»,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false] -- [compile-fix]
  rintro ⟨_,h⟩
  rcases hz with hz|hz <;> nlinarith [sq_nonneg ‖u‖]

private theorem slice_indicator {W:Set E2} {theta:ℝ} (hW:SectorDiskLaw W theta)
    (z:ℝ) :
    volume («section» W z)= -- [compile-fix]
      (Ioc (-1:ℝ) 1).indicator (fun z => ENNReal.ofReal (theta*(1-z^2)/2)) z := by
  by_cases hi : z∈Ioc (-1:ℝ) 1
  · have hn : 0 ≤ 1-z^2 := by nlinarith [hi.1,hi.2] -- [compile-fix begin: supply sqrt side condition explicitly]
    rw [Set.indicator_of_mem hi,section_inside ⟨hi.1.le,hi.2⟩,
      hW _ (Real.sqrt_nonneg _),Real.sq_sqrt hn] -- [compile-fix end]
  · rw [Set.indicator_of_notMem hi] -- [compile-fix]
    by_cases hz : z= -1
    · subst z
      rw [section_inside (by norm_num),show (1-(-1:ℝ)^2)=0 by norm_num,
        Real.sqrt_zero,hW 0 (by norm_num)]
      simp
    · have hout : z< -1 ∨ 1<z := by
        simp only [Set.mem_Ioc,not_and_or,not_lt,not_le] at hi
        rcases hi with hi|hi
        · exact Or.inl (lt_of_le_of_ne hi hz)
        · exact Or.inr hi
      rw [section_outside hout,measure_empty]

private theorem polynomial_integral (theta:ℝ) :
    (∫z in (-1:ℝ)..1,theta*(1-z^2)/2)=2*theta/3 := by
  rw [intervalIntegral.integral_div,intervalIntegral.integral_const_mul]
  have hi : (∫z in (-1:ℝ)..1,1-z^2)=4/3 := by -- [compile-fix begin: make the integrand functions explicit for Lean 4.31]
    calc
      (∫z in (-1:ℝ)..1,1-z^2) =
          (∫z in (-1:ℝ)..1,(1:ℝ)) - ∫z in (-1:ℝ)..1,z^2 :=
        intervalIntegral.integral_sub
          (continuous_const.intervalIntegrable (-1:ℝ) 1)
          ((continuous_id.pow 2).intervalIntegrable (-1:ℝ) 1)
      _ = 4/3 := by
        rw [intervalIntegral.integral_const,integral_pow 2]
        norm_num -- [compile-fix end]
  rw [hi]
  ring

/-- Actual 3D Lebesgue-volume result, with no convention substituted for it. -/
theorem prism_ball_volume {W:Set E2} (hW:MeasurableSet W)
    {theta:ℝ} (htheta:0≤theta) (hdisk:SectorDiskLaw W theta) :
    volume (prism W∩Metric.closedBall (0:E3) 1)=ENNReal.ofReal (2*theta/3) := by
  rw [prism_volume_by_slices hW]
  simp_rw [slice_indicator hdisk]
  rw [lintegral_indicator measurableSet_Ioc]
  let f : ℝ→ℝ := fun z => theta*(1-z^2)/2
  have hf : Continuous f := by fun_prop
  have hint : IntegrableOn f (Ioc (-1:ℝ) 1) := (hf.intervalIntegrable _ _).1
  have hn : 0≤ᵐ[volume.restrict (Ioc (-1:ℝ) 1)] f := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact Filter.Eventually.of_forall fun z hz =>
      div_nonneg (mul_nonneg htheta (by nlinarith [hz.1,hz.2])) (by norm_num)
  rw [←ofReal_integral_eq_lintegral_ofReal hint hn,
    ←intervalIntegral.integral_of_le (by norm_num : (-1:ℝ)≤1)]
  exact congrArg ENNReal.ofReal (polynomial_integral theta)

/-- Orthogonal images preserve the FROZEN solid-angle definition for every
measurable cone, not only for the circular cone used in A-L4.1. -/
theorem solidAngle_orthogonal (A:E3 ≃ₗᵢ[ℝ] E3) {C:Set E3} (hC:MeasurableSet C) :
    solidAngle (A '' C)=solidAngle C := by
  unfold solidAngle
  congr 1
  have he : A '' (C∩Metric.closedBall (0:E3) 1)=
      A '' C∩Metric.closedBall (0:E3) 1 := by
    rw [Set.image_inter A.injective,A.image_closedBall]
    simp
  rw [←he] -- [compile-fix begin: expose the linear-isometry coercion before preimage transport]
  change volume (A '' (C ∩ Metric.closedBall (0:E3) 1)) = _
  rw [A.image_eq_preimage_symm] -- [compile-fix end]
  exact A.symm.measurePreserving.measure_preimage
    (hC.inter measurableSet_closedBall).nullMeasurableSet

/-- The value HasFeatureDihedral needs after identifying its meridian sector. -/
theorem orthogonal_prism_solidAngle (A:E3 ≃ₗᵢ[ℝ] E3)
    {W:Set E2} (hW:MeasurableSet W) {theta:ℝ}
    (htheta:0≤theta) (hdisk:SectorDiskLaw W theta) :
    solidAngle (A '' prism W)=ENNReal.ofReal (2*theta) := by
  rw [solidAngle_orthogonal A (prism_measurable hW),solidAngle,
    prism_ball_volume hW htheta hdisk]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, -- [compile-fix]
    ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)] -- [compile-fix]
  congr 1
  ring

end
end R44.DischargeWedge
