/- -- [compile-fix: promoted to Proved after exchange 7]
# Actual area of a planar angular sector

A-L2.2/A-L3.1, proof/ALIGNMENT_PROOF.md. This file supplies the missing
TWO-dimensional polar-coordinate integral, with Mathlib's Lebesgue volume.
Together with WedgeVolume it yields the ACTUAL 3D wedge volume 2θ/3.
Neither solidAngle nor the frozen tangent cone is redefined.

The sector is centered on the positive real axis; an arbitrary meridian
is represented by an orthogonal change of axes. Its aperture lies in
[0,2π), which includes every R44 flat, carrier, base, and ridge angle.
The angle interval stays strictly inside the polar branch cut. The origin
has measure zero and is included by arg(0)=0. No mathematical admissions.

API note: the polar-coordinate theorem names were checked against the
public Mathlib documentation, NOT a locally available copy of the pinned
revision. Revision-sensitive calls are marked where used.
-/
import R44.Proved.WedgeVolume -- [compile-fix: promoted after exchange 7]
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace R44.DischargePlanar
open Set MeasureTheory Complex R44.DischargeWedge
open scoped ENNReal Interval
noncomputable section
set_option maxHeartbeats 0

/-- The coordinate identification, with the Euclidean area normalization. -/
def complexCoordinates : E2 ≃ᵐ ℂ :=
  ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm).trans
    Complex.measurableEquivPi.symm

@[simp] theorem complexCoordinates_apply (x : E2) :
    complexCoordinates x=(x 0 : ℂ)+(x 1 : ℂ)*Complex.I := by
  simp [complexCoordinates]

 theorem complexCoordinates_norm (x : E2) : ‖complexCoordinates x‖=‖x‖ := by
  have he : ‖complexCoordinates x‖^2=‖x‖^2 := by
    rw [Complex.sq_norm]
    simp [complexCoordinates_apply,Complex.normSq_apply,EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs]
      -- API?: Complex.sq_norm / Complex.normSq_apply express |z|²=re²+im².
    ring -- [compile-fix]
  nlinarith [norm_nonneg (complexCoordinates x),norm_nonneg x]

 theorem complexCoordinates_preserves :
    MeasurePreserving complexCoordinates volume volume := by
  have hE := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)
  have hC := MeasurePreserving.symm Complex.measurableEquivPi
    Complex.volume_preserving_equiv_pi
  exact hC.comp hE

/-- A closed angular sector; no restriction on radius is built in. -/
def complexSector (theta : ℝ) : Set ℂ :=
  {z | -(theta/2)≤z.arg ∧ z.arg≤theta/2}

def angularSector (theta : ℝ) : Set E2 :=
  complexCoordinates ⁻¹' complexSector theta

 theorem complexSector_measurable (theta : ℝ) : MeasurableSet (complexSector theta) := by
  exact (measurableSet_le measurable_const Complex.measurable_arg).inter
    (measurableSet_le Complex.measurable_arg measurable_const) -- [compile-fix]
    -- API?: Complex.measurable_arg : Measurable Complex.arg.

 theorem angularSector_measurable (theta : ℝ) : MeasurableSet (angularSector theta) :=
  (complexSector_measurable theta).preimage complexCoordinates.measurable

private theorem radial_integral (R : ℝ) (hR : 0≤R) :
    (∫⁻r:ℝ in Ioc 0 R,ENNReal.ofReal r)=ENNReal.ofReal (R^2/2) := by
  have hint : IntegrableOn (fun r : ℝ => r) (Ioc 0 R) :=
    (continuous_id.intervalIntegrable 0 R).1
  have hn : 0≤ᵐ[volume.restrict (Ioc 0 R)] (fun r : ℝ => r) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact Filter.Eventually.of_forall fun r hr => hr.1.le
  rw [←ofReal_integral_eq_lintegral_ofReal hint hn,
    ←intervalIntegral.integral_of_le hR]
  congr 1
  rw [integral_id]
  ring
  -- API?: integral_id is ∫x in a..b,x=(b²-a²)/2.

private theorem rectangle_integral (theta R : ℝ) (ht : 0≤theta) (hR : 0≤R) :
    (∫⁻p : ℝ×ℝ in (Ioc 0 R)×ˢ(Icc (-(theta/2)) (theta/2)),
      ENNReal.ofReal p.1)=ENNReal.ofReal (theta*R^2/2) := by
  change (∫⁻p : ℝ×ℝ in (Ioc 0 R)×ˢ(Icc (-(theta/2)) (theta/2)),
    ENNReal.ofReal p.1 ∂((volume : Measure ℝ).prod volume))=_ -- [compile-fix]
  rw [setLIntegral_prod _ (by fun_prop)] -- [compile-fix]
    -- API?: lintegral_prod for a measurable nonnegative function and product measures.
  simp only [lintegral_const,Measure.restrict_apply_univ]
  have hlen : volume (Icc (-(theta/2)) (theta/2))=ENNReal.ofReal theta := by
    rw [Real.volume_Icc]
    congr 1; ring
  rw [hlen,lintegral_mul_const _ ENNReal.measurable_ofReal,
    radial_integral R hR] -- [compile-fix]
    -- API?: lintegral_mul_const; measurability is available by fun_prop.
  rw [←ENNReal.ofReal_mul (by positivity : 0≤R^2/2)]
  congr 1; ring

/-- Evaluate the integral on the polar target. Radial and angular boundaries
are retained; there is no boundary-null premise hidden in the theorem. -/
theorem complex_sector_disk_area (theta : ℝ) (ht : 0≤theta)
    (hlt : theta<2*Real.pi) (R : ℝ) (hR : 0≤R) :
    volume (complexSector theta∩Metric.closedBall (0:ℂ) R)=
      ENNReal.ofReal (theta*R^2/2) := by
  classical
  let S := complexSector theta∩Metric.closedBall (0:ℂ) R
  let D := (Ioc (0:ℝ) R)×ˢ(Icc (-(theta/2)) (theta/2))
  let f : ℂ → ENNReal := S.indicator (fun _ => 1)
  have hS : MeasurableSet S :=
    (complexSector_measurable theta).inter measurableSet_closedBall
  have hD : MeasurableSet D := measurableSet_Ioc.prod measurableSet_Icc
  have hsub : D⊆Complex.polarCoord.target := by
    rintro ⟨r,a⟩ ⟨hr,ha⟩
    rw [Complex.polarCoord_target]
    refine ⟨hr.1,?_,?_⟩ <;> linarith [ha.1,ha.2]
  have har (p : ℝ×ℝ) (hp : p∈Complex.polarCoord.target) :
      (Complex.polarCoord.symm p).arg=p.2 := by
    have he := Complex.polarCoord.right_inv hp
    have he' := congrArg Prod.snd he
    simpa [Complex.polarCoord_apply] using he'
  have hnorm (p : ℝ×ℝ) (hp : p∈Complex.polarCoord.target) :
      ‖Complex.polarCoord.symm p‖=p.1 := by
    rw [Complex.norm_polarCoord_symm,abs_of_pos]
    have hh : 0<p.1 ∧ -Real.pi<p.2 ∧ p.2<Real.pi := by
      simpa only [Complex.polarCoord_target,Set.mem_prod,Set.mem_Ioi,Set.mem_Ioo] using hp
    exact hh.1
  have heq (p : ℝ×ℝ) (hp : p∈Complex.polarCoord.target) :
      ENNReal.ofReal p.1 * f (Complex.polarCoord.symm p)=
        D.indicator (fun q : ℝ×ℝ => ENNReal.ofReal q.1) p := by
    have hrad : 0<p.1 := by
      have hh : 0<p.1 ∧ -Real.pi<p.2 ∧ p.2<Real.pi := by
        simpa only [Complex.polarCoord_target,Set.mem_prod,Set.mem_Ioi,Set.mem_Ioo] using hp
      exact hh.1
    have hm : Complex.polarCoord.symm p∈S ↔ p∈D := by
      simp only [S,complexSector,Set.mem_inter_iff,Set.mem_setOf_eq,
        Metric.mem_closedBall,dist_zero_right,har p hp,hnorm p hp,
        D,Set.mem_prod,Set.mem_Ioc,Set.mem_Icc]
      tauto
    by_cases hd : p∈D
    · rw [show f (Complex.polarCoord.symm p)=1 by
          exact Set.indicator_of_mem (hm.mpr hd) _]
      rw [Set.indicator_of_mem hd]
      simp -- [compile-fix]
    · rw [show f (Complex.polarCoord.symm p)=0 by
          exact Set.indicator_of_notMem (fun hs => hd (hm.mp hs)) _]
      rw [Set.indicator_of_notMem hd]
      simp -- [compile-fix]
  have hcv := Complex.lintegral_comp_polarCoord_symm f
    -- API?: checked public signature: ∫⁻p in polar target,ofReal(p.1) •
    -- f(polar.symm p)=∫⁻z,f z. `•` is ENNReal multiplication here.
  change (∫⁻p in Complex.polarCoord.target,
    ENNReal.ofReal p.1*f (Complex.polarCoord.symm p))=∫⁻z,f z at hcv
  have hleft : (∫⁻p in Complex.polarCoord.target,
      ENNReal.ofReal p.1*f (Complex.polarCoord.symm p))=
      ∫⁻p in D,ENNReal.ofReal p.1 := by
    calc
      _ = ∫⁻p in Complex.polarCoord.target,
          D.indicator (fun q : ℝ×ℝ => ENNReal.ofReal q.1) p := by
        apply lintegral_congr_ae
        have htarg : MeasurableSet Complex.polarCoord.target := by
          rw [Complex.polarCoord_target]
          exact measurableSet_Ioi.prod measurableSet_Ioo
        apply (ae_restrict_iff' htarg).mpr
        exact Filter.Eventually.of_forall fun p hp => heq p hp
      _ = ∫⁻p in D,ENNReal.ofReal p.1 := by
        rw [lintegral_indicator hD,Measure.restrict_restrict hD,
          Set.inter_eq_left.mpr hsub]
  have hright : (∫⁻z,f z)=volume S := by simp [f,lintegral_indicator hS]
  rw [hleft,hright] at hcv
  rw [←hcv]
  exact rectangle_integral theta R ht hR

/-- The exact SectorDiskLaw consumed by WedgeVolume. -/
theorem angular_sector_disk_law (theta : ℝ) (ht : 0≤theta)
    (hlt : theta<2*Real.pi) : SectorDiskLaw (angularSector theta) theta := by
  intro R hR
  have he : angularSector theta∩Metric.closedBall (0:E2) R=
      complexCoordinates ⁻¹' (complexSector theta∩Metric.closedBall (0:ℂ) R) := by
    ext x
    simp only [angularSector,Set.mem_inter_iff,Set.mem_preimage,
      Metric.mem_closedBall,dist_zero_right]
    rw [complexCoordinates_norm] -- [compile-fix]
  rw [he,complexCoordinates_preserves.measure_preimage
    ((complexSector_measurable theta).inter measurableSet_closedBall).nullMeasurableSet]
  exact complex_sector_disk_area theta ht hlt R hR

end
end R44.DischargePlanar
