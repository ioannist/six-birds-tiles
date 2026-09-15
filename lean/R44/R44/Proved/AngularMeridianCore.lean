/- -- [compile-fix: promoted to Proved after exchange 7]
# Frozen angular/measure records (definition-only relocation)

The five declarations below are copied byte-for-byte from exchange 6's
NativeDihedralSectors.lean. Relocation breaks the import cycle between the
native interpretation and its records; no proposition, definition, measure
normalization or universe is changed. Sources: A-L2.2/A-L3.1.
-/
import R44.Proved.PlanarSectorArea -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeMeridian
open Set R44.DischargeWedge R44.DischargePlanar
noncomputable section

structure Meridian (C:Set E3) (theta:ℝ) where
  axes : E3 ≃ₗᵢ[ℝ] E3
  sector : Set E2
  measurable : MeasurableSet sector
  nonnegative : 0≤theta
  cone_eq : C=axes '' prism sector
  disk_law : SectorDiskLaw sector theta

def MeshAngleValue (c:Nat×Nat×Int) (theta:ℝ) : Prop :=
  if c.1=0 then theta=Real.pi+Real.arctan ((c.2.1:ℝ)/100) ∨
      theta=Real.pi-Real.arctan ((c.2.1:ℝ)/100)
  else if c.1=1 then theta=Real.pi+Real.arccos (1/(1+((c.2.1:ℝ)/100)^2)) ∨
      theta=Real.pi-Real.arccos (1/(1+((c.2.1:ℝ)/100)^2))
  else if c.1=2 then theta=Real.pi
  else theta=Real.pi/2 ∨ theta=3*Real.pi/2

/-- Pure geometric normal form. It has NO area or solid-angle field. -/
structure AngularMeridian (C : Set E3) (theta : ℝ) where
  axes : E3 ≃ₗᵢ[ℝ] E3
  lower : 0≤theta
  upper : theta<2*Real.pi
  set_eq : C=axes '' prism (angularSector theta)

def AngularMeridian.measured {C : Set E3} {theta : ℝ}
    (m : AngularMeridian C theta) : Meridian C theta where
  axes := m.axes
  sector := angularSector theta
  measurable := angularSector_measurable theta
  nonnegative := m.lower
  cone_eq := m.set_eq
  disk_law := angular_sector_disk_law theta m.lower m.upper

/-- Unchanged consequence of the existing ACTUAL 3D volume theorem. -/
theorem Meridian.solidAngle {C:Set E3} {theta:ℝ} (m:Meridian C theta) :
    solidAngle C=ENNReal.ofReal (2*theta) := by
  rw [m.cone_eq]
  exact orthogonal_prism_solidAngle m.axes m.measurable m.nonnegative m.disk_law

end
end R44.DischargeMeridian
