/- -- [compile-fix: promoted to Proved after exchange 7]
# Exact transport of the frozen radial tangent cone

A-L2.2/A-L3.2. Affine isometries transport the actual radial definition;
the following volume transport uses the already proved orthogonal
invariance theorem. No registration, edge direction, or dihedral premise.
-/
import R44.Proved.WedgeVolume -- [compile-fix: promoted after exchange 7]
import R44.Proved.PolyhedralConeMeasure -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeTangentTransport
open Set DischargeWedge DischargeConeMeasure
noncomputable section

 theorem radial_image (g : RigidMotion) (S : Set E3) (x : E3) :
    tangentCone (g '' S) (g x)=g.linearIsometryEquiv '' tangentCone S x := by
  have ray (v : E3) (t : ℝ) :
      g (x+t • v)=g x+t • g.linearIsometryEquiv v := by
    simpa [vadd_eq_add, add_comm] using g.map_vadd x (t • v) -- [compile-fix]
    -- API?: map_vadd and the linear map's map_smul; argument order follows
    -- the existing NativeGeometry/FeatureLocalCharts usage.
  ext v
  constructor
  · rintro ⟨eps,heps,hv⟩
    refine ⟨g.linearIsometryEquiv.symm v,⟨eps,heps,?_⟩,by simp⟩
    intro t ht hte
    obtain ⟨y,hy,he⟩ := hv t ht hte
    have he' : g (x+t • g.linearIsometryEquiv.symm v)=g y := by
      rw [ray]; simpa using he.symm
    exact g.injective he' ▸ hy
  · rintro ⟨w,⟨eps,heps,hw⟩,rfl⟩
    exact ⟨eps,heps,fun t ht hte =>
      ⟨x+t • w,hw t ht hte,ray w t⟩⟩

 theorem solidAngle_placed (g : RigidMotion) (x : E3) :
    solidAngle (tangentCone (g '' Q) x)=solidAngle (tangentCone Q (g.symm x)) := by
  have he : x=g (g.symm x) := (g.apply_symm_apply x).symm
  conv_lhs => rw [he,radial_image]
  apply solidAngle_orthogonal
  simpa using (placed_tangent_measurable_null_frontier (1:RigidMotion) (g.symm x)).1

end
end R44.DischargeTangentTransport
