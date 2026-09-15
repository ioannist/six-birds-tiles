/- -- [compile-fix: promoted to Proved after exchange 7]
# Every native open base/ridge point has the correct oriented meridian

A-L3.1 / A-L2.2, proof/ALIGNMENT_PROOF.md. This interprets the ACTUAL native
edge sets, not just a representative midpoint. Four square symmetries cover
all base edges. The ridge coordinates follow the genuinely slanted edge.
The principal inverse-trigonometric identities and the nonconvex cases are
proved in ElementarySectorGeometry. Mesh-subdivision edges are separate.
No mathematical admissions; no tiling hypothesis or complete-dihedral
hypothesis is used.
-/
import R44.Proved.AngularMeridianCore -- [compile-fix: promoted after exchange 7]
import R44.Proved.ElementarySectorGeometry -- [compile-fix: promoted after exchange 7]
import R44.Proved.TangentIsometry -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeMeridian
open Set DischargePyramid DischargeCharts DischargeGeometry
open DischargeTentCones DischargeMeridianFrames DischargeAngular
open DischargePlanar DischargeWedge DischargeTangentTransport
noncomputable section
set_option maxHeartbeats 0

/-- Orthogonal transport of a geometric (unmeasured) meridian. -/
def AngularMeridian.map {C : Set E3} {theta : ℝ}
    (m : AngularMeridian C theta) (A : E3 ≃ₗᵢ[ℝ] E3) :
    AngularMeridian (A '' C) theta where
  axes := A*m.axes
  lower := m.lower
  upper := m.upper
  set_eq := by -- [compile-fix: dependent rewrite replaced by congruence]
    calc
      A '' C = A '' (m.axes '' prism (angularSector theta)) :=
        congrArg (fun S : Set E3 => A '' S) m.set_eq
      _ = (A * m.axes) '' prism (angularSector theta) := by
        rw [Set.image_image]
        rfl

-- [compile-fix begin: normalize the signed base angle in the current cast API]
private theorem base_angle_signed (r : Role) :
    Real.pi+Real.arctan ((((profileCoefficient r : ℝ)/10000)/eta))=
      featureInteriorAngle r .base := by
  have habs : ((profileCoefficient r).natAbs : ℝ)=|(profileCoefficient r : ℝ)| := by
    -- [compile-fix: cast the integer identity explicitly for the current API]
    have h := congrArg (fun q : ℤ => (q : ℝ))
      (Int.natCast_natAbs (profileCoefficient r))
    simpa [Int.cast_abs] using h
  by_cases h : 0<profileCoefficient r
  · have hr : (0:ℝ)<(profileCoefficient r : ℝ) := by exact_mod_cast h
    have harg : (((profileCoefficient r : ℝ)/10000)/eta) =
        featureSlope r := by
      rw [featureSlope, habs, abs_of_pos hr]
      norm_num [eta]
      ring
    rw [harg]
    simp [featureInteriorAngle, h]
  · have hr : (profileCoefficient r : ℝ)≤0 := by exact_mod_cast (le_of_not_gt h)
    have harg : (((profileCoefficient r : ℝ)/10000)/eta) =
        -featureSlope r := by
      rw [featureSlope, habs, abs_of_nonpos hr]
      norm_num [eta]
      ring
    rw [harg, Real.arctan_neg]
    simp [featureInteriorAngle, h]
    ring -- [compile-fix: normalize additive negation]
-- [compile-fix end]

private theorem ridge_angle_signed (r : Role) :
    Real.pi-2*Real.arctan
      ((((profileCoefficient r : ℝ)/10000)/eta)/
        Real.sqrt (2+(((profileCoefficient r : ℝ)/10000)/eta)^2))=
      featureInteriorAngle r .ridge := by
  let a := (profileCoefficient r : ℝ)/10000
  let t := a/eta
  have hn : t≠0 := by
    dsimp [t,a]; apply div_ne_zero
    · apply div_ne_zero
      · exact_mod_cast (coefficient_bounds profile_canonical r).1
      · norm_num
    · norm_num [eta]
  have hid := ridge_principal t hn
  have ht : t=(profileCoefficient r : ℝ)/100 := by dsimp [t,a]; norm_num [eta]; ring
  have habs : ((profileCoefficient r).natAbs : ℝ)=|(profileCoefficient r : ℝ)| := by
    -- [compile-fix: cast the integer identity explicitly for the current API]
    have h := congrArg (fun q : ℤ => (q : ℝ))
      (Int.natCast_natAbs (profileCoefficient r))
    simpa [Int.cast_abs] using h
  have hsq : t^2=(featureSlope r)^2 := by
    rw [ht]; simp [featureSlope,habs,div_pow,sq_abs]
  have hpos : (0<t) ↔ 0<profileCoefficient r := by rw [ht]; norm_num
  change Real.pi-2*Real.arctan (t/Real.sqrt (2+t^2))=_
  rw [hid,hsq]
  unfold featureInteriorAngle
  split_ifs <;> simp_all [hpos] <;> ring

/-- Canonical base cone, with actual oriented aperture pi+atan(a/eta). -/
def canonical_base_meridian (a : ℝ) : -- [compile-fix: structure-valued declaration]
    AngularMeridian (baseCone a) (Real.pi+Real.arctan (a/eta)) := by
  obtain ⟨hl,hu,he⟩ := base_section_angular a
  refine ⟨baseAxes*(turn (Real.arctan (a/eta)/2)*turn (-Real.pi/2)),hl.le,hu,?_⟩
  rw [base_meridian,he,Set.image_image]
  rfl

/-- Canonical ridge cone; no principal-angle sign is suppressed. -/
def canonical_ridge_meridian (a sx sy : ℝ) -- [compile-fix: structure-valued declaration]
    (hx : sx=1 ∨ sx= -1) (hy : sy=1 ∨ sy= -1) :
    AngularMeridian (ridgeCone a sx sy)
      (Real.pi-2*Real.arctan ((a/eta)/Real.sqrt (2+(a/eta)^2))) := by
  obtain ⟨hl,hu,he⟩ := lowerV_angular ((a/eta)/Real.sqrt (2+(a/eta)^2))
  refine ⟨ridgeAxes a sx sy hx hy*turn (-Real.pi/2),hl.le,hu,?_⟩
  rw [ridge_meridian a sx sy hx hy]
  have hsec : prism (ridgeSection a)=
      {w:E3 | w 1≤-((a/eta)/Real.sqrt (2+(a/eta)^2))*|w 0|} := by
    ext w; rfl
  rw [hsec,he,Set.image_image]
  rfl

/-- The globally continued signed hypograph is the affine image of the
canonical tent hypograph. It is not the image of a truncated feature patch. -/
theorem chart_hypograph (r : Role) :
    chartPose r '' H ((profileCoefficient r : ℝ)/10000)=signedHypograph r := by
  have test (w : E3) : chartPose r w∈signedHypograph r ↔
      w∈H ((profileCoefficient r : ℝ)/10000) := by
    have hc := chart_coordinates r (w 0) (w 1) (w 2)
    have he : chartPose r w=chartPoint r (w 0) (w 1) (w 2) := by
      simp [chartPose_apply,chartEquiv_apply,chartLinear_apply,chartPoint]
      module
    rw [he]
    change featureNormalCoordinate r _≤featureHeight r _ ↔ _
    rw [hc.2.2]
    -- [compile-fix: rewrite coordinate equalities in their elaborated direction]
    simp only [featureHeight, featureRadius]
    change w 2 ≤ (profileCoefficient r : ℝ) / 10000 *
        max 0 (1 - max |chartU r (chartPoint r (w 0) (w 1) (w 2))|
          |chartV r (chartPoint r (w 0) (w 1) (w 2))| / eta) ↔ _
    rw [hc.1, hc.2.1]
    rfl
  ext x
  constructor
  · rintro ⟨w,hw,rfl⟩; exact (test w).mpr hw
  · intro hx
    exact ⟨(chartPose r).symm x,(test _).mp (by simpa using hx),by simp⟩

/-- Affine combinations are proved directly for the native chart; no
choice of a line parameter or an orientation of a segment is implicit. -/
theorem chart_affine (r : Role) (u v : E3) (s t : ℝ) (hst : s+t=1) :
    chartPose r (s • u+t • v)=s • chartPose r u+t • chartPose r v := by
  simp only [chartPose_apply,map_add,map_smul,smul_add]
  have hc : s • featureCenter r+t • featureCenter r=featureCenter r := by
    rw [←add_smul,hst,one_smul]
  calc
    _ = (s • featureCenter r+t • featureCenter r)+
        (s • chartEquiv r u+t • chartEquiv r v) := by rw [hc]
    _ = _ := by module

/-- Transport every point, rather than a midpoint of a native edge. -/
theorem chart_openSegment (r : Role) (u v x : E3)
    (hx : x∈openSegment ℝ u v) :
    chartPose r x∈openSegment ℝ (chartPose r u) (chartPose r v) := by
  rcases hx with ⟨s,t,hs,ht,hst,rfl⟩
  exact ⟨s,t,hs,ht,hst,(chart_affine r u v s t hst).symm⟩

/-- A spelling of the accepted radial transport specialized to linear
isometries; avoids relying on an implicit coercion to affine motions. -/
theorem radial_orthogonal_image (A : E3 ≃ₗᵢ[ℝ] E3) (S : Set E3) (x : E3) :
    tangentCone (A '' S) (A x)=A '' tangentCone S x := by
  simpa using radial_image A.toAffineIsometryEquiv S x
  -- API?: LinearIsometryEquiv.toAffineIsometryEquiv has zero translation
  -- and the original linear isometry as its linear part.

private def qturn (k : Fin 4) : E3 ≃ₗᵢ[ℝ] E3 := (turn (-Real.pi/2))^k.val

-- [compile-fix begin: normalize quarter-turn application definitionally]
private theorem qturn_H (k : Fin 4) (a : ℝ) :
    qturn k '' H a=H a := by
  have test (w : E3) : qturn k w∈H a ↔ w∈H a := by
    have hangle : -Real.pi/2 = -(Real.pi/2) := by ring
    fin_cases k <;>
      simp [qturn,pow_succ,turn_apply,H,tent,pt,hangle,
        Real.cos_neg,Real.sin_neg,Real.cos_pi_div_two,Real.sin_pi_div_two,
        max_comm]
  exact (set_image_of_test (qturn k) (H a) (H a) test).symm

private theorem qturn_corners (k : Fin 4) :
    qturn k (B 0)=B k ∧ qturn k (B 1)=B (nextCorner k) := by
  have hangle : -Real.pi/2 = -(Real.pi/2) := by ring
  fin_cases k <;>
    simp [qturn,pow_succ,turn_apply,B,nextCorner,pt,hangle,
      Real.cos_neg,Real.sin_neg,Real.cos_pi_div_two,Real.sin_pi_div_two]
-- [compile-fix end]

private theorem edge_membership_in_graph (r : Role) (kind : FeatureEdgeKind)
    {x : E3} (hx : x∈nativeGenericEdgesOfKind r kind) : x∈nativeFeatureGraph r := by
  cases kind with
  | base =>
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      exact Or.inl (Set.mem_iUnion.mpr ⟨k,openSegment_subset_segment ℝ _ _ hk⟩)
  | ridge =>
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨k,openSegment_subset_segment ℝ _ _ hk⟩)

/-- No generic point is omitted; all four open base edges and all four open
ridges are transported through their native affine charts. -/
theorem native_feature_oriented_meridian (r : Role) (kind : FeatureEdgeKind)
    (x : E3) (hx : x∈nativeGenericEdgesOfKind r kind) :
    Nonempty (AngularMeridian (tangentCone Q x) (featureInteriorAngle r kind)) := by
  let a := (profileCoefficient r : ℝ)/10000
  have hg := edge_membership_in_graph r kind hx
  have ht : tangentCone Q x=tangentCone (chartPose r '' H a) x := by
    rw [chart_hypograph]
    exact native_tangentCone_eq_hypograph r hg
  cases kind with
  | base =>
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      rcases hk with ⟨s,t,hs,ht',hst,he⟩
      let b := (t-s)*eta
      have hb : |b|<eta := by
        apply abs_lt.mpr
        dsimp [b]; norm_num [eta]; constructor <;> linarith
      let w := pt (-eta) b 0
      have hp : x=chartPose r (qturn k w) := by
        rw [←he]
        have hw : w=s • B 0+t • B 1 := by
          -- [compile-fix: use the affine coefficient equation algebraically]
          have ht_eq : t = 1 - s := by linarith
          ext i
          fin_cases i <;> simp [w,b,B,pt, ht_eq] <;> ring
        rw [hw,map_add,map_smul,map_smul,(qturn_corners k).1,
          (qturn_corners k).2]
        rw [chart_affine r (B k) (B (nextCorner k)) s t hst,
          chartPose_B,chartPose_B]
      rw [ht,hp,radial_image]
      have hi : tangentCone (H a) (qturn k w)=qturn k '' baseCone a := by
        conv_lhs => rw [←qturn_H k a]
        rw [radial_orthogonal_image]
        rw [tangent_at_base a b hb]
        -- [compile-fix: preceding rewrites close the goal]
      rw [hi]
      have m := ((canonical_base_meridian a).map (qturn k)).map (chartEquiv r)
      rw [show Real.pi+Real.arctan (a/eta)=featureInteriorAngle r .base from
        base_angle_signed r] at m
      exact ⟨m⟩
  | ridge =>
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      rcases hk with ⟨s,t,hs,ht',hst,he⟩
      let sx : ℝ := if k.val=0 ∨ k.val=1 then -1 else 1
      let sy : ℝ := if k.val=0 ∨ k.val=3 then -1 else 1
      have hsx : sx=1 ∨ sx= -1 := by dsimp [sx]; split_ifs <;> simp
      have hsy : sy=1 ∨ sy= -1 := by dsimp [sy]; split_ifs <;> simp
      let b := s*eta
      have hb0 : 0<b := mul_pos hs (by norm_num [eta])
      have hb1 : b<eta := by dsimp [b]; norm_num [eta]; linarith
      let w := pt (sx*b) (sy*b) (a*(1-b/eta))
      have hw : w=s • B k+t • A a := by
        -- [compile-fix: expose the four finite corner cases, then use hst]
        have ht_eq : t = 1 - s := by linarith
        fin_cases k <;>
          ext i <;> fin_cases i <;> simp [w,B,A,pt,sx,sy,b] <;>
            norm_num [eta] <;> simp [ht_eq] <;> ring
      have hp : x=chartPose r w := by
        rw [←he,hw]
        rw [chart_affine r (B k) (A a) s t hst,chartPose_B]
        have hA : chartPose r (A a)=featureApex r := by
          simpa [a] using chartPose_A r
        rw [hA]
      rw [ht,hp,radial_image,tangent_at_ridge a sx sy b hsx hsy hb0 hb1]
      have m := (canonical_ridge_meridian a sx sy hsx hsy).map (chartEquiv r)
      rw [show Real.pi-2*Real.arctan ((a/eta)/Real.sqrt (2+(a/eta)^2))=
        featureInteriorAngle r .ridge from ridge_angle_signed r] at m
      exact ⟨m⟩

end
end R44.DischargeMeridian
