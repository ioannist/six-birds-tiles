/- -- [compile-fix]
# Discharge: feature_containment_rigidity

Written source: proof/ALIGNMENT_PROOF.md A-L4.3, with ERRATA E1 and the
round-2 distinct-placement repair. The frozen g ≠ h premise is essential.
Generic partners identify the companion role and opposite coefficient.

ALTERNATIVE to the written Hausdorff-length step: congruent compact graphs
cannot be properly contained (CompactCongruent.lean). The graph's intrinsic
base square and apex then determine its lateral surfaces. This proves the
unchanged proposition without a Hausdorff-measure admission. No mesh-volume
bridge or later companion/alignment field is imported. No admissions.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.PyramidGeometry -- [compile-fix]

namespace R44.DischargePyramid
open Set R44.DischargeFeatureGraphs
noncomputable section

/-- Opposite polarity follows from one generic point and distinct tiles.
No presumed genericity of the containing graph is needed: uniqueness of
roles within one tile supplies it. -/
theorem containment_opposite (hgeneric : GenericFeaturePartners Q)
    (T : Tiling Q) (g h : RigidMotion) (hg : g∈T.placements)
    (hh : h∈T.placements) (hne : g≠h) (r s : Role)
    (hsub : featureGraphAt g r⊆featureGraphAt h s) :
    profileCoefficient r = -profileCoefficient s := by
  obtain ⟨D,hDsub,hcl,hpartner⟩ := hgeneric T g hg r
  have hn : (D .base∪D .ridge).Nonempty := by
    by_contra hempty
    have he := Set.not_nonempty_iff_eq_empty.mp hempty
      -- API?: not_nonempty_iff_eq_empty for Set.
    rw [he,closure_empty] at hcl
    exact (graph_connected g r).nonempty.ne_empty hcl.symm
  obtain ⟨x,hx⟩ := hn
  have hex : ∃kind,x∈D kind := by
    rcases hx with hx | hx
    · exact ⟨.base,hx⟩
    · exact ⟨.ridge,hx⟩
  obtain ⟨kind,hxD⟩ := hex
  have hxg := generic_subset_graph g r kind (hDsub kind hxD)
  have hxh := hsub hxg
  obtain ⟨⟨k,t⟩,hkt,_⟩ := hpartner kind x hxD
  have hk : h=k := (hkt.2.2.2.2 h hh (graph_in_tile h s hxh)).resolve_left
    (Ne.symm hne)
  subst k
  have hxt : x∈featureGraphAt h t := generic_subset_graph h t kind hkt.2.2.1
  have hst : s=t := by
    by_contra hhst
    exact Set.disjoint_left.mp (graph_roles_disjoint h hhst) hxh hxt
  simpa [hst] using hkt.2.2.2.1

/-- Transport a graph containment to the common canonical chart. -/
theorem normalized_graph_containment (g h : RigidMotion) (r s : Role)
    (hsub : featureGraphAt g r⊆featureGraphAt h s) :
    ((h*chartPose s)⁻¹*(g*chartPose r)) '' G ((profileCoefficient r:ℝ)/10000)
      ⊆ G ((profileCoefficient s:ℝ)/10000) := by
  rintro x ⟨w,hw,rfl⟩
  have hxg : (g*chartPose r) w∈featureGraphAt g r := by
    exact ⟨chartPose r w,chart_graph r ▸ ⟨w,hw,rfl⟩,rfl⟩
  obtain ⟨y,hy,hxy⟩ := hsub hxg
  rw [← chart_graph s] at hy
  obtain ⟨z,hz,hzy⟩ := hy
  have heq : (g*chartPose r) w=(h*chartPose s) z := by
    simpa [hzy] using hxy.symm
  have hn : ((h*chartPose s)⁻¹*(g*chartPose r)) w = z := by -- [compile-fix]
    change (h * chartPose s)⁻¹ ((g * chartPose r) w) = z -- [compile-fix begin: expose the composite without unfolding its factors]
    rw [heq] -- [compile-fix]
    exact (h * chartPose s).symm_apply_apply z -- [compile-fix]
    -- [compile-fix end]
  simpa only [hn] using hz -- [compile-fix]

/-- Equality of canonical graphs transports to the physical graphs. -/
theorem denormalize_graph_eq (g h : RigidMotion) (r s : Role)
    (heq : ((h*chartPose s)⁻¹*(g*chartPose r)) ''
      G ((profileCoefficient r:ℝ)/10000)=G ((profileCoefficient s:ℝ)/10000)) :
    featureGraphAt g r=featureGraphAt h s := by
  change g '' nativeFeatureGraph r = h '' nativeFeatureGraph s
  rw [← chart_graph r,← chart_graph s]
  calc
    g '' (chartPose r '' G ((profileCoefficient r:ℝ)/10000)) =
        (g*chartPose r) '' G ((profileCoefficient r:ℝ)/10000) := by
          simp only [Set.image_image,AffineIsometryEquiv.coe_mul,Function.comp_def]
    _ = (h*chartPose s) '' (((h*chartPose s)⁻¹*(g*chartPose r)) ''
        G ((profileCoefficient r:ℝ)/10000)) := by
          simp only [Set.image_image,AffineIsometryEquiv.coe_mul,Function.comp_def]
          congr 1; funext x; simp
    _ = (h*chartPose s) '' G ((profileCoefficient s:ℝ)/10000) := by rw [heq]
    _ = h '' (chartPose s '' G ((profileCoefficient s:ℝ)/10000)) := by
          simp only [Set.image_image,AffineIsometryEquiv.coe_mul,Function.comp_def]

/-- Equality of canonical lateral surfaces transports in the same way. -/
theorem denormalize_surface_eq (g h : RigidMotion) (r s : Role)
    (heq : ((h*chartPose s)⁻¹*(g*chartPose r)) ''
      S ((profileCoefficient r:ℝ)/10000)=S ((profileCoefficient s:ℝ)/10000)) :
    featureSurfaceAt g r=featureSurfaceAt h s := by
  change g '' nativeFeatureSurface r = h '' nativeFeatureSurface s
  rw [← chart_surface r,← chart_surface s]
  calc
    g '' (chartPose r '' S ((profileCoefficient r:ℝ)/10000)) =
        (g*chartPose r) '' S ((profileCoefficient r:ℝ)/10000) := by
          simp only [Set.image_image,AffineIsometryEquiv.coe_mul,Function.comp_def]
    _ = (h*chartPose s) '' (((h*chartPose s)⁻¹*(g*chartPose r)) ''
        S ((profileCoefficient r:ℝ)/10000)) := by
          simp only [Set.image_image,AffineIsometryEquiv.coe_mul,Function.comp_def]
          congr 1; funext x; simp
    _ = (h*chartPose s) '' S ((profileCoefficient s:ℝ)/10000) := by rw [heq]
    _ = h '' (chartPose s '' S ((profileCoefficient s:ℝ)/10000)) := by
          simp only [Set.image_image,AffineIsometryEquiv.coe_mul,Function.comp_def]

end
end R44.DischargePyramid

namespace R44
open R44.DischargePyramid
noncomputable section

/-- Exact frozen proposition. WholeFeatureCompanions remains a premise;
the stronger generic uniqueness proposition already suffices here. -/
theorem feature_containment_rigidity_holds :
    GenericFeaturePartners Q → WholeFeatureCompanions Q → FeatureContainmentRigidity Q := by
  intro hgeneric _hwhole T g h hg hh hne r s hsub
  have hsign := containment_opposite hgeneric T g h hg hh hne r s hsub
  have hsignR : ((profileCoefficient s:ℝ)/10000) =
      -((profileCoefficient r:ℝ)/10000) := by
    have he : (profileCoefficient s:ℝ)=-(profileCoefficient r:ℝ) := by
      have hi : profileCoefficient s = -profileCoefficient r := by omega
      exact_mod_cast hi
    rw [he]; ring
  let m : RigidMotion := (h*chartPose s)⁻¹*(g*chartPose r)
  have hsub' := normalized_graph_containment g h r s hsub
  rw [hsignR] at hsub'
  have heq := opposite_graph_containment_eq m hsub'
  have heq' : m '' G ((profileCoefficient r:ℝ)/10000)=
      G ((profileCoefficient s:ℝ)/10000) := by simpa [hsignR] using heq
  have hsurf := graph_eq_surface (native_small r) (native_small s) m heq'
  exact ⟨denormalize_graph_eq g h r s heq',
    denormalize_surface_eq g h r s hsurf,hsign⟩

end
end R44
