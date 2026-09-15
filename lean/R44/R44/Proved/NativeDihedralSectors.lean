/- -- [compile-fix: promoted to Proved after exchange 7]
# Closed native oriented meridians and their measured interpretation

Written sources: proof/ALIGNMENT_PROOF.md A-L2.2/A-L3.1 and A§1.
All public endpoint propositions and geometric records are unchanged.
The records now live in AngularMeridianCore (same namespace and definitions)
to avoid an import cycle. The native open edges are transported through
actual orthogonal charts, including the principal-angle sign and both
boundary rays. The independent incidence trace connects every OTHER
classified mesh edge to a carrier chart off every closed edit support.
The accepted polar-sector law and wedge-volume theorem supply measurement.

No mathematical admissions. No new hypothesis, compiler oracle, native
census, or floating-point comparison is introduced. See MeshChartIncidence
for the new kernel-reduced finite incidence predicate and its resource note.
-/
import R44.Proved.MeshChartInterpretation -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeMeridian
open Set R44.DischargeWedge R44.DischargePlanar
noncomputable section

theorem native_oriented_wedge_charts
    (hmesh:solidMeshCheck=true) (haudit:meshAngleAuditCheck=true)
    (hprofile:profileCanonicalCheck=true) :
    (∀r:Role,∀kind:FeatureEdgeKind,∀x∈nativeGenericEdgesOfKind r kind,
      Nonempty (AngularMeridian (tangentCone Q x) (featureInteriorAngle r kind))) ∧
    (∀key∈meshGeometricEdgeKeys,∀c:Nat×Nat×Int,classifyMeshEdge key=some c →
      ∀x∈nativeGenericMeshEdge key,∃theta:ℝ,MeshAngleValue c theta ∧
        Nonempty (AngularMeridian (tangentCone Q x) theta)) := by
  constructor
  · intro r kind x hx
    exact native_feature_oriented_meridian r kind x hx
  · intro key hk c hc x hx
    exact DischargeMeshTrace.every_mesh_edge_oriented key hk c hc x hx

/-- Frozen exchange-5 endpoint. The actual area law is constructed from the
proved native charts and the accepted planar-sector integration theorem. -/
theorem native_measured_meridians
    (hmesh:solidMeshCheck=true) (haudit:meshAngleAuditCheck=true)
    (hprofile:profileCanonicalCheck=true) :
    (∀r:Role,∀kind:FeatureEdgeKind,∀x∈nativeGenericEdgesOfKind r kind,
      Nonempty (Meridian (tangentCone Q x) (featureInteriorAngle r kind))) ∧
    (∀key∈meshGeometricEdgeKeys,∀c:Nat×Nat×Int,classifyMeshEdge key=some c →
      ∀x∈nativeGenericMeshEdge key,∃theta:ℝ,MeshAngleValue c theta ∧
        Nonempty (Meridian (tangentCone Q x) theta)) := by
  obtain ⟨hfeat,hall⟩ := native_oriented_wedge_charts hmesh haudit hprofile
  constructor
  · intro r kind x hx
    exact (hfeat r kind x hx).map AngularMeridian.measured
  · intro key hk c hc x hx
    obtain ⟨theta,ht,hm⟩ := hall key hk c hc x hx
    exact ⟨theta,ht,hm.map AngularMeridian.measured⟩

end
end R44.DischargeMeridian
