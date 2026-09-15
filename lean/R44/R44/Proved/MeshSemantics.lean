/- -- [compile-fix: promoted to Proved after exchange 7]
# Shared native mesh semantics — exchange 5

Written sources: proof/ALIGNMENT_PROOF.md A§1, A-L2.2, A-L3.1;
proof/PROOFS_registered.md R§1.1--1.3. The public shared endpoint and native
chart statements are unchanged. The actual 3D wedge-volume calculation and
orthogonal volume transport are now proved in WedgeVolume. The two signed
tangent-set formulas remain the accepted TentTangentCharts results.

-- [compile-fix begin: exchange 7 closes the native meridian bridge]
STATUS: CLOSED. NativeDihedralSectors.native_measured_meridians now proves the
oriented native planar sectors, their disk-area law, and complete mesh-edge
chart interpretation. The dependency chain is admission-free.
-- [compile-fix end]
-/
import R44.Proved.FeatureLocalCharts -- [compile-fix]
import R44.Proved.TentTangentCharts -- [compile-fix: promoted after exchange 7]
import R44.Proved.NativeDihedralSectors -- [compile-fix: promoted after exchange 7]

namespace R44
open Set
open Generated
noncomputable section

/-- The closed-tube set identity, with both signs of the native coefficient. -/
theorem native_Q_eq_signed_tent_in_tube (r : Role) (x : E3)
    (hx : featureTubeSupport r x) :
    x ∈ Q ↔ featureNormalCoordinate r x ≤ featureHeight r x :=
  DischargeGeometry.mem_Q_iff_in_tube r x hx

theorem native_Q_eq_carrier_outside {x : E3}
    (hx : ∀ r : Role, ¬ featureTubeSupport r x) :
    x ∈ Q ↔ x ∈ P :=
  DischargeGeometry.mem_Q_iff_outside hx

theorem native_features_in_frontier :
    ∀ r : Role, nativeFeatureGraph r ⊆ frontier Q ∧
      nativeFeatureSurface r ⊆ frontier Q := by
  intro r
  exact ⟨DischargeGeometry.nativeFeatureGraph_frontier r,
    DischargeGeometry.nativeFeatureSurface_frontier r⟩

/-- NEW: the defining hypograph agrees on an ambient OPEN neighborhood,
even when x lies on the perimeter of the closed native tube. -/
theorem native_feature_open_hypograph (r : Role) {x : E3}
    (hx : x ∈ nativeFeatureGraph r) :
    ∃ U : Set E3, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ Q ↔
        featureNormalCoordinate r y ≤ featureHeight r y :=
  DischargeCharts.open_tent_agreement r hx

/-- NEW: an equality of the frozen radial tangent-cone SETS. This is stronger
than frontier membership, but it does not assert a volume calculation. -/
theorem native_feature_tangent_germ (r : Role) {x : E3}
    (hx : x ∈ nativeFeatureGraph r) :
    tangentCone Q x = tangentCone
      {y | featureNormalCoordinate r y ≤ featureHeight r y} x :=
  DischargeCharts.native_tangentCone_eq_hypograph r hx

private theorem generic_edge_in_graph (r : Role) (kind : FeatureEdgeKind) :
    nativeGenericEdgesOfKind r kind ⊆ nativeFeatureGraph r := by
  intro x hx
  cases kind with
  | base =>
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      apply Or.inl
      exact Set.mem_iUnion.mpr ⟨k,openSegment_subset_segment ℝ _ _ hk⟩
        -- API?: expected openSegment_subset_segment : openSegment ℝ a b ⊆ segment ℝ a b.
  | ridge =>
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨k,openSegment_subset_segment ℝ _ _ hk⟩
        -- API?: same segment-containment lemma.

/-- NEW: specialization of the open-germ equality to the exact base/ridge
strata quantified by HasFeatureDihedral. No generic point is dropped. -/
theorem native_generic_dihedral_germ (r : Role) (kind : FeatureEdgeKind)
    {x : E3} (hx : x ∈ nativeGenericEdgesOfKind r kind) :
    tangentCone Q x = tangentCone
      {y | featureNormalCoordinate r y ≤ featureHeight r y} x :=
  native_feature_tangent_germ r (generic_edge_in_graph r kind hx)

/-- A-L3.1 canonical base SET formula. The native height may be negative.
Coordinates are an orthonormal feature chart; eta is the fixed half-width. -/
theorem canonical_tent_base_tangent (a b : ℝ) (hb : |b|<eta) :
    tangentCone (DischargeTentCones.H a) (DischargePyramid.pt (-eta) b 0) =
      {d : E3 | d 2≤(a/eta)*max 0 (d 0)} :=
  DischargeTentCones.tangent_at_base a b hb

/-- A-L3.1 canonical ridge SET formula, covering all four ridge directions.
This retains max and its sign: a recess gives a UNION, not an intersection. -/
theorem canonical_tent_ridge_tangent (a sx sy b : ℝ)
    (hsx : sx=1 ∨ sx=-1) (hsy : sy=1 ∨ sy=-1)
    (hb0 : 0<b) (hb1 : b<eta) :
    tangentCone (DischargeTentCones.H a)
      (DischargePyramid.pt (sx*b) (sy*b) (a*(1-b/eta))) =
      {d : E3 | d 2≤-(a/eta)*max (sx*d 0) (sy*d 1)} :=
  DischargeTentCones.tangent_at_ridge a sx sy b hsx hsy hb0 hb1

/-- The 3D cone-volume semantics is derived from the planar section normal
forms. -- [compile-fix: the exchange-7 dependency is admission-free] -/
private theorem native_mesh_cone_semantics
    (hmesh : solidMeshCheck = true)
    (haudit : meshAngleAuditCheck = true)
    (hprofile : profileCanonicalCheck = true) :
    (∀ r : Role, HasFeatureDihedral Q r .base ∧ HasFeatureDihedral Q r .ridge) ∧
    (∀ key ∈ meshGeometricEdgeKeys, ∀ c : Nat × Nat × Int,
      classifyMeshEdge key = some c → HasMeshDihedralClass Q key c) := by
  obtain ⟨hfeature,hclass⟩ :=
    DischargeMeridian.native_measured_meridians hmesh haudit hprofile
  constructor
  · intro r
    constructor <;> intro x hx
    · obtain ⟨m⟩ := hfeature r .base x hx
      exact m.solidAngle
    · obtain ⟨m⟩ := hfeature r .ridge x hx
      exact m.solidAngle
  · intro key hk c hc x hx
    obtain ⟨theta,hv,⟨m⟩⟩ := hclass key hk c hc x hx
    have hm := m.solidAngle
    change (if c.1=0 then _ else if c.1=1 then _ else if c.1=2 then _ else _)
    unfold DischargeMeridian.MeshAngleValue at hv
    split_ifs at hv ⊢ with h0 h1 h2
    · rcases hv with rfl|rfl
      · exact Or.inl hm
      · exact Or.inr hm
    · rcases hv with rfl|rfl
      · exact Or.inl hm
      · exact Or.inr hm
    · subst theta
      exact hm
    · rcases hv with rfl|rfl
      · left
        simpa only [show 2*(Real.pi/2)=Real.pi by ring] using hm
      · right
        simpa only [show 2*(3*Real.pi/2)=3*Real.pi by ring] using hm

/-- The frozen shared endpoint has the byte-for-byte exchange-2 proposition.
    Its exchange-7 dependency chain is admission-free. -- [compile-fix] -/
theorem native_mesh_dihedral_semantics
    (hmesh : solidMeshCheck = true)
    (haudit : meshAngleAuditCheck = true)
    (hprofile : profileCanonicalCheck = true) :
    (∀ r : Role, nativeFeatureGraph r ⊆ frontier Q ∧
      nativeFeatureSurface r ⊆ frontier Q) ∧
    (∀ r : Role, HasFeatureDihedral Q r .base ∧ HasFeatureDihedral Q r .ridge) ∧
    (∀ key ∈ meshGeometricEdgeKeys, ∀ c : Nat × Nat × Int,
      classifyMeshEdge key = some c → HasMeshDihedralClass Q key c) := by
  exact ⟨native_features_in_frontier,
    native_mesh_cone_semantics hmesh haudit hprofile⟩

end
end R44
