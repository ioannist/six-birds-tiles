/- -- [compile-fix: promoted to Proved after exchange 7]
# Native boundary strata: proof for the actual set-defined Q

Written sources: proof/ALIGNMENT_PROOF.md A-L2.2, A-L3.1, A-L3.2.
The frozen statement and exceptional set are unchanged. No tiling is used.

Inside a CLOSED native support, an OPEN ambient chart identifies Q with the
signed-tent hypograph. The square perimeter gives base segments, the equal
absolute-coordinate locus gives the ridges, and every strict max branch is
an affine facet. All exceptional apex/corner points are explicit vertices
of the frozen mesh. Outside every closed support, the carrier chart is
open; the carrier's five coordinate strata classify its actual radial cone.

The geometric classification has no measure-valued premise. Ordinary
angles follow from the accepted planar-sector and wedge-volume theorems;
named feature angles are taken from the frozen hdihedral premise. No
mesh-frontier equivalence, normal audit, or point sampling substitutes for
the continuous boundary argument. No mathematical admissions.
-/
import R44.Proved.PolyhedralConeMeasure -- [compile-fix: promoted after exchange 7]
import R44.Proved.CanonicalTentStrata -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeNativeStrata
open Set DischargeSectors Generated
open DischargeGeometry DischargeCharts DischargeBoundaryLocal
open DischargeTentCones DischargePyramid DischargeMeridian
open DischargeTentStrata DischargeCarrierStrata DischargeVertexData
open DischargePolyhedral DischargeTangentTransport
noncomputable section
set_option maxHeartbeats 0

/-- Includes artificial triangulation vertices. Over-exclusion is harmless:
only finiteness, not minimality of this exceptional set, is needed. -/
def nativeVertices : Set E3 :=
  {x | ∃v∈solidVertices10000, x=scaledV3 10000 v}

 theorem nativeVertices_finite : nativeVertices.Finite := by
  have he : nativeVertices=(fun v : V3 => scaledV3 10000 v) ''
      {v | v∈solidVertices10000} := by
    ext x; simp [nativeVertices,Set.mem_image,eq_comm]
  rw [he]
  exact solidVertices10000.finite_toSet.image _

private theorem mesh_vertex_mem {x : E3} (hx : MeshVertex x) : x∈nativeVertices := hx

private theorem ordinary_label (C : Set E3) (code : Fin 3)
    (h : Nonempty (AngularMeridian C (((code.val+1:Nat):ℝ)*Real.pi/2))) :
    solidAngle C=ENNReal.ofReal (2*(SectorLabel.ordinary code).angle) := by
  obtain ⟨m⟩ := h
  simpa [SectorLabel.angle] using m.measured.solidAngle

private theorem chart_open_base (r : Role) (w : E3) (hw : w∈openBases) :
    chartPose r w∈nativeGenericEdgesOfKind r .base := by
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hw
  apply Set.mem_iUnion.mpr
  refine ⟨k,?_⟩
  -- [compile-fix: use only the endpoint transport lemmas; do not unfold corners]
  simpa only [chartPose_B] using chart_openSegment r (B k) (B (nextCorner k)) w hk

private theorem chart_open_ridge (r : Role) (w : E3)
    (hw : w∈openRidges ((profileCoefficient r:ℝ)/10000)) :
    chartPose r w∈nativeGenericEdgesOfKind r .ridge := by
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hw
  apply Set.mem_iUnion.mpr
  refine ⟨k,?_⟩
  -- [compile-fix: use only the endpoint transport lemmas; do not unfold endpoints]
  simpa only [chartPose_B,chartPose_A] using
    chart_openSegment r (B k) (A ((profileCoefficient r:ℝ)/10000)) w hk

/-- The exact native interpretation requested by exchange 6/7. -/
theorem native_boundary_strata (hdihedral : CompleteDihedralList Q) :
    ∀x∈frontier Q, x∉nativeVertices →
      ∃label : SectorLabel,
        (∀kind r,label=.feature kind r → x∈nativeGenericEdgesOfKind r kind) ∧
        solidAngle (tangentCone Q x)=ENNReal.ofReal (2*label.angle) := by
  intro x hx hnv
  by_cases ht : ∃r:Role,featureTubeSupport r x
  · obtain ⟨r,hr⟩ := ht
    let a : ℝ := (profileCoefficient r:ℝ)/10000
    let w : E3 := (chartPose r).symm x
    have hw : chartPose r w=x := by simp [w]
    have he : chartPose r w=chartPoint r (w 0) (w 1) (w 2) := by
      simp [chartPose_apply,chartEquiv_apply,chartLinear_apply,chartPoint]
      module
    have hc := chart_coordinates r (w 0) (w 1) (w 2)
    rw [←he,hw] at hc
    have hrad : max |w 0| |w 1|≤eta := by
      -- [compile-fix: expose the coordinate abbreviations before rewriting]
      have h := hr.1
      change max |chartU r x| |chartV r x| ≤ eta at h
      simpa only [hc.1, hc.2.1] using h
    have heq := frontier_in_tube_equation r x hx hr
    have hz : w 2=tent a w := by
      rw [hc.2.2] at heq
      -- [compile-fix: rewrite chart coordinates through their proved equations]
      change w 2 = ((profileCoefficient r : ℝ) / 10000) *
        max 0 (1 - max |chartU r x| |chartV r x| / eta) at heq
      simpa only [hc.1, hc.2.1, a, tent] using heq
    obtain ⟨U,hU,hxU,heU⟩ := open_chart_at_tube r x hr
    have htan : tangentCone Q x=
        chartEquiv r '' tangentCone (H a) w := by
      rw [tangentCone_of_open_agreement hU hxU heU]
      rw [←chart_hypograph r,←hw,radial_image]
      rfl
    rcases canonical_boundary_cases a w hrad hz with hvertex|hbase|hridge|hflat
    · rcases hvertex with hapex|⟨k,hcorner⟩
      · have hxapex : x=featureApex r := by
          rw [←hw,hapex]; simpa [a] using chartPose_A r
        exfalso
        apply hnv
        rw [hxapex]
        exact mesh_vertex_mem (feature_apex_is_mesh_vertex r)
      · have hxcorner : x=featureCorner r k := by
          rw [←hw,hcorner,chartPose_B]
        exfalso
        apply hnv
        rw [hxcorner]
        exact mesh_vertex_mem (feature_corner_is_mesh_vertex r k)
    · have hb : x∈nativeGenericEdgesOfKind r .base := by
        simpa [hw] using chart_open_base r w hbase
      refine ⟨.feature .base r,?_,?_⟩
      · intro kind s hs
        cases hs
        exact hb
      · exact (hdihedral.2.1 r).2.2.1 x hb
    · have hb : x∈nativeGenericEdgesOfKind r .ridge := by
        simpa [hw,a] using chart_open_ridge r w hridge
      refine ⟨.feature .ridge r,?_,?_⟩
      · intro kind s hs
        cases hs
        exact hb
      · exact (hdihedral.2.1 r).2.2.2 x hb
    · refine ⟨.ordinary 1,by intros; contradiction,?_⟩
      rw [htan]
      obtain ⟨m⟩ := hflat
      simpa [SectorLabel.angle] using (m.map (chartEquiv r)).measured.solidAngle
  · have hout : ∀r:Role,¬featureTubeSupport r x := by simpa using ht
    obtain ⟨U,hU,hxU,he⟩ := open_carrier_off_tubes x hout
    have hxP : x∈frontier P :=
      frontier_transfer Q_object.1.isClosed P_compact.isClosed hU hxU he hx
    have hnotgrid : ¬∀i:Fin 3,x i=0 ∨ x i=1 ∨ x i=2 := by
      intro hgrid
      have hm : x∈P := by simpa [P_compact.isClosed.closure_eq] using hxP.1
      exact hnv (mesh_vertex_mem (carrier_grid_point_is_mesh_vertex x hm hgrid))
    obtain ⟨code,m⟩ := carrier_boundary_meridian x hxP hnotgrid
    refine ⟨.ordinary code,by intros; contradiction,?_⟩
    rw [tangentCone_of_open_agreement hU hxU he]
    exact ordinary_label _ code m

end
end R44.DischargeNativeStrata
