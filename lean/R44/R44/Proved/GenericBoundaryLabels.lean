/- -- [compile-fix: promoted to Proved after exchange 7]
# Generic labels in arbitrary tilings from the native boundary strata

A-L2.2/A-L3.2, proof/ALIGNMENT_PROOF.md. The frozen endpoint and helper
record are unchanged. The global quantifiers, finite incident family,
exceptional-set deletion, endpoint-inclusive density, and root label are
proved here. -- [compile-fix: exchange 7 proves NativeBoundaryStrata.native_boundary_strata]

The deletion may be smaller than the written planar-section deletion:
we remove all native mesh vertices of all tiles meeting the root graph.
Every remaining incident cone has a native edge/face label. The REAL sum
is then derived by the already proved THREE-dimensional cone-volume
additivity; a common transverse plane is not required for that argument.
There is no assumption that a point is face-to-face or that a neighbor's
edge is collinear. The sector arithmetic subsequently excludes any wrong
incident combination. This is an explicit proof route, not an unmentioned
replacement of the frozen sector or solidAngle definitions.
-/
import R44.Proved.NativeBoundaryStrata -- [compile-fix: admission-free exchange-7 bridge]
import R44.Proved.FiniteEdgeExceptions -- [compile-fix: promoted after exchange 7]
import R44.Proved.TangentIsometry -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeSectors
open Set DischargeNativeStrata DischargeFeatureGraphs DischargeEdgeDensity
open DischargePolyhedral DischargeTangentTransport
noncomputable section
set_option maxHeartbeats 0

structure BoundaryLabels (T:Tiling Q) (g:RigidMotion) (r:Role)
    (kind:FeatureEdgeKind) (x:E3) where
  incident : Finset RigidMotion
  incident_iff : ∀h,h∈incident ↔ h∈T.placements ∧ x∈h '' Q
  label : RigidMotion → SectorLabel
  feature_location : ∀h∈incident,∀k s,label h=.feature k s →
    x∈genericEdgesOfKindAt h s k
  root_mem : g∈incident
  root_label : label g=.feature kind r
  angle_semantics : ∀h∈incident,
    solidAngle (tangentCone (h '' Q) x)=ENNReal.ofReal (2*(label h).angle)

private theorem placed_regular (g : RigidMotion) :
    closure (interior (g '' Q))=g '' Q := by
  change closure (interior (g.toHomeomorph '' Q)) = g.toHomeomorph '' Q -- [compile-fix: expose the homeomorphism coercion]
  rw [←g.toHomeomorph.image_interior,←g.toHomeomorph.image_closure,Q_object.2.1]

/-- A different packed tile cannot put a regular-closed root boundary point
in its interior. The assertion is about the actual sets, not their meshes. -/
private theorem neighbor_frontier (T : Tiling Q) {g h : RigidMotion}
    (hg : g∈T.placements) (hh : h∈T.placements) (hne : g≠h)
    {x : E3} (hxg : x∈g '' Q) (hxh : x∈h '' Q) :
    x∈frontier (h '' Q) := by
  refine ⟨subset_closure hxh,?_⟩
  intro hxi
  have hxcl : x∈closure (interior (g '' Q)) := by rwa [placed_regular]
  obtain ⟨y,hyh,hyg⟩ := mem_closure_iff.mp hxcl (interior (h '' Q))
    isOpen_interior hxi
    -- API?: neighborhood form of mem_closure_iff: every open neighborhood
    -- of x intersects the set. Intersection order may require swapping fields.
  exact Set.disjoint_left.mp (T.disjoint_interiors hg hh hne) hyg hyh

private theorem placed_feature_angle (hlist : CompleteDihedralList Q)
    (g : RigidMotion) (r : Role) (kind : FeatureEdgeKind)
    {x : E3} (hx : x∈genericEdgesOfKindAt g r kind) :
    solidAngle (tangentCone (g '' Q) x)=
      ENNReal.ofReal (2*(SectorLabel.feature kind r).angle) := by
  obtain ⟨y,hy,rfl⟩ := hx
  rw [solidAngle_placed,g.symm_apply_apply]
  cases kind with
  | base => exact (hlist.2.1 r).2.2.1 y hy
  | ridge => exact (hlist.2.1 r).2.2.2 y hy

/-- Statement identical to exchange 5. All arbitrary-tiling steps are now
proved; its one remaining dependency is the native stratum interpretation. -/
theorem generic_boundary_labels
    (hbudget : ConeSectorBudgets Q) (hdihedral : CompleteDihedralList Q)
    (T : Tiling Q) (g : RigidMotion) (hg : g∈T.placements) (r : Role) :
    ∃D : FeatureEdgeKind → Set E3,
      (∀kind,D kind⊆genericEdgesOfKindAt g r kind) ∧
      closure (D .base∪D .ridge)=featureGraphAt g r ∧
      ∀kind x,x∈D kind → Nonempty (BoundaryLabels T g r kind x) := by
  classical
  let J : Set RigidMotion :=
    {h | h∈T.placements ∧ (h '' Q∩featureGraphAt g r).Nonempty}
  have hJ : J.Finite := local_finiteness Q_object T.toPacking _ (graph_compact g r)
  letI : Fintype J := hJ.fintype
  let E : Set E3 := ⋃h : J,h.val '' nativeVertices
  have hE : E.Finite := Set.finite_iUnion fun h : J => nativeVertices_finite.image h.val
    -- API?: finite_iUnion over a finite index type for finite sets.
  let D : FeatureEdgeKind → Set E3 := fun kind => genericEdgesOfKindAt g r kind\E
  refine ⟨D,fun _ _ h => h.1,graph_delete_finite g r E hE,?_⟩
  intro kind x hx
  have hxroot : x∈genericEdgesOfKindAt g r kind := hx.1
  have hxgraph := generic_subset_graph g r kind hxroot
  have hxrootQ := graph_in_tile g r hxgraph
  have hJmem (h : RigidMotion) (hh : h∈T.placements) (hxh : x∈h '' Q) :
      h∈J := ⟨hh,x,hxh,hxgraph⟩
  let I : Finset RigidMotion := hJ.toFinset.filter (fun h => x∈h '' Q)
  have hI (h : RigidMotion) : h∈I ↔ h∈T.placements ∧ x∈h '' Q := by
    simp only [I,Finset.mem_filter,Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hj,hx⟩; exact ⟨hj.1,hx⟩
    · rintro ⟨hh,hx⟩; exact ⟨hJmem h hh hx,hx⟩
  have hiRoot : g∈I := (hI g).mpr ⟨hg,hxrootQ⟩
  have hfront (h : RigidMotion) (hh : h∈I) : x∈frontier (h '' Q) := by
    by_cases he : h=g
    · subst h
      change x ∈ frontier (g.toHomeomorph '' Q) -- [compile-fix: expose the homeomorphism coercion]
      rw [←g.toHomeomorph.image_frontier]
      exact Set.image_mono (hdihedral.1 r).1 hxgraph
    · exact neighbor_frontier T hg ((hI h).mp hh).1 (Ne.symm he)
        hxrootQ ((hI h).mp hh).2
  have hnotV (h : RigidMotion) (hh : h∈I) : h.symm x∉nativeVertices := by
    intro hv
    apply hx.2
    exact Set.mem_iUnion.mpr ⟨⟨h,hJmem h ((hI h).mp hh).1 ((hI h).mp hh).2⟩,
      h.symm x,hv,h.apply_symm_apply x⟩
  have hnative (h : RigidMotion) (hh : h∈I) :
      ∃L : SectorLabel,
        (∀k s,L=.feature k s → x∈genericEdgesOfKindAt h s k) ∧
        solidAngle (tangentCone (h '' Q) x)=ENNReal.ofReal (2*L.angle) := by
    have hb := hfront h hh
    change x ∈ frontier (h.toHomeomorph '' Q) at hb -- [compile-fix: expose the homeomorphism coercion]
    rw [←h.toHomeomorph.image_frontier] at hb
    have hn : h.symm x∈frontier Q := by
      obtain ⟨y,hy,he⟩ := hb
      simpa [←he] using hy
    obtain ⟨L,hL,ha⟩ := native_boundary_strata hdihedral _ hn (hnotV h hh)
    refine ⟨L,?_,?_⟩
    · intro k s he
      exact ⟨h.symm x,hL k s he,h.apply_symm_apply x⟩
    · rw [solidAngle_placed]; exact ha
  let pick (h : RigidMotion) : SectorLabel :=
    if hh : h∈I then Classical.choose (hnative h hh) else .ordinary 0
  have hpick (h : RigidMotion) (hh : h∈I) :
      (∀k s,pick h=.feature k s → x∈genericEdgesOfKindAt h s k) ∧
      solidAngle (tangentCone (h '' Q) x)=ENNReal.ofReal (2*(pick h).angle) := by
    simpa [pick,hh] using Classical.choose_spec (hnative h hh)
  let lab (h : RigidMotion) : SectorLabel := if h=g then .feature kind r else pick h
  refine ⟨{
    incident := I
    incident_iff := hI
    label := lab
    feature_location := ?_
    root_mem := hiRoot
    root_label := by simp [lab]
    angle_semantics := ?_
  }⟩
  · intro h hh k s he
    by_cases hhg : h=g
    · subst h
      have he' : kind=k ∧ r=s := by simpa [lab] using he
      rcases he' with ⟨rfl,rfl⟩
      exact hxroot
    · exact (hpick h hh).1 k s (by simpa [lab,hhg] using he)
  · intro h hh
    by_cases hhg : h=g
    · subst h
      simpa [lab] using placed_feature_angle hdihedral g r kind hxroot
    · simpa [lab,hhg] using (hpick h hh).2

/-- Unchanged derived conversion. The angle sum is not a stratum premise. -/
def BoundaryLabels.toSectorPacket (hbudget:ConeSectorBudgets Q)
    (hdihedral:CompleteDihedralList Q)
    {T:Tiling Q} {g:RigidMotion} {r:Role} {kind:FeatureEdgeKind} {x:E3}
    (b:BoundaryLabels T g r kind x) : SectorPacket T g r kind x where
  incident := b.incident
  incident_iff := b.incident_iff
  label := b.label
  feature_location := b.feature_location
  root_mem := b.root_mem
  root_label := b.root_label
  angle_sum := DischargeConeMeasure.incident_angle_sum hbudget hdihedral T x
    b.incident b.incident_iff b.label b.angle_semantics

end
end R44.DischargeSectors
