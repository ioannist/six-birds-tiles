/- -- [compile-fix]
# Closed connected feature graphs and finite closed covers

Written source: proof/ALIGNMENT_PROOF.md A-T4.2 and A-L4.3, with ERRATA E1.
Only the concrete segment graphs are used. The finite closed-cover lemma is
proved for an arbitrary finite family; it is not a disguised companion
assumption. Native frontier membership comes from NativeGeometry, not from
an admitted mesh/volume bridge.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.FeatureLocalCharts -- [compile-fix]

namespace R44.DischargeFeatureGraphs
open Set R44.DischargeGeometry R44.DischargeCharts
noncomputable section

/-- Generic strata sit in the closed feature graph. -/
theorem native_generic_subset_graph (r : Role) (kind : FeatureEdgeKind) :
    nativeGenericEdgesOfKind r kind ⊆ nativeFeatureGraph r := by
  intro x hx
  cases kind with
  | base =>
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      exact Or.inl (Set.mem_iUnion.mpr ⟨k,openSegment_subset_segment ℝ _ _ hk⟩)
      -- API?: expected openSegment_subset_segment ℝ a b.
  | ridge =>
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨k,openSegment_subset_segment ℝ _ _ hk⟩)

theorem generic_subset_graph (g : RigidMotion) (r : Role) (kind : FeatureEdgeKind) :
    genericEdgesOfKindAt g r kind ⊆ featureGraphAt g r :=
  Set.image_mono (native_generic_subset_graph r kind)

theorem native_graph_compact (r : Role) : IsCompact (nativeFeatureGraph r) := by
  have hsegment (a b : E3) : IsCompact (segment ℝ a b) := by -- [compile-fix]
    rw [segment_eq_image] -- [compile-fix]
    exact isCompact_Icc.image (by fun_prop) -- [compile-fix]
  exact (isCompact_iUnion fun k : Fin 4 => hsegment -- [compile-fix]
    (featureCorner r k) (featureCorner r (nextCorner k))).union
    (isCompact_iUnion fun k : Fin 4 => hsegment -- [compile-fix]
      (featureCorner r k) (featureApex r))
  -- API?: isCompact_iUnion for a finite family; isCompact_segment endpoints.

theorem graph_compact (g : RigidMotion) (r : Role) :
    IsCompact (featureGraphAt g r) := (native_graph_compact r).image g.continuous

theorem graph_closed (g : RigidMotion) (r : Role) :
    IsClosed (featureGraphAt g r) := (graph_compact g r).isClosed

theorem apex_mem_graph (r : Role) : featureApex r ∈ nativeFeatureGraph r := by
  exact Or.inr (Set.mem_iUnion.mpr ⟨0,right_mem_segment ℝ _ _⟩)

theorem corner_mem_graph (r : Role) (k : Fin 4) :
    featureCorner r k ∈ nativeFeatureGraph r := by
  exact Or.inr (Set.mem_iUnion.mpr ⟨k,left_mem_segment ℝ _ _⟩)

/-- Every point joins the apex along one or two graph segments. In
particular this is graph connectedness, not connectedness of its filled hull. -/
theorem native_graph_connected (r : Role) : IsConnected (nativeFeatureGraph r) := by
  refine ⟨⟨featureApex r,apex_mem_graph r⟩,?_⟩
  apply isPreconnected_of_forall (featureApex r)
  -- API?: isPreconnected_of_forall x: each point joins x in a preconnected subset.
  intro y hy
  rcases hy with hy | hy
  · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hy
    let B := segment ℝ (featureCorner r k) (featureCorner r (nextCorner k))
    let R := segment ℝ (featureCorner r k) (featureApex r)
    refine ⟨B∪R,?_,Or.inr (right_mem_segment ℝ _ _),Or.inl hk,?_⟩
    · intro x hx; rcases hx with hx | hx
      · exact Or.inl (Set.mem_iUnion.mpr ⟨k,hx⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨k,hx⟩)
    · exact IsPreconnected.union (featureCorner r k)
        (left_mem_segment ℝ _ _) (left_mem_segment ℝ _ _)
        (convex_segment _ _).isPreconnected (convex_segment _ _).isPreconnected
        -- API?: IsPreconnected.union x hx hy hs ht; Convex.isPreconnected.
  · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hy
    refine ⟨segment ℝ (featureCorner r k) (featureApex r),?_,
      right_mem_segment ℝ _ _,hk,(convex_segment _ _).isPreconnected⟩
    intro x hx; exact Or.inr (Set.mem_iUnion.mpr ⟨k,hx⟩)

theorem graph_connected (g : RigidMotion) (r : Role) :
    IsConnected (featureGraphAt g r) :=
  (native_graph_connected r).image g g.continuous.continuousOn

theorem native_graph_in_Q (r : Role) : nativeFeatureGraph r ⊆ Q := by
  intro x hx
  have h := graph_coordinates r hx
  have hb := featureHeight_abs_bound r x
  have ht : featureTubeSupport r x := by
    refine ⟨h.1,?_⟩
    rw [h.2]
    exact hb.trans (by norm_num [eta])
  exact (mem_Q_iff_in_tube r x ht).mpr h.2.le

theorem graph_in_tile (g : RigidMotion) (r : Role) :
    featureGraphAt g r ⊆ g '' Q := Set.image_mono (native_graph_in_Q r)

theorem native_graph_in_support (r : Role) :
    nativeFeatureGraph r ⊆ {x | featureTubeSupport r x} := by
  intro x hx
  have h := graph_coordinates r hx
  refine ⟨h.1,?_⟩
  rw [h.2]
  exact (featureHeight_abs_bound r x).trans (by norm_num [eta])

/-- Different native roles cannot intersect in the same tile. -/
theorem graph_roles_disjoint (g : RigidMotion) {r s : Role} (hrs : r ≠ s) :
    Disjoint (featureGraphAt g r) (featureGraphAt g s) := by
  rw [Set.disjoint_left]
  rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
  have huv : u=v := g.injective (hux.trans hvx.symm)
  subst v
  exact Set.disjoint_left.mp (featureTubeSupports_pairwiseDisjoint r s hrs)
    (native_graph_in_support r hu) (native_graph_in_support s hv)

/-- The closed-cover step of A-T4.2, including exceptional vertices.
The intersections with E, not necessarily the ambient sets, are disjoint. -/
theorem connected_finite_closed_cover {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Finite ι] {E : Set X} (hE : IsConnected E)
    (C : ι → Set X) (hclosed : ∀ i, IsClosed (C i))
    (hcover : E ⊆ ⋃ i,C i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (E∩C i) (E∩C j)) :
    ∃ i, E ⊆ C i := by
  classical
  obtain ⟨x,hx⟩ := hE.nonempty
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover hx)
  refine ⟨i,?_⟩
  intro y hy
  by_contra hnyi
  let J := {j : ι // j ≠ i}
  let D : Set X := ⋃ j : J,C j.1
  have hDclosed : IsClosed D := isClosed_iUnion_of_finite fun j : J => hclosed j.1 -- [compile-fix]
    -- API?: isClosed_iUnion for a finite family.
  have hED : E ⊆ C i ∪ D := by
    intro z hz
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hcover hz)
    by_cases hji : j=i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)
  have hyD : y ∈ D := (hED hy).resolve_left hnyi
  have hxCi : (E∩C i).Nonempty := ⟨x,hx,hi⟩
  have hyDi : (E∩D).Nonempty := ⟨y,hy,hyD⟩
  obtain ⟨z,hzE,hzCi,hzD⟩ :=
    isPreconnected_closed_iff.mp hE.isPreconnected (C i) D
      (hclosed i) hDclosed hED hxCi hyDi
    -- API?: closed-set form of preconnectedness: intersecting both parts
    -- of a closed cover forces E∩C_i∩D nonempty.
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hzD
  exact Set.disjoint_left.mp (hdisj i j.1 (Ne.symm j.2)) ⟨hzE,hzCi⟩ ⟨hzE,hj⟩

end
end R44.DischargeFeatureGraphs
