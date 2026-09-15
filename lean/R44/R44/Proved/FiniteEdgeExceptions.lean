/- -- [compile-fix: promoted to Proved after exchange 7]
# Finite exceptional points do not remove density on a feature graph

A-L2.2/A-L3.2. This is a general interval argument, not a certificate
about a particular tiling. Nondegenerate edges are essential. It removes
an arbitrary finite set, including vertices of ALL tiles meeting the root.
No boundary-stratification or mesh/volume theorem is used here.
-/
import R44.Proved.FeatureGraphTopology -- [compile-fix]

namespace R44.DischargeEdgeDensity
open Set Filter DischargeFeatureGraphs DischargeGeometry DischargeCharts
open scoped Topology
noncomputable section
set_option maxRecDepth 1000000 -- [compile-fix]
set_option maxHeartbeats 0 -- [compile-fix]

private def lerp (a b : E3) (t : ℝ) : E3 := (1-t) • a+t • b

private theorem lerp_injective {a b : E3} (hab : a≠b) :
    Function.Injective (lerp a b) := by
  intro s t he
  have hz : (s-t) • (b-a)=0 := by
    calc
      _ = lerp a b s-lerp a b t := by dsimp [lerp]; module
      _ = 0 := sub_eq_zero.mpr he
  have hn : b-a≠0 := sub_ne_zero.mpr (Ne.symm hab)
  have hst : s-t=0 := (smul_eq_zero.mp hz).resolve_right hn
  exact sub_eq_zero.mp hst

private theorem interval_delete_finite (F : Set ℝ) (hF : F.Finite) :
    closure (Ioo (0:ℝ) 1\F)=Icc (0:ℝ) 1 := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ h => ⟨h.1.1.le,h.1.2.le⟩) isClosed_Icc
  · intro t ht
    rw [Metric.mem_closure_iff]
    intro eps heps
    let d : ℝ := min (eps/2) (1/4)
    let l : ℝ := max 0 (t-d)
    let u : ℝ := min 1 (t+d)
    have hd : 0<d := lt_min (half_pos heps) (by norm_num)
    have hlu : l<u := by
      dsimp [l,u]
      rw [max_lt_iff,lt_min_iff,lt_min_iff]
      constructor
      · exact ⟨by norm_num,by linarith [ht.1]⟩
      · exact ⟨by linarith [ht.2],by linarith⟩
    have hinf : (Ioo l u).Infinite := Set.Ioo_infinite hlu
      -- API?: a nonempty real open interval is infinite; expected
      -- Set.Ioo_infinite (l<u), possibly namespace Set.Ioo.infinite.
    obtain ⟨s,hs,hout⟩ := hinf.exists_notMem_finite hF -- [compile-fix]
      -- API?: Infinite.exists_not_mem_finite chooses a point outside F.
    refine ⟨s,⟨?_,hout⟩,?_⟩
    · exact ⟨lt_of_le_of_lt (le_max_left _ _) hs.1,
        lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
    · have hlo := lt_of_le_of_lt (le_max_right 0 (t-d)) hs.1
      have hhi := lt_of_lt_of_le hs.2 (min_le_right 1 (t+d))
      rw [Real.dist_eq,abs_lt]
      have hde : d≤eps/2 := min_le_left _ _
      constructor <;> linarith

/-- Endpoint-inclusive density follows from continuous parametrization.
No ambient-interior claim about a line segment is used. -/
theorem segment_delete_finite {a b : E3} (hab : a≠b)
    (F : Set E3) (hF : F.Finite) :
    closure (openSegment ℝ a b\F)=segment ℝ a b := by
  have hf : Continuous (lerp a b) := by -- [compile-fix]
    change Continuous (fun t : ℝ => (1-t) • a+t • b)
    fun_prop
  have hpre : ((lerp a b) ⁻¹' F).Finite :=
    hF.preimage (Set.injOn_of_injective (lerp_injective hab)) -- [compile-fix]
  have hopen : lerp a b '' (Ioo (0:ℝ) 1\(lerp a b) ⁻¹' F)=
      openSegment ℝ a b\F := by
    ext x
    constructor
    · rintro ⟨t,⟨ht,hF⟩,rfl⟩
      exact ⟨⟨1-t,t,by linarith [ht.2],ht.1,by ring,rfl⟩,hF⟩
    · rintro ⟨⟨s,t,hs,ht,hst,hx⟩,hF⟩
      refine ⟨t,⟨⟨ht,by linarith⟩,?_⟩,?_⟩
      · simpa [lerp,show 1-t=s by linarith,hx] using hF
      · simpa [lerp,show 1-t=s by linarith] using hx
  have hclosed : lerp a b '' Icc (0:ℝ) 1=segment ℝ a b := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨1-t,t,by linarith [ht.2],ht.1,by ring,rfl⟩
    · rintro ⟨s,t,hs,ht,hst,hx⟩
      exact ⟨t,⟨ht,by linarith⟩,by simpa [lerp,show 1-t=s by linarith] using hx⟩
  apply Set.Subset.antisymm
  · exact closure_minimal (fun x hx => openSegment_subset_segment ℝ a b hx.1)
      (by -- [compile-fix begin: compactness via the delivered parametrization]
        rw [← hclosed]
        exact (isCompact_Icc.image hf).isClosed) -- [compile-fix end]
  · rw [←hclosed,←interval_delete_finite _ hpre]
    have hcont := image_closure_subset_closure_image
      (s := Ioo (0:ℝ) 1\(lerp a b) ⁻¹' F) hf -- [compile-fix]
      -- API?: continuous f gives f '' closure S ⊆ closure (f '' S).
    simpa only [hopen] using hcont

private theorem endpoints_distinct (r : Role) (kind : FeatureEdgeKind) (k : Fin 4) :
    featureCorner r k≠(match kind with
      | .base => featureCorner r (nextCorner k)
      | .ridge => featureApex r) := by
  have hu (j : Fin 4) : chartU r (featureCorner r j) =
      (if j.val = 0 ∨ j.val = 1 then -1 else 1) * eta := by
    rw [show featureCorner r j = chartPoint r
      ((if j.val = 0 ∨ j.val = 1 then -1 else 1) * eta)
      ((if j.val = 0 ∨ j.val = 3 then -1 else 1) * eta) 0 by
        simp [featureCorner,chartPoint]]
    simp -- [compile-fix]
  have hv (j : Fin 4) : chartV r (featureCorner r j) =
      (if j.val = 0 ∨ j.val = 3 then -1 else 1) * eta := by
    rw [show featureCorner r j = chartPoint r
      ((if j.val = 0 ∨ j.val = 1 then -1 else 1) * eta)
      ((if j.val = 0 ∨ j.val = 3 then -1 else 1) * eta) 0 by
        simp [featureCorner,chartPoint]]
    simp -- [compile-fix]
  have hua : chartU r (featureApex r) = 0 := by
    rw [show featureApex r = chartPoint r 0 0
      ((profileCoefficient r : ℝ)/10000) by simp [featureApex,chartPoint]]
    simp -- [compile-fix]
  have hva : chartV r (featureApex r) = 0 := by
    rw [show featureApex r = chartPoint r 0 0
      ((profileCoefficient r : ℝ)/10000) by simp [featureApex,chartPoint]]
    simp -- [compile-fix]
  intro he
  have hU := congrArg (chartU r) he
  have hV := congrArg (chartV r) he
  cases kind
  · fin_cases k
    · simp only [hu,hv] at hU hV; norm_num [nextCorner,eta] at hV
    · simp only [hu,hv] at hU hV; norm_num [nextCorner,eta] at hU
    · simp only [hu,hv] at hU hV; norm_num [nextCorner,eta] at hV
    · simp only [hu,hv] at hU hV; norm_num [nextCorner,eta] at hU
  · fin_cases k <;> simp only [hu,hv,hua,hva] at hU hV <;>
      norm_num [eta] at hU -- [compile-fix]
    -- Coordinate identities for the already proved orthogonal native chart
    -- can replace this simp list without changing the geometric assertion.

/-- Remove a finite set from every open native edge, in an arbitrary pose. -/
theorem graph_delete_finite (g : RigidMotion) (r : Role)
    (F : Set E3) (hF : F.Finite) :
    closure ((genericEdgesOfKindAt g r .base\F)∪
      (genericEdgesOfKindAt g r .ridge\F))=featureGraphAt g r := by
  let D := (genericEdgesOfKindAt g r .base\F)∪
    (genericEdgesOfKindAt g r .ridge\F)
  have hsub : D⊆featureGraphAt g r := by
    rintro x (h|h)
    · exact generic_subset_graph g r .base h.1
    · exact generic_subset_graph g r .ridge h.1
  apply Set.Subset.antisymm
  · exact closure_minimal hsub (graph_closed g r)
  · rintro x ⟨y,hy,rfl⟩
    rcases hy with hy|hy
    all_goals
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hy
    · have hc := segment_delete_finite
        (fun he => endpoints_distinct r .base k (g.injective he)) F hF
      have hx : g y∈segment ℝ (g (featureCorner r k))
          (g (featureCorner r (nextCorner k))) := by
        have hi : g.toAffineEquiv y ∈
            g.toAffineEquiv.toAffineMap '' segment ℝ (featureCorner r k)
              (featureCorner r (nextCorner k)) := ⟨y,hk,rfl⟩
        rw [image_segment] at hi
        exact hi -- [compile-fix]
        -- API?: AffineIsometryEquiv.image_segment preserves real segments.
      rw [←hc] at hx
      refine closure_mono ?_ hx
      intro z hz -- [compile-fix]
      have hz' : z ∈ g.toAffineEquiv.toAffineMap '' openSegment ℝ
          (featureCorner r k) (featureCorner r (nextCorner k)) := by
        rw [image_openSegment]
        exact hz.1 -- [compile-fix]
      obtain ⟨w,hw,hwz⟩ := hz'
      exact Or.inl ⟨⟨w,Set.mem_iUnion.mpr ⟨k,hw⟩,hwz⟩,hz.2⟩
    · have hc := segment_delete_finite
        (fun he => endpoints_distinct r .ridge k (g.injective he)) F hF
      have hx : g y∈segment ℝ (g (featureCorner r k)) (g (featureApex r)) := by
        have hi : g.toAffineEquiv y ∈
            g.toAffineEquiv.toAffineMap '' segment ℝ (featureCorner r k)
              (featureApex r) := ⟨y,hk,rfl⟩
        rw [image_segment] at hi
        exact hi -- [compile-fix]
      rw [←hc] at hx
      refine closure_mono ?_ hx
      intro z hz -- [compile-fix]
      have hz' : z ∈ g.toAffineEquiv.toAffineMap '' openSegment ℝ
          (featureCorner r k) (featureApex r) := by
        rw [image_openSegment]
        exact hz.1 -- [compile-fix]
      obtain ⟨w,hw,hwz⟩ := hz'
      exact Or.inr ⟨⟨w,Set.mem_iUnion.mpr ⟨k,hw⟩,hwz⟩,hz.2⟩

end
end R44.DischargeEdgeDensity
