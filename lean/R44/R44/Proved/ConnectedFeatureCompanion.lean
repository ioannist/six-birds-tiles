/- -- [compile-fix]
# Discharge: connected_feature_companion

Written proof: A-L4.1 and A-T4.2 of proof/ALIGNMENT_PROOF.md. The finite
closed-cover argument includes feature vertices and needs no face-to-face
assumption. No ERRATA changes that argument.

The triple-contact bound uses the already proved F2 open circular cones,
not an unproved equality between volumes of a tangent cone and its interior.
The frozen UniformFeatureSolidAngle premise is retained verbatim but this
stronger local inclusion makes it unnecessary in the proof.
No MeshSemantics or GenericFeaturePartner discharge file is imported: the
frozen generic-partner premise is used as supplied. No admissions.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.FeatureGraphTopology -- [compile-fix]
import R44.Proved.FeatureCircularConeContainment -- [compile-fix]
import R44.Proved.CircularConeSolidAngle -- [compile-fix]

namespace R44.DischargeFeatureGraphs
open Set MeasureTheory
noncomputable section
set_option maxHeartbeats 0 -- [compile-fix]

private theorem three_disjoint_caps_impossible (A : Fin 3 → E3 ≃ₗᵢ[ℝ] E3)
    (hd : Pairwise (fun i j => Disjoint
      (A i '' circularCone (3/25)) (A j '' circularCone (3/25)))) : False := by
  let C (i : Fin 3) := A i '' circularCone (3/25) ∩ Metric.closedBall (0 : E3) 1
  have hc (i : Fin 3) : MeasurableSet (C i) :=
    ((A i).toHomeomorph.isOpenMap _ (circularCone_isOpen _)).measurableSet.inter
      measurableSet_closedBall
  have hcd : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij; exact (hd hij).mono inter_subset_left inter_subset_left
  have hsum : ∑ i : Fin 3, volume (C i) ≤
      volume (Metric.closedBall (0 : E3) 1) := by
    have heq : volume (⋃i:Fin 3,C i)=∑i:Fin 3,volume (C i) := by
      simpa only [tsum_fintype] using measure_iUnion hcd (fun i => hc i)
      -- API?: measure_iUnion for pairwise-disjoint measurable sets; tsum_fintype.
    rw [← heq]
    apply measure_mono
    exact Set.iUnion_subset fun _ => inter_subset_right
  have hangle (i : Fin 3) : 3*volume (C i) =
      ENNReal.ofReal (coneAngle (3/25)) := by
    calc
      _ = solidAngle (A i '' circularCone (3/25)) := rfl
      _ = solidAngle (circularCone (3/25)) := solidAngle_linearIsometry_image _ _
      _ = _ := circular_cone_solid_angle_holds
  have hball : 3*volume (Metric.closedBall (0 : E3) 1) =
      ENNReal.ofReal (4*Real.pi) := by
    rw [EuclideanSpace.volume_closedBall_fin_three]
    -- API?: expected formula for the Euclidean 3-ball: ofReal r^3*(4/3)*ofReal π.
    norm_num only [ENNReal.ofReal_one,one_pow,one_mul] -- [compile-fix begin: normalize ENNReal rational factors]
    rw [show Real.pi*4/3=4/3*Real.pi by ring,
      ENNReal.ofReal_mul (by positivity : (0:Real)≤4/3),
      ENNReal.ofReal_mul (by positivity : (0:Real)≤4)]
    norm_num only [ENNReal.ofReal_ofNat]
    have hnum : (3:ENNReal)*ENNReal.ofReal (4/3:Real)=4 := by
      rw [ENNReal.ofReal_eq_coe_nnreal (by positivity : (0:Real)≤4/3)]
      norm_cast
      apply NNReal.eq
      norm_num
    calc
      3*(ENNReal.ofReal (4/3:Real)*ENNReal.ofReal Real.pi)=
          (3*ENNReal.ofReal (4/3:Real))*ENNReal.ofReal Real.pi := by ring
      _=4*ENNReal.ofReal Real.pi := by rw [hnum]
    -- [compile-fix end]
  have hs := mul_le_mul_left' hsum (3 : ENNReal)
  rw [Finset.mul_sum,Fin.sum_univ_succ] at hs
  simp only [Fin.sum_univ_succ,Finset.sum_empty,add_zero,hangle,hball] at hs
  have hp : 4*Real.pi/3 < coneAngle (3/25) :=
    (coneAngle_gt_four_pi_div_three_iff (by norm_num : (0:ℝ)≤3/25)).mpr
      (by norm_num)
  have hcp : 0≤coneAngle (3/25) := by linarith [Real.pi_pos]
  have hreal : 3*coneAngle (3/25) ≤ 4*Real.pi := by
    have heq : ENNReal.ofReal (coneAngle (3/25)) +
        ENNReal.ofReal (coneAngle (3/25)) + ENNReal.ofReal (coneAngle (3/25)) =
        ENNReal.ofReal (3*coneAngle (3/25)) := by
      rw [← ENNReal.ofReal_add hcp hcp,← ENNReal.ofReal_add (by positivity) hcp]
      congr 1; ring
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0≤4*Real.pi)).mp
      -- API?: ofReal order cancellation with nonnegative RHS.
    simpa [← add_assoc,heq] using hs
  linarith

/-- No point can belong to feature graphs of three distinct placed tiles.
The cone interiors supplied by F2 are open measurable sets. -/
theorem no_three_feature_tiles (hbudget : ConeSectorBudgets Q) (T : Tiling Q)
    {g h k : RigidMotion} (hg : g∈T.placements) (hh : h∈T.placements)
    (hk : k∈T.placements) (hgh : g≠h) (hgk : g≠k) (hhk : h≠k)
    (r s t : Role) (x : E3) (hxg : x∈featureGraphAt g r)
    (hxh : x∈featureGraphAt h s) (hxk : x∈featureGraphAt k t) : False := by
  obtain ⟨A,hA⟩ := feature_circular_cone_containment_holds T g hg r x hxg
  obtain ⟨B,hB⟩ := feature_circular_cone_containment_holds T h hh s x hxh
  obtain ⟨C,hC⟩ := feature_circular_cone_containment_holds T k hk t x hxk
  have hb := (hbudget T x).2.1
  have hAB := (hb hg hh (graph_in_tile g r hxg) (graph_in_tile h s hxh) hgh).mono hA hB
  have hAC := (hb hg hk (graph_in_tile g r hxg) (graph_in_tile k t hxk) hgk).mono hA hC
  have hBC := (hb hh hk (graph_in_tile h s hxh) (graph_in_tile k t hxk) hhk).mono hB hC
  apply three_disjoint_caps_impossible ![A,B,C]
  intro i j hij
  fin_cases i <;> fin_cases j <;> -- [compile-fix begin: include symmetry of Disjoint]
    simp_all [Matrix.cons_val_zero,Matrix.cons_val_one,disjoint_comm]
  -- [compile-fix end]

/-- A dense family of generic partners closes to one whole-feature companion. -/
theorem whole_from_generic
    (hlf : EveryPackingLocallyFinite Q) (hbudget : ConeSectorBudgets Q)
    (hgeneric : GenericFeaturePartners Q) : WholeFeatureCompanions Q := by
  classical
  intro T g hg r
  let E := featureGraphAt g r
  let J : Set RigidMotion :=
    {h | h∈T.placements ∧ h≠g ∧ (h '' Q ∩ E).Nonempty}
  have hJ : J.Finite := by
    apply (hlf T.toPacking E (graph_compact g r)).subset
    intro h hh; exact ⟨hh.1,hh.2.2⟩
  letI : Fintype J := hJ.fintype
  let C (h : J) := E ∩ ⋃ s : Role, featureGraphAt h.1 s
  have hclosed (h : J) : IsClosed (C h) :=
    (graph_closed g r).inter -- [compile-fix begin: Role is finite, not Alexandrov-discrete]
      (isClosed_iUnion_of_finite fun s => graph_closed h.1 s)
    -- [compile-fix end]
  obtain ⟨D,hDsub,hDclosure,hDpartner⟩ := hgeneric T g hg r
  have hDcover : D .base ∪ D .ridge ⊆ ⋃ h : J,C h := by
    intro x hx
    have hex : ∃ kind, x∈D kind := by
      rcases hx with hx | hx
      · exact ⟨.base,hx⟩
      · exact ⟨.ridge,hx⟩
    obtain ⟨kind,hxD⟩ := hex
    obtain ⟨⟨h,s⟩,hhs,_⟩ := hDpartner kind x hxD
    have hxE : x∈E := generic_subset_graph g r kind (hDsub kind hxD)
    have hxhs : x∈featureGraphAt h s := generic_subset_graph h s kind hhs.2.2.1
    have hj : h∈J := ⟨hhs.1,hhs.2.1,x,graph_in_tile h s hxhs,hxE⟩
    exact Set.mem_iUnion.mpr ⟨⟨h,hj⟩,hxE,Set.mem_iUnion.mpr ⟨s,hxhs⟩⟩
  have hcover : E ⊆ ⋃ h : J,C h := by
    change closure (D .base ∪ D .ridge) = E at hDclosure -- [compile-fix]
    rw [← hDclosure]
    exact closure_minimal hDcover -- [compile-fix begin: J is finite]
      (isClosed_iUnion_of_finite hclosed)
    -- [compile-fix end]
  have hdisj : ∀ h k : J, h≠k → Disjoint (E∩C h) (E∩C k) := by
    intro h k hne
    rw [Set.disjoint_left]
    rintro x ⟨hxE,_,hxh⟩ ⟨_,_,hxk⟩
    obtain ⟨s,hxs⟩ := Set.mem_iUnion.mp hxh
    obtain ⟨t,hxt⟩ := Set.mem_iUnion.mp hxk
    have hv : h.1≠k.1 := by intro he; exact hne (Subtype.ext he)
    exact no_three_feature_tiles hbudget T hg h.2.1 k.2.1
      (Ne.symm h.2.2.1) (Ne.symm k.2.2.1) hv r s t x hxE hxs hxt
  obtain ⟨h,heh⟩ := connected_finite_closed_cover (graph_connected g r) C hclosed hcover hdisj
  have hcovered : FeatureCoveredByTile g r h.1 := fun x hx => (heh hx).2
  have hrolesdisj : ∀ s t : Role, s≠t →
      Disjoint (E∩featureGraphAt h.1 s) (E∩featureGraphAt h.1 t) := by
    intro s t hst
    exact (graph_roles_disjoint h.1 hst).mono inter_subset_right inter_subset_right
  obtain ⟨s,hes⟩ := connected_finite_closed_cover (graph_connected g r)
    (featureGraphAt h.1) (graph_closed h.1) hcovered hrolesdisj
  refine ⟨h.1,h.2.1,h.2.2.1,hcovered,⟨s,hes⟩,?_⟩
  intro k hk hkg hkcover
  by_contra hkh
  obtain ⟨x,hx⟩ := (graph_connected g r).nonempty
  obtain ⟨t,hxt⟩ := Set.mem_iUnion.mp (hkcover hx)
  exact no_three_feature_tiles hbudget T hg h.2.1 hk
    (Ne.symm h.2.2.1) (Ne.symm hkg) (Ne.symm hkh) r s t x hx (hes hx) hxt

end
end R44.DischargeFeatureGraphs

namespace R44
noncomputable section
/-- Frozen field proposition, with no new hypothesis. -/
theorem connected_feature_companion_holds :
    EveryPackingLocallyFinite Q → ConeSectorBudgets Q → GenericFeaturePartners Q →
      UniformFeatureSolidAngle Q → WholeFeatureCompanions Q := by
  intro hlf hbudget hgeneric _hangle
  exact DischargeFeatureGraphs.whole_from_generic hlf hbudget hgeneric
end
end R44
