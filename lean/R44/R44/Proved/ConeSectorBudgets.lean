/- -- [compile-fix]
# Discharge: cone_sector_budgets

Written proof: A-L2.2 of proof/ALIGNMENT_PROOF.md. No ERRATA changes this
lemma. The proof uses local finiteness, the exact locally conical germs of
finite affine predicates, closedness, and disjoint physical interiors.
It covers EVERY direction, including cone-boundary directions; it does not
replace coverage by coverage of the open cone interiors.

No dihedral/mesh-volume bridge is assumed, and no Hypotheses record is used.
The endpoint copies the frozen field proposition verbatim.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.PolyhedralGerms -- [compile-fix]

namespace R44.DischargePolyhedral
open Set Filter
open scoped Topology
noncomputable section

private def dilation (a : ℝ) (ha : a ≠ 0) : E3 ≃ₜ E3 where
  toFun := fun v => a • v
  invFun := fun v => a⁻¹ • v
  left_inv := by intro v; simp [smul_smul,ha]
  right_inv := by intro v; simp [smul_smul,ha]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem scaled_interior {C : Set E3}
    (hC : ∀ a : ℝ, 0<a → ∀ v : E3, a • v ∈ C ↔ v ∈ C)
    {a : ℝ} (ha : 0<a) {v : E3} (hv : v ∈ interior C) :
    a • v ∈ interior C := by
  let e := dilation a ha.ne'
  have he : e '' C = C := by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩; exact (hC a ha v).mpr hv
    · intro hw
      refine ⟨a⁻¹ • w,?_,?_⟩
      · exact (hC a⁻¹ (inv_pos.mpr ha) w).mpr hw
      · simp [e,dilation,smul_smul,ha.ne']
  rw [← he,← e.image_interior]
  exact ⟨v,hv,rfl⟩

/-- Uniform local conicality moves open direction sets into actual material
interiors. This is the needed strengthening of a pointwise ray statement. -/
private theorem model_interior_to_solid {S C : Set E3} {x u : E3} {δ : ℝ}
    (hg : ∀ v ∈ Metric.ball (0 : E3) δ, x+v ∈ S ↔ v ∈ C)
    (hu : u ∈ Metric.ball (0 : E3) δ) (hc : u ∈ interior C) :
    x+u ∈ interior S := by
  let e := (translation x).toHomeomorph
  let U := Metric.ball (0 : E3) δ ∩ interior C
  have hopen : IsOpen (e '' U) :=
    e.isOpenMap _ (Metric.isOpen_ball.inter isOpen_interior) -- [compile-fix]
  have hsub : e '' U ⊆ S := by
    rintro y ⟨v,⟨hv,hcv⟩,rfl⟩
    exact (hg v hv).mpr (interior_subset hcv)
  have hmem : x+u ∈ e '' U := ⟨u,⟨hu,hc⟩,by simp [e,translation]⟩
  exact (interior_maximal hsub hopen) hmem

/-- Closedness puts the cone base point in the solid. -/
theorem base_mem_of_tangent {S : Set E3} (hS : IsClosed S) {x v : E3}
    (hv : v ∈ tangentCone S x) : x ∈ S := by
  rcases hv with ⟨ε,hε,hseg⟩
  have hm : ∀ᶠ t in 𝓝[>] (0 : ℝ), x+t • v ∈ S := by
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t<ε :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hε) -- [compile-fix]
      -- API?: Iio_mem_nhds hε gives eventually t<ε at 0; restrict to the right.
    filter_upwards [self_mem_nhdsWithin,hsmall] with t ht hte
    exact hseg t ht hte
  have ht : Tendsto (fun t : ℝ => x+t • v) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x+t • v) := by fun_prop
    have hc0 : Tendsto (fun t : ℝ => x+t • v) (𝓝 (0 : ℝ)) -- [compile-fix]
        (𝓝 (x + (0 : ℝ) • v)) := hc.continuousAt -- [compile-fix]
    simpa using hc0.mono_left nhdsWithin_le_nhds -- [compile-fix]
  exact hS.mem_of_tendsto ht hm
  -- API?: IsClosed.mem_of_tendsto uses the nontrivial one-sided neighborhood filter.

/-- Actual packing disjointness induces disjoint INTERIORS of the radial
cones; shared boundary directions remain permitted. -/
theorem placed_tangent_interiors_disjoint (T : Tiling Q)
    {g h : RigidMotion} (hg : g ∈ T.placements) (hh : h ∈ T.placements)
    (hne : g ≠ h) (x : E3) :
    Disjoint (interior (tangentCone (g '' Q) x))
      (interior (tangentCone (h '' Q) x)) := by
  obtain ⟨C,hC,hgerm⟩ := Q_placed_localCone g x
  obtain ⟨D,hD,hhgerm⟩ := Q_placed_localCone h x
  rw [LocalCone.tangent_eq hC hgerm,LocalCone.tangent_eq hD hhgerm]
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hgerm
  obtain ⟨ε,hε,heball⟩ := Metric.mem_nhds_iff.mp hhgerm
  rw [Set.disjoint_left]
  intro v hvC hvD
  let t := min δ ε / (2*(‖v‖+1))
  have ht : 0<t := div_pos (lt_min hδ hε) (by positivity)
  have hnorm : ‖t • v‖ < min δ ε := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have heq : t*(2*(‖v‖+1))=min δ ε := by
      dsimp [t]; field_simp
    nlinarith [norm_nonneg v,lt_min hδ hε]
  have huC : t • v ∈ Metric.ball (0 : E3) δ := by
    simpa [Metric.mem_ball,dist_zero_right] using hnorm.trans_le (min_le_left _ _)
  have huD : t • v ∈ Metric.ball (0 : E3) ε := by
    simpa [Metric.mem_ball,dist_zero_right] using hnorm.trans_le (min_le_right _ _)
  have hiC := model_interior_to_solid (S:=g '' Q) (x:=x)
    (fun v hv => hball hv) huC (scaled_interior hC ht hvC)
  have hiD := model_interior_to_solid (S:=h '' Q) (x:=x)
    (fun v hv => heball hv) huD (scaled_interior hD ht hvD)
  exact Set.disjoint_left.mp (T.disjoint_interiors hg hh hne) hiC hiD

/-- Every direction belongs to one incident cone, with a finite common
neighborhood. No improper pigeonhole argument over infinitely many tiles. -/
private theorem cones_cover (hlf : EveryPackingLocallyFinite Q)
    (T : Tiling Q) (x v : E3) :
    ∃ g : RigidMotion, g ∈ T.placements ∧ x ∈ g '' Q ∧
      v ∈ tangentCone (g '' Q) x := by
  classical
  let J : Set RigidMotion :=
    {g | g ∈ T.placements ∧ (g '' Q ∩ Metric.closedBall x 1).Nonempty}
  have hJ : J.Finite := hlf T.toPacking _ (isCompact_closedBall x 1)
  letI : Fintype J := hJ.fintype
  have hcharts : ∀ j : J, LocalCone (j.1 '' Q) x :=
    fun j => Q_placed_localCone j.1 x
  choose C hC hG using hcharts
  have hgerms : ∀ᶠ u in 𝓝 (0 : E3), ∀ j : J,
      x+u ∈ j.1 '' Q ↔ u ∈ C j :=
    (Filter.eventually_all).mpr hG
  have hneighborhood : ∀ᶠ u in 𝓝 (0 : E3),
      ‖u‖<1 ∧ ∀ j : J, x+u ∈ j.1 '' Q ↔ u ∈ C j := by
    filter_upwards [hgerms,Metric.ball_mem_nhds (0 : E3) (by norm_num : (0:ℝ)<1)]
      with u hu hb
    exact ⟨by simpa [Metric.mem_ball,dist_zero_right] using hb,hu⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  let t := δ/(2*(‖v‖+1))
  have ht : 0<t := div_pos hδ (by positivity)
  have hsmall : t • v ∈ Metric.ball (0 : E3) δ := by
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have heq : t*(2*(‖v‖+1))=δ := by dsimp [t]; field_simp
    nlinarith [norm_nonneg v]
  have hgood := hball hsmall
  obtain ⟨g,hg,hcover⟩ := T.covers (x+t • v)
  have gj : g ∈ J := by
    refine ⟨hg,x+t • v,hcover,?_⟩
    simpa [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left] using hgood.1.le
  let j : J := ⟨g,gj⟩
  have hvC : v ∈ C j := (hC j t ht v).mp ((hgood.2 j).mp hcover)
  have hvc : v ∈ tangentCone (g '' Q) x := by
    rw [LocalCone.tangent_eq (hC j) (hG j)]
    exact hvC
  have hclosed : IsClosed (g '' Q) := (Q_object.1.image g.continuous).isClosed
  exact ⟨g,hg,base_mem_of_tangent hclosed hvc,hvc⟩

end
end R44.DischargePolyhedral

namespace R44
open Set DischargePolyhedral
noncomputable section

/-- Frozen field proposition. -/
theorem cone_sector_budgets_holds : EveryPackingLocallyFinite Q → ConeSectorBudgets Q := by
  intro hlf T x
  have hfinite : {g | g ∈ T.placements ∧ x ∈ g '' Q}.Finite := by
    have h := hlf T.toPacking ({x} : Set E3) (isCompact_singleton)
    simpa using h
  refine ⟨hfinite,?_,?_⟩
  · intro g h hg hh _ _ hne
    exact placed_tangent_interiors_disjoint T hg hh hne x
  · intro v
    exact DischargePolyhedral.cones_cover hlf T x v

end
end R44
