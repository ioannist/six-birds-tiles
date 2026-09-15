/- -- [compile-fix]
# Open native hypograph charts, including base edges

Written proof: A§1 and A-L4.1 of proof/ALIGNMENT_PROOF.md. These lemmas make
explicit the open-neighborhood clause at a closed base edge: the function
continues as zero onto the flat panel beyond the square. The closed-tube
identity alone would not license a tangent-cone argument at those points.

No MeshSemantics admission, area recovery, tube-homeomorphism field, or
Hypotheses inhabitant is used. This file uses only the unconditional
NativeGeometry results and elementary coordinate/topological arguments.
No mathematical admissions. New/unconfirmed API calls are marked inline.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.PerTubeHomeomorphisms -- [compile-fix]

namespace R44.DischargeCharts
open Set R44.Generated R44.DischargeGeometry R44.DischargeTube
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem normal_cases (r : Role) :
    (nativeFeatureData r).normal = v 1 0 0 ∨
    (nativeFeatureData r).normal = v (-1) 0 0 ∨
    (nativeFeatureData r).normal = v 0 1 0 ∨
    (nativeFeatureData r).normal = v 0 (-1) 0 ∨
    (nativeFeatureData r).normal = v 0 0 1 ∨
    (nativeFeatureData r).normal = v 0 0 (-1) := by
  -- Definitional reading of panel coordinate axes, not a new certificate run.
  -- [compile-fix begin: use the accepted finite chart classifier instead of expanding 192 roles]
  obtain ⟨i, h⟩ := native_feature_chart_classification r
  dsimp only at h
  rcases h with h | h | h
  all_goals
    rcases h with ⟨hn, _⟩
    fin_cases i <;> simp [unitAxis, R44.v] at hn ⊢ <;> tauto
  -- [compile-fix end]

/-- The native orthogonal chart's linear part. The affine translation is
featureCenter r and is deliberately kept separate from tangent directions. -/
def chartLinear (r : Role) : E3 →ₗ[ℝ] E3 where
  toFun := fun v => v 0 • featureTangent₁ r + v 1 • featureTangent₂ r +
    v 2 • featureNormal r
  map_add' := by intros; simp only [PiLp.add_apply]; module
    -- API?: expected PiLp.add_apply: evaluation of a sum is the sum of evaluations.
  map_smul' := by intros; simp only [PiLp.smul_apply, RingHom.id_apply]; module -- [compile-fix]
    -- API?: expected PiLp.smul_apply: evaluation commutes with scalar multiplication.

@[simp] theorem chartLinear_apply (r : Role) (w : E3) :
    chartLinear r w = w 0 • featureTangent₁ r + w 1 • featureTangent₂ r +
      w 2 • featureNormal r := rfl

def chartIsometry (r : Role) : E3 →ₗᵢ[ℝ] E3 where
  toLinearMap := chartLinear r
  norm_map' := by
    intro w
    have hs : ‖chartLinear r w‖ ^ 2 = ‖w‖ ^ 2 := by
      rcases normal_cases r with h | h | h | h | h | h <;>
        simp [chartLinear_apply, featureTangent₁, featureTangent₂,
          featureTangentAxes, featureAxis, featureAxisOf, h, featureNormal,
          coordinateVector, scaledV3, EuclideanSpace.norm_sq_eq,
          Fin.sum_univ_succ, V3.get, R44.v] <;> ring
    nlinarith [norm_nonneg (chartLinear r w), norm_nonneg w]

private theorem chart_surjective (r : Role) : Function.Surjective (chartIsometry r) := by
  intro x
  let w : E3 := WithLp.toLp 2 ![
    chartU r (featureCenter r + x),
    chartV r (featureCenter r + x),
    featureNormalCoordinate r (featureCenter r + x)]
  refine ⟨w, ?_⟩
  have hr := chart_reconstruct r (featureCenter r + x)
  have hr' : featureCenter r + chartLinear r w = featureCenter r + x := by
    calc
      _ = chartPoint r (chartU r (featureCenter r+x))
          (chartV r (featureCenter r+x))
          (featureNormalCoordinate r (featureCenter r+x)) := by
            simp [chartLinear_apply, w, chartPoint] -- [compile-fix]
            module
      _ = featureCenter r+x := hr
  exact add_left_cancel hr' 

/-- This uses the same verified constructor already used in LogicalSpine. -/
def chartEquiv (r : Role) : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.ofSurjective (chartIsometry r) (chart_surjective r)

@[simp] theorem chartEquiv_apply (r : Role) (w : E3) :
    chartEquiv r w = chartLinear r w := rfl

private theorem coord_add (x y : E3) (i : Nat) :
    frameCoordinate (x+y) i = frameCoordinate x i + frameCoordinate y i := by
  unfold frameCoordinate
  split_ifs <;> simp

private theorem coord_smul (x : E3) (a : ℝ) (i : Nat) :
    frameCoordinate (a • x) i = a * frameCoordinate x i := by
  unfold frameCoordinate
  split_ifs <;> simp

/-- Affine chart coordinates of a convex/affine combination. -/
theorem affine_coordinates (r : Role) (x y : E3) (a b : ℝ) (hab : a+b=1) :
    chartU r (a • x + b • y) = a*chartU r x + b*chartU r y ∧
    chartV r (a • x + b • y) = a*chartV r x + b*chartV r y ∧
    featureNormalCoordinate r (a • x + b • y) =
      a*featureNormalCoordinate r x + b*featureNormalCoordinate r y := by
  have hd : (a • x + b • y) - featureCenter r =
      a • (x-featureCenter r) + b • (y-featureCenter r) := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
  simp only [chartU, chartV, featureNormalCoordinate, hd, coord_add, coord_smul]
  constructor
  · trivial -- [compile-fix]
  constructor
  · trivial -- [compile-fix]
  · ring

/-- A direction expressed in the native chart has exactly those three
coordinate increments. -/
theorem ray_coordinates (r : Role) (x w : E3) (t : ℝ) :
    chartU r (x + t • chartEquiv r w) = chartU r x + t*w 0 ∧
    chartV r (x + t • chartEquiv r w) = chartV r x + t*w 1 ∧
    featureNormalCoordinate r (x + t • chartEquiv r w) =
      featureNormalCoordinate r x + t*w 2 := by
  have heq : x + t • chartEquiv r w =
      chartPoint r (chartU r x + t*w 0) (chartV r x + t*w 1)
        (featureNormalCoordinate r x + t*w 2) := by
    calc
      _ = chartPoint r (chartU r x) (chartV r x)
          (featureNormalCoordinate r x) + t • chartEquiv r w := by
            rw [chart_reconstruct]
      _ = _ := by simp only [chartPoint, chartEquiv_apply, chartLinear_apply]; module
  rw [heq]
  simp

private def cornerU (k : Fin 4) : ℝ :=
  (if k.val = 0 ∨ k.val = 1 then -1 else 1) * eta
private def cornerV (k : Fin 4) : ℝ :=
  (if k.val = 0 ∨ k.val = 3 then -1 else 1) * eta

private theorem corner_chart (r : Role) (k : Fin 4) :
    featureCorner r k = chartPoint r (cornerU k) (cornerV k) 0 := by
  simp [featureCorner, chartPoint, cornerU, cornerV]

private theorem apex_chart (r : Role) :
    featureApex r = chartPoint r 0 0 ((profileCoefficient r : ℝ)/10000) := by
  simp [featureApex, chartPoint]

@[simp] private theorem chartU_corner (r : Role) (k : Fin 4) :
    chartU r (featureCorner r k) = cornerU k := by rw [corner_chart]; simp
@[simp] private theorem chartV_corner (r : Role) (k : Fin 4) :
    chartV r (featureCorner r k) = cornerV k := by rw [corner_chart]; simp
@[simp] private theorem chartZ_corner (r : Role) (k : Fin 4) :
    featureNormalCoordinate r (featureCorner r k) = 0 := by rw [corner_chart]; simp
@[simp] private theorem chartU_apex (r : Role) :
    chartU r (featureApex r) = 0 := by rw [apex_chart]; simp
@[simp] private theorem chartV_apex (r : Role) :
    chartV r (featureApex r) = 0 := by rw [apex_chart]; simp
@[simp] private theorem chartZ_apex (r : Role) :
    featureNormalCoordinate r (featureApex r) = (profileCoefficient r : ℝ)/10000 := by
  rw [apex_chart]; simp

private theorem corner_bounds (k : Fin 4) :
    |cornerU k| ≤ eta ∧ |cornerV k| ≤ eta := by
  fin_cases k <;> norm_num [cornerU,cornerV,eta]

private theorem consecutive_fixed_coordinate (k : Fin 4) :
    (cornerU k = cornerU (nextCorner k) ∧ |cornerU k| = eta) ∨
    (cornerV k = cornerV (nextCorner k) ∧ |cornerV k| = eta) := by
  fin_cases k <;> norm_num [cornerU,cornerV,nextCorner,eta]

private theorem convex_abs_bound {a b u v : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (hu : |u| ≤ eta) (hv : |v| ≤ eta) : |a*u+b*v| ≤ eta := by
  calc
    |a*u+b*v| ≤ |a*u|+|b*v| := abs_add_le _ _
    _ = a*|u|+b*|v| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*eta+b*eta := add_le_add (mul_le_mul_of_nonneg_left hu ha)
      (mul_le_mul_of_nonneg_left hv hb)
    _ = eta := by rw [← add_mul,hab,one_mul]

/-- Closed feature graphs really lie on the signed function, with the
square radius bound. The closed base corners and the apex are included. -/
theorem graph_coordinates (r : Role) {x : E3} (hx : x ∈ nativeFeatureGraph r) :
    featureRadius r x ≤ eta ∧
      featureNormalCoordinate r x = featureHeight r x := by
  rcases hx with hx | hx
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    rcases hk with ⟨a,b,ha,hb,hab,rfl⟩
    have hc := affine_coordinates r (featureCorner r k)
      (featureCorner r (nextCorner k)) a b hab
    simp only [chartU_corner,chartV_corner,chartZ_corner,mul_zero,add_zero] at hc
    have hrad : featureRadius r (a • featureCorner r k +
        b • featureCorner r (nextCorner k)) = eta := by
      change max |chartU r _| |chartV r _| = eta
      rw [hc.1,hc.2.1]
      have hu := convex_abs_bound ha hb hab (corner_bounds k).1
        (corner_bounds (nextCorner k)).1
      have hv := convex_abs_bound ha hb hab (corner_bounds k).2
        (corner_bounds (nextCorner k)).2
      apply le_antisymm (max_le hu hv)
      rcases consecutive_fixed_coordinate k with ⟨heq,habs⟩ | ⟨heq,habs⟩
      · have hfix : |a*cornerU k+b*cornerU (nextCorner k)| = eta := by
          rw [← heq,← add_mul,hab,one_mul,habs]
        rw [← hfix]
        exact le_max_left _ _
      · have hfix : |a*cornerV k+b*cornerV (nextCorner k)| = eta := by
          rw [← heq,← add_mul,hab,one_mul,habs]
        rw [← hfix]
        exact le_max_right _ _
    refine ⟨hrad.le, ?_⟩
    rw [hc.2.2, featureHeight, hrad]
    norm_num [eta]
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    rcases hk with ⟨a,b,ha,hb,hab,rfl⟩
    have hc := affine_coordinates r (featureCorner r k) (featureApex r) a b hab
    simp only [chartU_corner,chartV_corner,chartZ_corner,chartU_apex,chartV_apex,
      chartZ_apex,mul_zero,add_zero,zero_add] at hc
    have hrad : featureRadius r (a • featureCorner r k + b • featureApex r) = a*eta := by
      change max |chartU r _| |chartV r _| = a*eta
      rw [hc.1,hc.2.1]
      fin_cases k <;>
        simp [cornerU,cornerV,eta,abs_mul,abs_of_nonneg ha]
    refine ⟨by rw [hrad]; norm_num [eta]; linarith, ?_⟩
    rw [hc.2.2,featureHeight,hrad]
    have hw : 1-a*eta/eta = b := by
      norm_num [eta]
      linarith
    rw [hw,max_eq_right hb]
    ring

/-- A larger coordinate box entirely within one carrier panel chart. -/
def panelNeighborhood (r : Role) : Set E3 :=
  {x | ∀ i : Fin 3, |x i-featureCenter r i| < 2*eta}

private theorem carrier_in_panelNeighborhood (r : Role) (x : E3)
    (hx : x ∈ panelNeighborhood r) :
    x ∈ P ↔ featureNormalCoordinate r x ≤ 0 := by
  -- [compile-fix begin: replace the nonterminating 192-role expansion by the accepted chart classifier]
  have hcoord (i : Fin 3) :
      |x i - ((nativeFeatureData r).center8.get i : ℝ) / 8| < 2 * eta := by
    simpa [panelNeighborhood, featureCenter, scaledV3] using hx i
  have near_box (i : Fin 3)
      (hl : 2 ≤ (nativeFeatureData r).center8.get i)
      (hu : (nativeFeatureData r).center8.get i ≤ 14) :
      0 ≤ x i ∧ x i ≤ 2 := by
    have hi := hcoord i
    have hl' : (2 : ℝ) ≤ ((nativeFeatureData r).center8.get i : ℝ) := by
      exact_mod_cast hl
    have hu' : ((nativeFeatureData r).center8.get i : ℝ) ≤ (14 : ℝ) := by
      exact_mod_cast hu
    rw [abs_lt] at hi
    norm_num [eta] at hi
    constructor <;> linarith
  have near_low (i : Fin 3)
      (hu : (nativeFeatureData r).center8.get i ≤ 6) : x i ≤ 1 := by
    have hi := hcoord i
    have hu' : ((nativeFeatureData r).center8.get i : ℝ) ≤ (6 : ℝ) := by
      exact_mod_cast hu
    rw [abs_lt] at hi
    norm_num [eta] at hi
    linarith
  have near_high (i : Fin 3)
      (hl : 10 ≤ (nativeFeatureData r).center8.get i) : 1 < x i := by
    have hi := hcoord i
    have hl' : (10 : ℝ) ≤ ((nativeFeatureData r).center8.get i : ℝ) := by
      exact_mod_cast hl
    rw [abs_lt] at hi
    norm_num [eta] at hi
    linarith
  have hP : x ∈ P ↔
      (∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 2) ∧ ∃ i : Fin 3, x i ≤ 1 := by
    rw [mem_P_iff_coordinates]
    constructor
    · rintro ⟨h0, h0', h1, h1', h2, h2', hn⟩
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i <;> simp_all
      · rcases hn with hn | hn | hn
        · exact ⟨0, hn⟩
        · exact ⟨1, hn⟩
        · exact ⟨2, hn⟩
    · rintro ⟨hbox, i, hi⟩
      refine ⟨(hbox 0).1, (hbox 0).2, (hbox 1).1, (hbox 1).2,
        (hbox 2).1, (hbox 2).2, ?_⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr hi)
  have normal_pos (i : Fin 3)
      (hn : (nativeFeatureData r).normal = unitAxis i.val 1) :
      featureNormalCoordinate r x =
        x i - ((nativeFeatureData r).center8.get i : ℝ) / 8 := by
    fin_cases i <;>
      simp [featureNormalCoordinate, featureAxis, featureAxisOf, hn,
        featureCenter, scaledV3, frameCoordinate, unitAxis, V3.get, R44.v]
  have normal_neg (i : Fin 3)
      (hn : (nativeFeatureData r).normal = unitAxis i.val (-1)) :
      featureNormalCoordinate r x =
        -(x i - ((nativeFeatureData r).center8.get i : ℝ) / 8) := by
    fin_cases i <;>
      simp [featureNormalCoordinate, featureAxis, featureAxisOf, hn,
        featureCenter, scaledV3, frameCoordinate, unitAxis, V3.get, R44.v]
  obtain ⟨i, hcase⟩ := native_feature_chart_classification r
  dsimp only at hcase
  rcases hcase with hneg | hnotch | houter
  · rcases hneg with ⟨hn, hc, htan⟩
    have hi := hcoord i
    norm_num [hc, eta] at hi
    rcases abs_lt.mp hi with ⟨hi0, hi1⟩
    rw [hP, normal_neg i hn]
    norm_num [hc]
    constructor
    · intro hmem
      exact (hmem.1 i).1
    · intro hin
      constructor
      · intro j
        by_cases hji : j = i
        · subst j
          exact ⟨hin, by linarith⟩
        · exact near_box j (htan j hji).1 (htan j hji).2
      · exact ⟨i, by linarith⟩
  · rcases hnotch with ⟨hn, hc, htan⟩
    rw [hP, normal_pos i hn]
    norm_num [hc]
    constructor
    · rintro ⟨_, j, hj⟩
      by_cases hji : j = i
      · simpa [hji] using hj
      · exact False.elim ((not_le_of_gt (near_high j (htan j hji).1)) hj)
    · intro hin
      constructor
      · intro j
        by_cases hji : j = i
        · subst j
          exact near_box i (by omega) (by omega)
        · have hj := htan j hji
          exact near_box j (by omega) hj.2
      · exact ⟨i, hin⟩
  · rcases houter with ⟨hn, hc, htan, j, hji, hjlow⟩
    have hi := hcoord i
    norm_num [hc, eta] at hi
    rcases abs_lt.mp hi with ⟨hi0, hi1⟩
    rw [hP, normal_pos i hn]
    norm_num [hc]
    constructor
    · intro hmem
      exact (hmem.1 i).2
    · intro hin
      constructor
      · intro k
        by_cases hki : k = i
        · subst k
          exact ⟨by linarith, hin⟩
        · exact near_box k (htan k hki).1 (htan k hki).2
      · exact ⟨j, near_low j hjlow⟩
  -- [compile-fix end]

theorem tubeSupport_closed (r : Role) :
    IsClosed {x : E3 | featureTubeSupport r x} := by
  exact (isClosed_le (continuous_radius r) continuous_const).inter
    (isClosed_le (continuous_normalCoordinate r).abs continuous_const)

def signedHypograph (r : Role) : Set E3 :=
  {x | featureNormalCoordinate r x ≤ featureHeight r x}

/-- Open, not merely relative-to-the-closed-tube, agreement. This supplies
the neighborhood needed at pyramid base edges and all their endpoints. -/
theorem open_tent_agreement (r : Role) {x : E3}
    (hx : x ∈ nativeFeatureGraph r) :
    ∃ U : Set E3, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ Q ↔ y ∈ signedHypograph r := by
  obtain ⟨hrad,hgraph⟩ := graph_coordinates r hx
  have hz : |featureNormalCoordinate r x| < eta := by
    rw [hgraph]
    exact height_strict r x
  have hxs : featureTubeSupport r x := ⟨hrad,hz.le⟩
  let V : Set E3 := ⋂ s : Role, {y | s ≠ r → ¬ featureTubeSupport s y}
  have hV : IsOpen V := by
    apply isOpen_iInter_of_finite -- API?: finite-index intersections of open sets are open.
    intro s
    by_cases hsr : s=r
    · simpa [hsr] using (isOpen_univ : IsOpen (Set.univ : Set E3))
    · -- [compile-fix begin: avoid simp rewriting the type of the complement-openness witness]
      convert (tubeSupport_closed s).isOpen_compl using 1
      ext y
      simp [hsr]
      -- [compile-fix end]
  have hVx : x ∈ V := by
    simp only [V, Set.mem_iInter, Set.mem_setOf_eq]
    intro s hsr
    exact other_support_absent hsr hxs
  have hPopen : IsOpen (panelNeighborhood r) := by
    -- [compile-fix begin: unfold the forall-set as the finite intersection explicitly]
    rw [show panelNeighborhood r =
      ⋂ i : Fin 3, {y : E3 | |y i-featureCenter r i| < 2*eta} by
        ext y
        simp [panelNeighborhood]]
    exact isOpen_iInter_of_finite fun _ => isOpen_lt (by fun_prop) continuous_const
    -- [compile-fix end]
      -- API?: same finite-index open-intersection lemma as above.
  have hPx : x ∈ panelNeighborhood r := by
    intro i
    exact (featureTubeSupport_coordinate_bound hxs i).trans_lt (by norm_num [eta])
  let U : Set E3 := panelNeighborhood r ∩
    ({y : E3 | |featureNormalCoordinate r y| < eta} ∩ V)
  refine ⟨U, hPopen.inter
    ((isOpen_lt (continuous_normalCoordinate r).abs continuous_const).inter hV),
    ⟨hPx,hz,hVx⟩,?_⟩
  intro y hy
  rcases hy with ⟨hyP,hyn,hyV⟩
  by_cases hyt : featureTubeSupport r y
  · exact mem_Q_iff_in_tube r y hyt
  · have hall : ∀ s : Role, ¬ featureTubeSupport s y := by
      intro s
      by_cases hs : s=r
      · simpa [hs] using hyt
      · exact (Set.mem_iInter.mp hyV s) hs
    have hr : eta < featureRadius r y := by
      exact lt_of_not_ge (fun h => hyt ⟨h,hyn.le⟩)
    have hh : featureHeight r y = 0 := by
      unfold featureHeight
      have h := (one_le_div (show 0 < eta by norm_num [eta])).mpr hr.le
      rw [max_eq_left (show 1-featureRadius r y/eta ≤ 0 by linarith)]
      ring
    change y ∈ Q ↔ featureNormalCoordinate r y ≤ featureHeight r y
    rw [mem_Q_iff_outside hall,carrier_in_panelNeighborhood r y hyP,hh]

/-- Radial cones depend only on the set germ at their base point. -/
theorem tangentCone_of_open_agreement {S T U : Set E3} {x : E3}
    (hU : IsOpen U) (hx : x ∈ U)
    (heq : ∀ y ∈ U, y ∈ S ↔ y ∈ T) : tangentCone S x = tangentCone T x := by
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hnear (v : E3) (t : ℝ) (ht : 0<t) (hs : t<δ/(‖v‖+1)) :
      x+t • v ∈ U := by
    apply hball
    have hd : dist (x+t • v) x = t*‖v‖ := by
      simp [dist_eq_norm,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    rw [Metric.mem_ball,hd]
    have hp : 0<‖v‖+1 := by positivity
    have hh := (lt_div_iff₀ hp).mp hs
    nlinarith
  have transfer {S T : Set E3} (h : ∀ y ∈ U, y ∈ S ↔ y ∈ T) :
      tangentCone S x ⊆ tangentCone T x := by
    intro v hv
    obtain ⟨ε,hε,hv⟩ := hv
    refine ⟨min ε (δ/(‖v‖+1)),lt_min hε (by positivity),?_⟩
    intro t ht hs
    exact (h _ (hnear v t ht (lt_min_iff.mp hs).2)).mp
      (hv t ht (lt_min_iff.mp hs).1)
  exact Set.Subset.antisymm (transfer heq) (transfer fun y hy => (heq y hy).symm)

/-- The concrete tangent cone at every feature point has the same germ as
the globally continued square-tent hypograph. No volume claim is used. -/
theorem native_tangentCone_eq_hypograph (r : Role) {x : E3}
    (hx : x ∈ nativeFeatureGraph r) :
    tangentCone Q x = tangentCone (signedHypograph r) x := by
  obtain ⟨U,hU,hxU,hagree⟩ := open_tent_agreement r hx
  exact tangentCone_of_open_agreement hU hxU hagree

end
end R44.DischargeCharts
