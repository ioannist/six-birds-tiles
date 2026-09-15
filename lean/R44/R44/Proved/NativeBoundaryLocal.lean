/- -- [compile-fix: promoted to Proved after exchange 7]
# Native frontier charts from the actual signed-tent set

A§1, A-L2.2/A-L3.1. The wide-panel proof reuses the ACCEPTED
native_feature_chart_classification (six axis types / three carrier strata).
No 192-case new decision is inserted. Open agreement is proved at every
closed-tube point, not only at pre-identified feature edges. This supplies
exact frontier equations on sloping faces and at base-square boundaries.
No admissions.
-/
import R44.Proved.NativeExceptionalVertices -- [compile-fix: promoted after exchange 7]
import R44.Proved.CarrierBoundaryStrata -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeBoundaryLocal
open Set Filter DischargeGeometry DischargeCharts DischargeTube
open DischargePyramid DischargeTentCones DischargePolyhedral
open DischargeMeridian DischargeOrdinary DischargeTangentTransport
open DischargeVertexData Generated
open scoped Topology
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem carrier_in_wide_panel (r : Role) (x : E3)
    (hx : ∀i:Fin 3, |x i-featureCenter r i|<2*eta) :
    x ∈ P ↔ featureNormalCoordinate r x ≤ 0 := by
  -- [compile-fix] Use the named classification once, then do the real
  -- inequalities generically; expanding all 192 rows in every `norm_num`
  -- branch exhausted elaboration resources.
  have hcoord (i : Fin 3) :
      |x i-((nativeFeatureData r).center8.get i : ℝ)/8|≤2*eta := by
    simpa [featureCenter,scaledV3] using (hx i).le
  have near_box (i : Fin 3)
      (hl : 2 ≤ (nativeFeatureData r).center8.get i)
      (hu : (nativeFeatureData r).center8.get i ≤ 14) :
      0 ≤ x i ∧ x i ≤ 2 := by
    have hi := hcoord i
    have hl' : (2 : ℝ) ≤ ((nativeFeatureData r).center8.get i : ℝ) := by
      exact_mod_cast hl
    have hu' : ((nativeFeatureData r).center8.get i : ℝ) ≤ (14 : ℝ) := by
      exact_mod_cast hu
    rw [abs_le] at hi
    norm_num [eta] at hi
    constructor <;> linarith
  have near_low (i : Fin 3)
      (hu : (nativeFeatureData r).center8.get i ≤ 6) : x i ≤ 1 := by
    have hi := hcoord i
    have hu' : ((nativeFeatureData r).center8.get i : ℝ) ≤ (6 : ℝ) := by
      exact_mod_cast hu
    rw [abs_le] at hi
    norm_num [eta] at hi
    linarith
  have near_high (i : Fin 3)
      (hl : 10 ≤ (nativeFeatureData r).center8.get i) : 1 < x i := by
    have hi := hcoord i
    have hl' : (10 : ℝ) ≤ ((nativeFeatureData r).center8.get i : ℝ) := by
      exact_mod_cast hl
    rw [abs_le] at hi
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
    rcases abs_le.mp hi with ⟨hi0, hi1⟩
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
    rcases abs_le.mp hi with ⟨hi0, hi1⟩
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


/-- Extends the accepted graph-point chart to all points of a closed tube. -/
theorem open_chart_at_tube (r : Role) (x : E3) (hx : featureTubeSupport r x) :
    ∃U:Set E3,IsOpen U ∧ x∈U ∧
      ∀y∈U,y∈Q ↔ y∈signedHypograph r := by
  let V : Set E3 := ⋂s:Role,{y | s≠r → ¬featureTubeSupport s y}
  have hV : IsOpen V := by
    apply isOpen_iInter_of_finite
    intro s
    by_cases hs : s=r
    · simp [hs]
    · -- [compile-fix: name the closed support before taking its open complement]
      have hc : IsClosed {y : E3 | featureTubeSupport s y} := tubeSupport_closed s
      have heq : {y : E3 | s ≠ r → ¬featureTubeSupport s y} =
          ({y : E3 | featureTubeSupport s y})ᶜ := by
        ext y
        simp [hs]
      rw [heq]
      exact isOpen_compl_iff.mpr hc
  have hxV : x∈V := by
    -- [compile-fix: expose membership in the finite intersection]
    simp only [V, mem_iInter, mem_setOf_eq]
    intro s
    exact fun hs => other_support_absent hs hx
  let W : Set E3 := {y | ∀i:Fin 3,|y i-featureCenter r i|<2*eta}
  have hW : IsOpen W := by
    -- [compile-fix: unfold the local set abbreviation before changing form]
    have heq : W = ⋂i:Fin 3,{y:E3 | |y i-featureCenter r i|<2*eta} := by
      ext y
      simp only [W, mem_setOf_eq, mem_iInter]
    rw [heq]
    apply isOpen_iInter_of_finite
    intro i; apply isOpen_lt <;> fun_prop
  have hxW : x∈W := by
    intro i
    exact (featureTubeSupport_coordinate_bound hx i).trans_lt (by norm_num [eta])
  refine ⟨W∩V,hW.inter hV,⟨hxW,hxV⟩,?_⟩
  intro y hy
  by_cases ht : featureTubeSupport r y
  · exact mem_Q_iff_in_tube r y ht
  · have hout : ∀s:Role,¬featureTubeSupport s y := by
      intro s
      by_cases hs : s=r
      · simpa [hs] using ht
      · -- [compile-fix: expose membership in V before applying it]
        have hyV : ∀ s : Role, s ≠ r → ¬featureTubeSupport s y := by
          have hyV' : y ∈ V := hy.2
          simpa only [V, mem_iInter, mem_setOf_eq] using hyV'
        exact hyV s hs
    rw [mem_Q_iff_outside hout,carrier_in_wide_panel r y hy.1]
    change featureNormalCoordinate r y≤0 ↔
      featureNormalCoordinate r y≤featureHeight r y
    by_cases hrad : featureRadius r y≤eta
    -- [compile-fix begin: split the sign cases for the current parser]
    · have hz : ¬|featureNormalCoordinate r y|≤eta := fun hz => ht ⟨hrad,hz⟩
      have hb := height_strict r y
      rw [abs_lt] at hb
      have hz' : featureNormalCoordinate r y < -eta ∨
          eta < featureNormalCoordinate r y := by
        have hgt : eta < |featureNormalCoordinate r y| := lt_of_not_ge hz
        by_cases hp : 0≤featureNormalCoordinate r y
        · right; simpa [abs_of_nonneg hp] using hgt
        · left
          rw [abs_of_neg (lt_of_not_ge hp)] at hgt
          linarith
      -- [compile-fix: split the sign cases explicitly for current tactic parsing]
      rcases hz' with hz' | hz'
      · constructor <;> intro hh <;> norm_num [eta] at * <;> linarith
      · constructor <;> intro hh <;> norm_num [eta] at * <;> linarith
    · have hh : featureHeight r y=0 := by
        unfold featureHeight
        rw [max_eq_left]
        · ring
        · have h := (one_le_div (show 0<eta by norm_num [eta])).mpr (le_of_lt (lt_of_not_ge hrad))
          linarith
      -- [compile-fix: close the rewritten equivalence explicitly]
      simp [hh]
    -- [compile-fix end]

/-- At any actual frontier point in a closed tube, the normal coordinate
is exactly the signed tent height. Strict subgraph or supergraph points cannot
-- [compile-fix: avoid a comment-closing token inside the documentation]
be frontier points, including points on the support's vertical sides. -/
theorem frontier_in_tube_equation (r : Role) (x : E3)
    (hx : x∈frontier Q) (ht : featureTubeSupport r x) :
    featureNormalCoordinate r x=featureHeight r x := by
  obtain ⟨U,hU,hxU,hagree⟩ := open_chart_at_tube r x ht
  have hxQ : x∈Q := by simpa [Q_object.1.isClosed.closure_eq] using hx.1
  have hle := (hagree x hxU).mp hxQ
  change featureNormalCoordinate r x≤featureHeight r x at hle
  by_contra hn
  have hs : featureNormalCoordinate r x<featureHeight r x := lt_of_le_of_ne hle hn
  have hO : IsOpen {y:E3 | featureNormalCoordinate r y<featureHeight r y} :=
    isOpen_lt (continuous_normalCoordinate r) (continuous_height r)
    -- API?: continuous_height is the accepted continuity theorem for
    -- featureHeight in PerTubeHomeomorphisms / NativeGeometry.
  apply hx.2
  -- [compile-fix: make the open-subset witness explicit before applying it]
  have hsub : U ∩ {y:E3 | featureNormalCoordinate r y<featureHeight r y} ⊆ Q := by
    intro y hy
    apply (hagree y hy.1).mpr
    change featureNormalCoordinate r y ≤ featureHeight r y
    exact hy.2.le
  exact (interior_maximal hsub (hU.inter hO)) ⟨hxU,hs⟩

/-- Off the finite union of CLOSED supports there is an open carrier chart. -/
theorem open_carrier_off_tubes (x : E3) (hx : ∀r:Role,¬featureTubeSupport r x) :
    ∃U:Set E3,IsOpen U ∧ x∈U ∧ ∀y∈U,y∈Q ↔ y∈P := by
  let U : Set E3 := ⋂r:Role,({y:E3 | featureTubeSupport r y})ᶜ
  have hU : IsOpen U := isOpen_iInter_of_finite fun r => (tubeSupport_closed r).isOpen_compl
  refine ⟨U,hU,by simpa [U] using hx,?_⟩
  intro y hy
  exact mem_Q_iff_outside (by simpa [U] using hy)

/-- Transfer frontier membership through a genuine open agreement chart. -/
theorem frontier_transfer {S T U : Set E3} {x : E3}
    (hS : IsClosed S) (hT : IsClosed T) (hU : IsOpen U) (hxU : x∈U)
    (he : ∀y∈U,y∈S ↔ y∈T) (hx : x∈frontier S) : x∈frontier T := by
  have hxS : x∈S := by simpa [hS.closure_eq] using hx.1
  refine ⟨subset_closure ((he x hxU).mp hxS),?_⟩
  intro hi
  apply hx.2
  -- [compile-fix: make the open-subset witness explicit before applying it]
  have hsub : U ∩ interior T ⊆ S := by
    intro y hy
    exact (he y hy.1).mpr (interior_subset hy.2)
  exact (interior_maximal hsub (hU.inter isOpen_interior)) ⟨hxU,hi⟩

end
end R44.DischargeBoundaryLocal
