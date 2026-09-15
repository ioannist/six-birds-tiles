/-
Shared native-chart geometry for F1: A§1, A-L3.1, A-L5.1, and R§1.1–1.3.
This file follows the signed-tent set definition, not an interpretation of a
Boolean mesh audit. No ERRATA changes these native chart formulas.

All statements here have proof scripts with no mathematical admissions.
The frozen file and all its definitions are imported unchanged. API-sensitive
calls not established in the supplied repository are flagged at use sites.

This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.LogicalSpineFoundation -- [compile-fix]

namespace R44.DischargeGeometry

open Set
open R44.Generated
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- This is only definitional identification of two literal presentations,
not re-execution of a Boolean certificate. -/
private theorem native_coefficient_literal_identity :
    nativeFeatures.map Feature.coefficient = panelProfile := by
  rfl

private theorem coefficient_mem_panelProfile (r : Role) :
    profileCoefficient r ∈ panelProfile := by
  have hr : r.val < nativeFeatures.length := by
    rw [native_features_length]
    exact r.isLt
  have hdata : nativeFeatureData r = nativeFeatures[r.val] := by
    simp [nativeFeatureData, R44.getD, hr]
  have hmem : nativeFeatureData r ∈ nativeFeatures := by
    rw [hdata]
    exact List.getElem_mem hr -- API?: expected List lemma: hr : i < xs.length → xs[i] ∈ xs.
  rw [← native_coefficient_literal_identity]
  exact List.mem_map.mpr ⟨nativeFeatureData r, hmem, rfl⟩

/-- Interpret a certified canonical component assignment. In a covered role,
findIdx? cannot use its fallback, and find? must return a certified sign. -/
private theorem canonical_coefficient_bounds
    (rows : List SignEquation) (cs : List (List (Nat × Int)))
    (hgraph : componentsDescribeGraph rows cs = true)
    {a : Int} (ha : a ∈ canonicalProfile cs) :
    a ≠ 0 ∧ a.natAbs ≤ 12 := by
  have hparts := hgraph
  unfold componentsDescribeGraph at hparts
  simp only [Bool.and_eq_true] at hparts
  have hlengthB : (cs.length == 12) = true := by tauto
  have hlength : cs.length = 12 := by simpa using hlengthB
  have hcover : setEq (cs.flatMap componentRoleList) (List.range 192) = true := by
    tauto
  have hvalid : cs.all (componentValid rows) = true := by tauto
  change a ∈ (List.range 192).map (fun r =>
    Int.ofNat (componentIndex cs r + 1) * componentSign cs r) at ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  have hcovered : r ∈ cs.flatMap componentRoleList := by
    unfold setEq R44.subset at hcover
    simp only [Bool.and_eq_true] at hcover
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hcover.2 r hr)
  obtain ⟨c, hc, hrc⟩ := List.mem_flatMap.mp hcovered
  have hex : ∃ c ∈ cs, (componentRoleList c).contains r = true :=
    ⟨c, hc, List.contains_iff_mem.mpr hrc⟩
  have hidxSome := List.findIdx?_eq_some_of_exists hex -- API?: expected List lemma: an existing match gives findIdx? p xs = some (findIdx p xs).
  have hidxLt := List.findIdx_lt_length_of_exists hex -- API?: expected List lemma: an existing match gives findIdx p xs < xs.length.
  have hidx : componentIndex cs r < 12 := by
    simpa only [componentIndex, hidxSome, hlength] using hidxLt
  change r ∈ c.map Prod.fst at hrc
  obtain ⟨q, hq, hqr⟩ := List.mem_map.mp hrc
  have hqflat : q ∈ cs.flatten := List.mem_flatten.mpr ⟨c, hc, hq⟩ -- API?: expected List lemma: x ∈ xs.flatten ↔ ∃ ys ∈ xs, x ∈ ys.
  have hexSign : ∃ q ∈ cs.flatten, (q.1 == r) = true :=
    ⟨q, hqflat, by simpa using hqr⟩
  have hsome : (cs.flatten.find? (fun q => q.1 == r)).isSome = true :=
    List.find?_isSome.mpr hexSign -- API?: expected List lemma: (xs.find? p).isSome = true ↔ ∃ x ∈ xs, p x = true.
  have hsign : componentSign cs r = 1 ∨ componentSign cs r = -1 := by
    cases hfind : cs.flatten.find? (fun q => q.1 == r) with
    | none => simp [hfind] at hsome
    | some q =>
        have hq' : q ∈ cs.flatten := List.mem_of_find?_eq_some hfind -- API?: expected List lemma: xs.find? p = some q → q ∈ xs.
        obtain ⟨cq, hcq, hqcq⟩ := List.mem_flatten.mp hq' -- API?: expected List lemma: x ∈ xs.flatten ↔ ∃ ys ∈ xs, x ∈ ys.
        have hcvalid := List.all_eq_true.mp hvalid cq hcq
        unfold componentValid at hcvalid
        simp only [Bool.and_eq_true] at hcvalid
        have hall : cq.all (fun q => q.2 == 1 || q.2 == -1) = true := by
          tauto
        have hqsign : q.2 = 1 ∨ q.2 = -1 := by
          simpa using List.all_eq_true.mp hall q hqcq
        simpa only [componentSign, hfind] using hqsign
  have hnonzero : (Int.ofNat (componentIndex cs r + 1)) ≠ 0 := by -- [compile-fix]
    exact Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero _) -- [compile-fix]
  have hbound : componentIndex cs r + 1 ≤ 12 := by omega
  rcases hsign with hsign | hsign
  · rw [hsign, mul_one] -- [compile-fix]
    exact ⟨hnonzero, by simpa only [Int.natAbs_ofNat'] using hbound⟩ -- [compile-fix]
  · rw [hsign, mul_neg_one] -- [compile-fix]
    exact ⟨neg_ne_zero.mpr hnonzero, by -- [compile-fix]
      simpa only [Int.natAbs_neg, Int.natAbs_ofNat'] using hbound⟩ -- [compile-fix]

/-- The existing profile certificate supplies nonzero coefficients of
absolute value at most 12. No 192-case decide/native_decide is used. -/
theorem coefficient_bounds (hprofile : profileCanonicalCheck = true)
    (r : Role) : profileCoefficient r ≠ 0 ∧ (profileCoefficient r).natAbs ≤ 12 := by
  have hparts := hprofile
  unfold profileCanonicalCheck profileCanonicalCheckWith at hparts
  simp only [Bool.and_eq_true] at hparts
  have hgraph : componentsDescribeGraph signedRows balancedComponents = true := by
    exact hparts.1.1.1.2 -- [compile-fix]
  have hcanonicalB :
      (canonicalProfile balancedComponents == certificateProfile) = true := by -- [compile-fix]
    exact hparts.1.1.2 -- [compile-fix]
  have hpanelsB : (certificateProfile == panelProfile) = true := by -- [compile-fix]
    exact hparts.1.2 -- [compile-fix]
  have hcanonical : canonicalProfile balancedComponents = certificateProfile := by
    simpa using hcanonicalB
  have hpanels : certificateProfile = panelProfile := by simpa using hpanelsB
  have hmem := coefficient_mem_panelProfile r
  rw [← hpanels, ← hcanonical] at hmem
  exact canonical_coefficient_bounds signedRows balancedComponents hgraph hmem

/-! ## Cartesian chart facts

The two small literal facts below are new *coordinate* facts, not a replay of
any atlas, census, profile or mesh certificate. The normal magnitude and the
profile bounds use their existing theorems. The role case split is used only
to read the selected panel axis and its integer supporting-plane coordinate.
-/

private theorem normal_data_cases (r : Role) :
    (nativeFeatureData r).normal = v 1 0 0 ∨
    (nativeFeatureData r).normal = v (-1) 0 0 ∨
    (nativeFeatureData r).normal = v 0 1 0 ∨
    (nativeFeatureData r).normal = v 0 (-1) 0 ∨
    (nativeFeatureData r).normal = v 0 0 1 ∨
    (nativeFeatureData r).normal = v 0 0 (-1) := by
  revert r -- [compile-fix]
  decide -- [compile-fix]

/-- The normal coordinate of a native panel lies on an integer plane. -/
theorem normal_plane_integer (r : Role) :
    ∃ i : Fin 3, ∃ k : Int,
      featureAxis r = i.val ∧ featureCenter r i = (k : ℝ) := by
  have hraw : ∀ s : Role, ∃ i : Fin 3, -- [compile-fix]
      featureAxis s = i.val ∧ -- [compile-fix]
        (nativeFeatureData s).center8.get i = -- [compile-fix]
          8 * ((nativeFeatureData s).center8.get i / 8) := by -- [compile-fix]
    decide -- [compile-fix]
  obtain ⟨i, haxis, hcenter⟩ := hraw r -- [compile-fix]
  let k : Int := (nativeFeatureData r).center8.get i / 8 -- [compile-fix]
  refine ⟨i, k, haxis, ?_⟩ -- [compile-fix]
  change ((nativeFeatureData r).center8.get i : ℝ) / 8 = (k : ℝ) -- [compile-fix]
  have hcenter' : ((nativeFeatureData r).center8.get i : ℝ) = -- [compile-fix]
      8 * (k : ℝ) := by -- [compile-fix]
    exact_mod_cast hcenter -- [compile-fix]
  rw [hcenter'] -- [compile-fix]
  ring -- [compile-fix]

/-- Native tangent coordinate functions; these are only abbreviations. -/
def chartU (r : Role) (x : E3) : ℝ :=
  frameCoordinate (x - featureCenter r) (featureTangentAxes r).1

def chartV (r : Role) (x : E3) : ℝ :=
  frameCoordinate (x - featureCenter r) (featureTangentAxes r).2

/-- Local coordinate parametrization, with the genuine outward unit normal. -/
def chartPoint (r : Role) (u v z : ℝ) : E3 :=
  featureCenter r + u • featureTangent₁ r + v • featureTangent₂ r +
    z • featureNormal r

@[simp] theorem chart_coordinates (r : Role) (u v z : ℝ) :
    chartU r (chartPoint r u v z) = u ∧
    chartV r (chartPoint r u v z) = v ∧
    featureNormalCoordinate r (chartPoint r u v z) = z := by
  rcases normal_data_cases r with h | h | h | h | h | h <;>
    simp [chartU, chartV, chartPoint, featureTangent₁, featureTangent₂,
      featureTangentAxes, featureAxis, featureAxisOf, h, featureNormal,
      coordinateVector, frameCoordinate, featureNormalCoordinate,
      scaledV3, V3.get, R44.v] <;> ring

@[simp] theorem chartU_chartPoint (r : Role) (u v z : ℝ) :
    chartU r (chartPoint r u v z) = u := (chart_coordinates r u v z).1
@[simp] theorem chartV_chartPoint (r : Role) (u v z : ℝ) :
    chartV r (chartPoint r u v z) = v := (chart_coordinates r u v z).2.1
@[simp] theorem chartZ_chartPoint (r : Role) (u v z : ℝ) :
    featureNormalCoordinate r (chartPoint r u v z) = z :=
  (chart_coordinates r u v z).2.2

@[simp] theorem chart_reconstruct (r : Role) (x : E3) :
    chartPoint r (chartU r x) (chartV r x) (featureNormalCoordinate r x) = x := by
  apply PiLp.ext
  intro i
  rcases normal_data_cases r with h | h | h | h | h | h <;>
    fin_cases i <;>
    simp [chartU, chartV, chartPoint, featureTangent₁, featureTangent₂,
      featureTangentAxes, featureAxis, featureAxisOf, h, featureNormal,
      coordinateVector, frameCoordinate, featureNormalCoordinate,
      scaledV3, V3.get, R44.v] <;> ring

@[simp] theorem normal_shift (r : Role) (x : E3) (t : ℝ) :
    featureNormalCoordinate r (x + t • featureNormal r) =
      featureNormalCoordinate r x + t := by
  rcases normal_data_cases r with h | h | h | h | h | h <;>
    simp [featureNormalCoordinate, featureAxis, featureAxisOf, h,
      featureNormal, scaledV3, frameCoordinate, V3.get, R44.v] <;> ring

@[simp] theorem radius_normal_shift (r : Role) (x : E3) (t : ℝ) :
    featureRadius r (x + t • featureNormal r) = featureRadius r x := by
  rcases normal_data_cases r with h | h | h | h | h | h <;>
    simp [featureRadius, featureTangentAxes, featureAxis, featureAxisOf,
      h, featureNormal, scaledV3, frameCoordinate, V3.get, R44.v]

@[simp] theorem height_normal_shift (r : Role) (x : E3) (t : ℝ) :
    featureHeight r (x + t • featureNormal r) = featureHeight r x := by
  simp only [featureHeight, radius_normal_shift]

/-- Every normal has Euclidean norm one, not merely one nonzero coordinate. -/
@[simp] theorem featureNormal_norm (r : Role) : ‖featureNormal r‖ = 1 := by
  have hs : ‖featureNormal r‖ ^ 2 = 1 := by
    rcases normal_data_cases r with h | h | h | h | h | h <;>
      norm_num [featureNormal, h, scaledV3, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_succ, V3.get, R44.v]
  nlinarith [norm_nonneg (featureNormal r)]

/-- Equality with the carrier outside all 192 *closed* supports. -/
theorem mem_Q_iff_outside {x : E3}
    (hout : ∀ r : Role, ¬ featureTubeSupport r x) :
    x ∈ Q ↔ x ∈ P := by
  constructor
  · rintro (⟨hxP, _⟩ | ⟨r, _, hr, _⟩)
    · exact hxP
    · exact (hout r hr).elim
  · intro hxP
    exact Or.inl ⟨hxP, fun r _ hr => (hout r hr).elim⟩

/-- No unrelated edit can contribute at a point of this tube. -/
theorem other_support_absent {r s : Role} {x : E3}
    (hrs : s ≠ r) (hx : featureTubeSupport r x) :
    ¬ featureTubeSupport s x := by
  intro hs
  exact Set.disjoint_left.mp
    (featureTubeSupports_pairwiseDisjoint r s (Ne.symm hrs)) hx hs

/-- A useful coordinate description of the *closed* carrier, including its
internal cube interfaces. -/
theorem mem_P_iff_coordinates (x : E3) :
    x ∈ P ↔
      0 ≤ x 0 ∧ x 0 ≤ 2 ∧ 0 ≤ x 1 ∧ x 1 ≤ 2 ∧
      0 ≤ x 2 ∧ x 2 ≤ 2 ∧ (x 0 ≤ 1 ∨ x 1 ≤ 1 ∨ x 2 ≤ 1) := by
  have hcube (a : V3) : x ∈ unitCube a ↔
      (a.x : ℝ) ≤ x 0 ∧ x 0 ≤ (a.x : ℝ) + 1 ∧
      (a.y : ℝ) ≤ x 1 ∧ x 1 ≤ (a.y : ℝ) + 1 ∧
      (a.z : ℝ) ≤ x 2 ∧ x 2 ≤ (a.z : ℝ) + 1 := by
    simp [unitCube, Fin.forall_fin_succ, V3.get, and_assoc] -- [compile-fix]
  constructor
  · rintro ⟨a, ha, hx⟩
    change a ∈ bits.filter (fun x => x != v 1 1 1) at ha -- [compile-fix]
    obtain ⟨ha, hne⟩ := List.mem_filter.mp ha -- [compile-fix]
    have ha_ne : a ≠ v 1 1 1 := by -- [compile-fix]
      intro hae -- [compile-fix]
      subst a -- [compile-fix]
      have hf : (v 1 1 1 != v 1 1 1) = false := by rfl -- [compile-fix]
      rw [hf] at hne -- [compile-fix]
      exact Bool.noConfusion hne -- [compile-fix]
    simp only [bits, List.mem_cons, List.not_mem_nil, or_false] at ha -- [compile-fix]
    have ha7 : a = v 0 0 0 ∨ a = v 0 0 1 ∨ a = v 0 1 0 ∨ -- [compile-fix]
        a = v 0 1 1 ∨ a = v 1 0 0 ∨ a = v 1 0 1 ∨ a = v 1 1 0 := by -- [compile-fix]
      tauto -- [compile-fix]
    clear ha hne ha_ne -- [compile-fix]
    rcases ha7 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) -- [compile-fix]
    all_goals
      rw [hcube] at hx
      norm_num [v] at hx
      rcases hx with ⟨h0, h0', h1, h1', h2, h2'⟩
      refine ⟨by linarith, by linarith, by linarith, by linarith,
        by linarith, by linarith, ?_⟩
      first
      | exact Or.inl (by linarith)
      | exact Or.inr (Or.inl (by linarith))
      | exact Or.inr (Or.inr (by linarith))
  · rintro ⟨h0, h0', h1, h1', h2, h2', hnotch⟩
    let a : V3 := v (if x 0 ≤ 1 then 0 else 1)
      (if x 1 ≤ 1 then 0 else 1) (if x 2 ≤ 1 then 0 else 1)
    refine ⟨a, ?_, ?_⟩
    · rcases hnotch with h | h | h <;>
        simp [a, h, chairCells, bits, R44.v] <;> -- [compile-fix]
          split_ifs <;> simp_all <;> decide -- [compile-fix]
    · have slot (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
          (((if t ≤ 1 then 0 else 1) : Int) : ℝ) ≤ t ∧
          t ≤ (((if t ≤ 1 then 0 else 1) : Int) : ℝ) + 1 := by
        by_cases ht : t ≤ 1
        · simpa [ht] using And.intro ht0 ht
        · have ht1 : (1 : ℝ) ≤ t := le_of_lt (lt_of_not_ge ht)
          norm_num [ht] -- [compile-fix]
          exact ⟨ht1, ht2⟩ -- [compile-fix]
      rw [hcube]
      exact ⟨(slot (x 0) h0 h0').1, (slot (x 0) h0 h0').2,
        (slot (x 1) h1 h1').1, (slot (x 1) h1 h1').2,
        (slot (x 2) h2 h2').1, (slot (x 2) h2 h2').2⟩

-- [compile-fix begin: replace 192-way chart expansion with one finite classifier and generic inequalities]
/-- The finite 192-chart classification used by `carrier_in_tube`. -/
theorem native_feature_chart_classification :
    ∀ s : Role, ∃ i : Fin 3,
      let c := (nativeFeatureData s).center8
      let n := (nativeFeatureData s).normal
      (n = unitAxis i.val (-1) ∧ c.get i = 0 ∧
        ∀ j : Fin 3, j ≠ i → 2 ≤ c.get j ∧ c.get j ≤ 14) ∨
      (n = unitAxis i.val 1 ∧ c.get i = 8 ∧
        ∀ j : Fin 3, j ≠ i → 10 ≤ c.get j ∧ c.get j ≤ 14) ∨
      (n = unitAxis i.val 1 ∧ c.get i = 16 ∧
        (∀ j : Fin 3, j ≠ i → 2 ≤ c.get j ∧ c.get j ≤ 14) ∧
        ∃ j : Fin 3, j ≠ i ∧ c.get j ≤ 6) := by
  decide -- [compile-fix]

/-- On each closed tube the bare carrier occupies exactly the inward
half-space. This is direct real arithmetic on the native panels; it does
not assume a homeomorphism of Q or a frontier/mesh correspondence. -/
theorem carrier_in_tube (r : Role) (x : E3)
    (hx : featureTubeSupport r x) :
    x ∈ P ↔ featureNormalCoordinate r x ≤ 0 := by
  -- [compile-fix] Use the named classification once, then do the real
  -- inequalities generically; expanding all 192 rows in every `norm_num`
  -- branch exhausted elaboration resources.
  have hb := featureTubeSupport_coordinate_bound hx
  have hcoord (i : Fin 3) :
      |x i - ((nativeFeatureData r).center8.get i : ℝ) / 8| ≤ eta := by
    simpa [featureCenter, scaledV3] using hb i
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
-- [compile-fix end]

/-- Signed tent functions really describe the frozen set Q in every tube.
This includes tube sides and edges, not only a face interior. -/
theorem mem_Q_iff_in_tube (r : Role) (x : E3)
    (hx : featureTubeSupport r x) :
    x ∈ Q ↔ featureNormalCoordinate r x ≤ featureHeight r x := by
  have hother : ∀ s : Role, s ≠ r → ¬ featureTubeSupport s x :=
    fun s hsr => other_support_absent hsr hx
  have hheight_sign :
      (profileCoefficient r ≤ 0 → featureHeight r x ≤ 0) ∧
      (0 ≤ profileCoefficient r → 0 ≤ featureHeight r x) := by
    constructor
    · intro hc
      exact mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hc) (by norm_num))
        (le_max_left _ _)
    · intro hc
      exact mul_nonneg
        (div_nonneg (by exact_mod_cast hc) (by norm_num)) (le_max_left _ _)
  constructor
  · rintro (⟨hxP, hcuts⟩ | ⟨s, hspos, hs, hz, hzh⟩)
    · by_cases hneg : profileCoefficient r < 0
      · exact hcuts r hneg hx
      · exact (carrier_in_tube r x hx).mp hxP |>.trans
          (hheight_sign.2 (by omega))
    · have hsr : s = r := by
        by_contra hne
        exact hother s hne hs
      subst s
      exact hzh
  · intro hz
    by_cases hpos : 0 < profileCoefficient r
    · by_cases hnonneg : 0 ≤ featureNormalCoordinate r x
      · exact Or.inr ⟨r, hpos, hx, hnonneg, hz⟩
      · refine Or.inl ⟨(carrier_in_tube r x hx).mpr (le_of_not_ge hnonneg), ?_⟩
        intro s hsneg hs
        by_cases hsr : s = r
        · subst s; omega
        · exact (hother s hsr hs).elim
    · refine Or.inl ⟨(carrier_in_tube r x hx).mpr
        (hz.trans (hheight_sign.1 (by omega))), ?_⟩
      intro s _ hs
      by_cases hsr : s = r
      · simpa [hsr] using hz
      · exact (hother s hsr hs).elim

/-- Uniform native height estimate extracted from the certified profile. -/
theorem featureHeight_abs_bound (r : Role) (x : E3) :
    |featureHeight r x| ≤ (12 : ℝ) / 10000 := by
  have hc : |(profileCoefficient r : ℝ)| ≤ 12 := by
    have h := (coefficient_bounds profile_canonical r).2
    have hz : (|profileCoefficient r| : ℤ) ≤ 12 := by -- [compile-fix]
      rw [← Int.natCast_natAbs] -- [compile-fix]
      exact_mod_cast h -- [compile-fix]
    exact_mod_cast hz -- [compile-fix]
  have hr : 0 ≤ featureRadius r x :=
    (abs_nonneg _).trans (le_max_left _ _)
  have hw0 : 0 ≤ max 0 (1 - featureRadius r x / eta) := le_max_left _ _
  have hw1 : max 0 (1 - featureRadius r x / eta) ≤ 1 := by
    apply max_le
    · norm_num
    · have hq : 0 ≤ featureRadius r x / eta :=
        div_nonneg hr (by norm_num [eta])
      linarith
  rw [featureHeight, abs_mul, abs_div, abs_of_nonneg hw0]
  norm_num
  nlinarith [abs_nonneg (profileCoefficient r : ℝ)]

/-! ## Actual frontier membership for every graph point -/

/-- Any point on the native signed graph over the closed square is on the
frontier of Q. The test points are moved only in the normal direction, so
this argument also covers the square perimeter and its corners. -/
theorem graph_point_frontier (r : Role) (x : E3)
    (hrad : featureRadius r x ≤ eta)
    (hgraph : featureNormalCoordinate r x = featureHeight r x) :
    x ∈ frontier Q := by
  have hh := featureHeight_abs_bound r x
  have hz : |featureNormalCoordinate r x| < eta := by
    rw [hgraph]
    norm_num [eta] at *
    linarith
  have htube : featureTubeSupport r x := ⟨hrad, hz.le⟩
  have hxQ : x ∈ Q := (mem_Q_iff_in_tube r x htube).mpr hgraph.le
  rw [frontier, Set.mem_diff]
  refine ⟨subset_closure hxQ, ?_⟩
  intro hxint
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
  let ε := min (δ / 2) ((eta - |featureNormalCoordinate r x|) / 2)
  have hε : 0 < ε := lt_min (by positivity) (by linarith)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hεeta : |featureNormalCoordinate r x| + ε < eta := by
    have h := min_le_right (δ / 2)
      ((eta - |featureNormalCoordinate r x|) / 2)
    change ε ≤ _ at h
    linarith
  let y := x + ε • featureNormal r
  have hydist : dist y x = ε := by
    simp [y, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have hyint : y ∈ interior Q := hball (by simpa [Metric.mem_ball, hydist] using hεδ)
  have hytube : featureTubeSupport r y := by
    refine ⟨by simpa [y] using hrad, ?_⟩
    rw [show y = x + ε • featureNormal r from rfl, normal_shift]
    exact (abs_add_le _ _).trans
      (by simpa [abs_of_pos hε] using hεeta.le)
  have hyineq := (mem_Q_iff_in_tube r y hytube).mp (interior_subset hyint)
  simp only [y, normal_shift, height_normal_shift, hgraph] at hyineq
  linarith

/-! Helpers for the finite feature graphs and triangles are below. -/

private theorem frameCoordinate_add (x y : E3) (i : Nat) :
    frameCoordinate (x + y) i = frameCoordinate x i + frameCoordinate y i := by
  unfold frameCoordinate
  split_ifs <;> simp

private theorem frameCoordinate_smul (x : E3) (a : ℝ) (i : Nat) :
    frameCoordinate (a • x) i = a * frameCoordinate x i := by
  unfold frameCoordinate
  split_ifs <;> simp

private theorem affine_difference (x y c : E3) (a b : ℝ) (hab : a + b = 1) :
    (a • x + b • y) - c = a • (x - c) + b • (y - c) := by
  rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]

private theorem chartU_affine (r : Role) (x y : E3)
    (a b : ℝ) (hab : a + b = 1) :
    chartU r (a • x + b • y) = a * chartU r x + b * chartU r y := by
  unfold chartU
  rw [affine_difference x y _ a b hab,
    frameCoordinate_add, frameCoordinate_smul, frameCoordinate_smul]

private theorem chartV_affine (r : Role) (x y : E3)
    (a b : ℝ) (hab : a + b = 1) :
    chartV r (a • x + b • y) = a * chartV r x + b * chartV r y := by
  unfold chartV
  rw [affine_difference x y _ a b hab,
    frameCoordinate_add, frameCoordinate_smul, frameCoordinate_smul]

private theorem chartZ_affine (r : Role) (x y : E3)
    (a b : ℝ) (hab : a + b = 1) :
    featureNormalCoordinate r (a • x + b • y) =
      a * featureNormalCoordinate r x + b * featureNormalCoordinate r y := by
  unfold featureNormalCoordinate
  rw [affine_difference x y _ a b hab,
    frameCoordinate_add, frameCoordinate_smul, frameCoordinate_smul]
  ring

private def sectorRadius (r : Role) (k : Fin 4) (x : E3) : ℝ :=
  if k.val = 0 then -chartU r x
  else if k.val = 1 then chartV r x
  else if k.val = 2 then chartU r x
  else -chartV r x

private theorem sectorRadius_affine (r : Role) (k : Fin 4) (x y : E3)
    (a b : ℝ) (hab : a + b = 1) :
    sectorRadius r k (a • x + b • y) =
      a * sectorRadius r k x + b * sectorRadius r k y := by
  fin_cases k <;>
    simp [sectorRadius, chartU_affine r x y a b hab,
      chartV_affine r x y a b hab] <;> ring

private def facetRegion (r : Role) (k : Fin 4) : Set E3 :=
  {x | -sectorRadius r k x ≤ chartU r x ∧
    chartU r x ≤ sectorRadius r k x ∧
    -sectorRadius r k x ≤ chartV r x ∧
    chartV r x ≤ sectorRadius r k x ∧
    0 ≤ sectorRadius r k x ∧ sectorRadius r k x ≤ eta ∧
    featureNormalCoordinate r x =
      ((profileCoefficient r : ℝ) / 10000) * (1 - sectorRadius r k x / eta)}

private theorem facetRegion_convex (r : Role) (k : Fin 4) :
    Convex ℝ (facetRegion r k) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxu0, hxu1, hxv0, hxv1, hx0, hx1, hxz⟩
  rcases hy with ⟨hyu0, hyu1, hyv0, hyv1, hy0, hy1, hyz⟩
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [sectorRadius_affine r k x y a b hab,
    chartU_affine r x y a b hab, chartV_affine r x y a b hab,
    chartZ_affine r x y a b hab]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := add_le_add (mul_le_mul_of_nonneg_left hxu0 ha)
      (mul_le_mul_of_nonneg_left hyu0 hb)
    linarith
  · exact add_le_add (mul_le_mul_of_nonneg_left hxu1 ha)
      (mul_le_mul_of_nonneg_left hyu1 hb)
  · have h := add_le_add (mul_le_mul_of_nonneg_left hxv0 ha)
      (mul_le_mul_of_nonneg_left hyv0 hb)
    linarith
  · exact add_le_add (mul_le_mul_of_nonneg_left hxv1 ha)
      (mul_le_mul_of_nonneg_left hyv1 hb)
  · positivity
  · have h := add_le_add (mul_le_mul_of_nonneg_left hx1 ha)
      (mul_le_mul_of_nonneg_left hy1 hb)
    nlinarith [hab]
  · rw [hxz, hyz]
    calc
      _ = ((profileCoefficient r : ℝ) / 10000) *
          ((a + b) - (a * sectorRadius r k x + b * sectorRadius r k y) / eta) := by ring
      _ = _ := by rw [hab]

private def cornerU (k : Fin 4) : ℝ :=
  (if k.val = 0 ∨ k.val = 1 then -1 else 1) * eta
private def cornerV (k : Fin 4) : ℝ :=
  (if k.val = 0 ∨ k.val = 3 then -1 else 1) * eta

private theorem corner_eq_chart (r : Role) (k : Fin 4) :
    featureCorner r k = chartPoint r (cornerU k) (cornerV k) 0 := by
  simp [featureCorner, chartPoint, cornerU, cornerV]

private theorem apex_eq_chart (r : Role) :
    featureApex r = chartPoint r 0 0 ((profileCoefficient r : ℝ) / 10000) := by
  simp [featureApex, chartPoint]

private theorem facet_vertices (r : Role) (k : Fin 4) :
    featureCorner r k ∈ facetRegion r k ∧
    featureCorner r (nextCorner k) ∈ facetRegion r k ∧
    featureApex r ∈ facetRegion r k := by
  simp only [facetRegion, Set.mem_setOf_eq, corner_eq_chart, apex_eq_chart]
  fin_cases k <;>
    simp [sectorRadius, cornerU, cornerV, nextCorner, eta,
      chartU_chartPoint, chartV_chartPoint, chartZ_chartPoint]

private theorem facet_radius (r : Role) (k : Fin 4) {x : E3}
    (hx : x ∈ facetRegion r k) : featureRadius r x = sectorRadius r k x := by
  rcases hx with ⟨hu0, hu1, hv0, hv1, _, _, _⟩
  change max |chartU r x| |chartV r x| = sectorRadius r k x
  apply le_antisymm
  · exact max_le (abs_le.mpr ⟨hu0, hu1⟩) (abs_le.mpr ⟨hv0, hv1⟩)
  · fin_cases k
    · exact (neg_le_abs _).trans (le_max_left _ _)
    · exact (le_abs_self _).trans (le_max_right _ _)
    · exact (le_abs_self _).trans (le_max_left _ _)
    · exact (neg_le_abs _).trans (le_max_right _ _)

/-- The actual triangular feature surface, not merely its sampled vertices,
lies on the set-defined Q frontier. -/
theorem nativeFeatureSurface_frontier (r : Role) :
    nativeFeatureSurface r ⊆ frontier Q := by
  intro x hx
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
  have hverts := facet_vertices r k
  have hsubset : ({featureCorner r k, featureCorner r (nextCorner k),
      featureApex r} : Set E3) ⊆ facetRegion r k := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hverts.1
    · exact hverts.2.1
    · exact hverts.2.2
  -- API?: expected Mathlib lemma: convexHull_min : s ⊆ t → Convex ℝ t → convexHull ℝ s ⊆ t.
  have hxf : x ∈ facetRegion r k :=
    convexHull_min hsubset (facetRegion_convex r k) hxk
  have hradius := facet_radius r k hxf
  have h0 := hxf.2.2.2.2.1
  have h1 := hxf.2.2.2.2.2.1
  have hz := hxf.2.2.2.2.2.2
  apply graph_point_frontier r x (by simpa [hradius] using h1)
  rw [featureHeight, hradius, max_eq_right]
  · exact hz
  · have heta : 0 < eta := by norm_num [eta]
    have hd : sectorRadius r k x / eta ≤ 1 := (div_le_one heta).mpr h1
    linarith

/-- The closed edge graph lies in its triangular surface. -/
theorem nativeFeatureGraph_subset_surface (r : Role) :
    nativeFeatureGraph r ⊆ nativeFeatureSurface r := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    -- API?: expected Mathlib lemma: Convex.segment_subset, applied to the convex hull.
    apply (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) hk
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    apply (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (by simp))
      (subset_convexHull ℝ _ (by simp)) hk

theorem nativeFeatureGraph_frontier (r : Role) :
    nativeFeatureGraph r ⊆ frontier Q :=
  (nativeFeatureGraph_subset_surface r).trans (nativeFeatureSurface_frontier r)

end
end R44.DischargeGeometry
