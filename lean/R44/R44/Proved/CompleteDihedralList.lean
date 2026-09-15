/- -- [compile-fix: promoted to Proved after exchange 7]
Discharge target: Hypotheses.complete_dihedral_list (A-L3.1).
Written argument: proof/ALIGNMENT_PROOF.md §1 and §3, Lemma 3.1;
proof/PROOFS_registered.md §1.1–1.3 supplies the same native tent geometry.
No ERRATA entry changes A-L3.1. E1 and E3 concern subsequent applications,
not this proposition.

-- [compile-fix begin: update provenance after exchange 7]
Status: DISCHARGED; the shared MeshSemantics chain is admission-free.
-- [compile-fix end]
The endpoint proposition is copied verbatim from LogicalSpine.lean.
No existing statement or definition is changed. No Hypotheses inhabitant is
assumed, and no field of Hypotheses is used.

API policy: upstream revision fabf563a7c95a166b8d7b6efca11c8b4dc9d911f
could not be fetched. Calls checked against current upstream documentation,
but not that revision, carry API? comments with the expected statement.
-/
import R44.Proved.MeshSemantics -- [compile-fix: promoted after exchange 7]

/-!
# First F1 delivery: complete_dihedral_list

The arithmetic and finite-certificate interpretation below do not assume the
geometric remainder. The one missing lemma is the semantic interpretation
of the literal mesh as boundary strata and tangent-cone volumes of the
*set-theoretically defined* Q. In particular, a successful mesh-angle Boolean
check is not silently used as a proof of a Lebesgue-volume identity.
-/

namespace R44

open Set
open Generated

noncomputable section

set_option maxRecDepth 100000

/-! ## Extract finite information; do not re-run native_decide -/

/-- Pure list argument: filterMap cannot increase length. -/
private theorem filterMap_length_bound {α β : Type*}
    (f : α → Option β) (xs : List α) :
    (xs.filterMap f).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      cases hfa : f a <;> simp [hfa] at * <;> omega

/-- Equality of lengths makes a filterMap total on its input list. -/
private theorem filterMap_total_of_length {α β : Type*}
    (f : α → Option β) (xs : List α)
    (h : (xs.filterMap f).length = xs.length) :
    ∀ a ∈ xs, ∃ b, f a = some b := by
  revert h
  induction xs with
  | nil => simp
  | cons a xs ih =>
      intro h
      cases hfa : f a with
      | none =>
          have hle := filterMap_length_bound f xs
          have hlen : (xs.filterMap f).length = xs.length + 1 := by
            simpa [hfa] using h
          omega
      | some b =>
          have hlen : (xs.filterMap f).length = xs.length := by
            simpa [hfa] using h
          intro x hx
          rcases List.mem_cons.mp hx with hxa | hxs
          · subst x
            exact ⟨b, hfa⟩
          · exact ih hlen x hxs

/-- Extract total classification from the already certified mesh audit.
No evaluation of classifyMeshEdge is performed here. -/
private theorem mesh_classifier_total (haudit : meshAngleAuditCheck = true) :
    ∀ key ∈ meshGeometricEdgeKeys, ∃ c : Nat × Nat × Int,
      classifyMeshEdge key = some c := by
  have hparts := haudit
  unfold meshAngleAuditCheck at hparts
  simp only [Bool.and_eq_true] at hparts
  have hkeysB : (meshGeometricEdgeKeys.length == 6408) = true := by tauto
  have hclassesB : (meshAngleClasses.length == 6408) = true := by tauto
  have hkeys : meshGeometricEdgeKeys.length = 6408 := by simpa using hkeysB
  have hclasses : meshAngleClasses.length = 6408 := by simpa using hclassesB
  have hlen : (meshGeometricEdgeKeys.filterMap classifyMeshEdge).length =
      meshGeometricEdgeKeys.length := by
    change meshAngleClasses.length = meshGeometricEdgeKeys.length
    exact hclasses.trans hkeys.symm
  exact filterMap_total_of_length classifyMeshEdge meshGeometricEdgeKeys hlen

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
private theorem coefficient_bounds (hprofile : profileCanonicalCheck = true)
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

/-- Read the finite arithmetic certificate as a universally quantified
integer noncollision fact. The certificate is not recomputed. -/
private theorem cross_equation_forbidden
    (hcert : deviationsDistinctCheck = true) (i j : Fin 12) :
    10000 * (i.val + 1)^2 ≠ 20000 * (j.val + 1)^2 + (j.val + 1)^4 := by
  let indices : List Nat := (List.range 12).map (fun n => n + 1)
  have hi : i.val + 1 ∈ indices :=
    List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
  have hj : j.val + 1 ∈ indices :=
    List.mem_map.mpr ⟨j.val, List.mem_range.mpr j.isLt, rfl⟩
  have hp : (i.val + 1, j.val + 1) ∈ allPairs indices := by
    exact List.mem_flatMap.mpr
      ⟨i.val + 1, hi, List.mem_map.mpr ⟨j.val + 1, hj, rfl⟩⟩
  change (allPairs indices).all
    (fun ij => 10000 * ij.1^2 != 20000 * ij.2^2 + ij.2^4) = true at hcert
  have hn := List.all_eq_true.mp hcert (i.val + 1, j.val + 1) hp
  simpa using hn

/-! ## Real angle arithmetic, independent of the geometric remainder -/

private def slopeAt (i : Fin 12) : ℝ := ((i.val : ℝ) + 1) / 100

private theorem slope_bounds (i : Fin 12) :
    0 < slopeAt i ∧ slopeAt i ≤ 3 / 25 := by
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hiLimit : i.val < 12 := i.isLt
  have hi11 : (i.val : ℝ) ≤ 11 := by exact_mod_cast (show i.val ≤ 11 by omega)
  dsimp [slopeAt]
  constructor <;> linarith

private theorem slope_sq_bound (i : Fin 12) :
    (slopeAt i)^2 ≤ 9 / 625 := by
  have hb := slope_bounds i
  have hp : 0 ≤ ((3 / 25 : ℝ) - slopeAt i) * ((3 / 25 : ℝ) + slopeAt i) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

private theorem slope_quartic_bound (i : Fin 12) :
    (1 + (slopeAt i)^2)^2 < 2 := by
  have hb := slope_sq_bound i
  have hp : 0 ≤ ((634 / 625 : ℝ) - (1 + (slopeAt i)^2)) *
      ((634 / 625 : ℝ) + (1 + (slopeAt i)^2)) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith

private theorem ridge_input_bounds (i : Fin 12) :
    0 < 1 / (1 + (slopeAt i)^2) ∧ 1 / (1 + (slopeAt i)^2) < 1 := by
  have ht := (slope_bounds i).1
  have ht2 : 0 < (slopeAt i)^2 := by
    simpa only [pow_two] using mul_pos ht ht
  have hd : 0 < 1 + (slopeAt i)^2 := by positivity
  constructor
  · positivity
  · apply (div_lt_iff₀ hd).2
    nlinarith

private theorem base_bounds (i : Fin 12) :
    0 < baseDeviation i ∧ baseDeviation i < Real.pi / 4 := by
  change 0 < Real.arctan (slopeAt i) ∧ Real.arctan (slopeAt i) < Real.pi / 4
  have hb := slope_bounds i
  constructor
  · exact Real.arctan_pos.mpr hb.1 -- API?: expected Mathlib lemma: 0 < arctan x ↔ 0 < x.
  · rw [← Real.arctan_one] -- API?: expected Mathlib lemma: arctan 1 = pi/4.
    exact Real.arctan_strictMono (by linarith : slopeAt i < 1) -- API?: expected Mathlib lemma: StrictMono Real.arctan.

private theorem ridge_cos (i : Fin 12) :
    Real.cos (ridgeDeviation i) = 1 / (1 + (slopeAt i)^2) := by
  change Real.cos (Real.arccos (1 / (1 + (slopeAt i)^2))) = _
  have hb := ridge_input_bounds i
  exact Real.cos_arccos (by linarith) (le_of_lt hb.2) -- API?: expected Mathlib lemma: -1 ≤ x → x ≤ 1 → cos (arccos x) = x.

private theorem ridge_bounds (i : Fin 12) :
    0 < ridgeDeviation i ∧ ridgeDeviation i < Real.pi / 4 := by
  change 0 < Real.arccos (1 / (1 + (slopeAt i)^2)) ∧
    Real.arccos (1 / (1 + (slopeAt i)^2)) < Real.pi / 4
  have hu := ridge_input_bounds i
  have hd : 0 < 1 + (slopeAt i)^2 := by positivity
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num) -- API?: expected Mathlib lemma: 0 ≤ x → (sqrt x)^2 = x.
  have hden : 1 + (slopeAt i)^2 < Real.sqrt 2 := by
    nlinarith [slope_quartic_bound i]
  have hrecip : 1 / Real.sqrt 2 < 1 / (1 + (slopeAt i)^2) := by
    apply (div_lt_div_iff₀ hs0 hd).2
    simpa only [one_mul] using hden
  have hcos : Real.cos (Real.pi / 4) = 1 / Real.sqrt 2 := by
    rw [← Real.arctan_one] -- [compile-fix]
    convert Real.cos_arctan (1 : ℝ) using 1 -- [compile-fix]
    norm_num -- [compile-fix]
  have harccos : Real.arccos (1 / Real.sqrt 2) = Real.pi / 4 := by
    rw [← hcos]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos]) -- API?: expected Mathlib lemma: 0 ≤ x → x ≤ pi → arccos (cos x) = x.
  constructor
  · exact Real.arccos_pos.mpr hu.2 -- API?: expected Mathlib lemma: 0 < arccos x ↔ x < 1.
  · rw [← harccos]
    have hleft : (-1 : ℝ) ≤ 1 / Real.sqrt 2 := by
      have hpos : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
      linarith
    exact Real.arccos_lt_arccos hleft hrecip (le_of_lt hu.2) -- API?: expected Mathlib lemma: -1 ≤ x → x < y → y ≤ 1 → arccos y < arccos x.

private theorem slope_injective : Function.Injective slopeAt := by
  intro i j hij
  have hreal : (i.val : ℝ) = j.val := by
    dsimp [slopeAt] at hij
    linarith
  apply Fin.ext
  exact_mod_cast hreal

private theorem base_injective : Function.Injective baseDeviation := by
  intro i j hij
  have htan := congrArg Real.tan hij
  change Real.tan (Real.arctan (slopeAt i)) = Real.tan (Real.arctan (slopeAt j)) at htan
  simp only [Real.tan_arctan] at htan -- API?: expected Mathlib lemma: tan (arctan x) = x.
  exact slope_injective htan

private theorem ridge_injective : Function.Injective ridgeDeviation := by
  intro i j hij
  have hcos := congrArg Real.cos hij
  rw [ridge_cos, ridge_cos] at hcos
  have hden := congrArg (fun x : ℝ => x⁻¹) hcos
  simp only [one_div, inv_inv] at hden
  have hprod : (slopeAt i - slopeAt j) * (slopeAt i + slopeAt j) = 0 := by
    nlinarith
  have hs : slopeAt i = slopeAt j := by
    rcases mul_eq_zero.mp hprod with hminus | hplus
    · linarith
    · have hi := (slope_bounds i).1
      have hj := (slope_bounds j).1
      linarith
  exact slope_injective hs

/-- A base/ridge collision implies exactly the integer equation excluded by
R44.deviations_distinct. No arctangent values are approximated. -/
private theorem base_ne_ridge (hcert : deviationsDistinctCheck = true)
    (i j : Fin 12) : baseDeviation i ≠ ridgeDeviation j := by
  intro heq
  have hcos := congrArg (fun x : ℝ => (Real.cos x)^2) heq
  change (Real.cos (Real.arctan (slopeAt i)))^2 =
      (Real.cos (ridgeDeviation j))^2 at hcos
  rw [Real.cos_sq_arctan, ridge_cos, div_pow, one_pow] at hcos -- API?: expected Mathlib lemma: cos (arctan x)^2 = 1/(1+x^2).
  have hden := congrArg (fun x : ℝ => x⁻¹) hcos
  simp only [one_div, inv_inv] at hden
  have hreal : (10000 : ℝ) * ((i.val : ℝ) + 1)^2 =
      20000 * ((j.val : ℝ) + 1)^2 + ((j.val : ℝ) + 1)^4 := by
    dsimp [slopeAt] at hden
    nlinarith [hden]
  have hnat : 10000 * (i.val + 1)^2 =
      20000 * (j.val + 1)^2 + (j.val + 1)^4 := by
    exact_mod_cast hreal
  exact cross_equation_forbidden hcert i j hnat

private theorem all_deviations_injective (hcert : deviationsDistinctCheck = true) :
    Function.Injective featureDeviation := by
  intro i j hij
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  by_cases hi12 : i < 12
  · by_cases hj12 : j < 12
    · have heq : baseDeviation ⟨i, hi12⟩ = baseDeviation ⟨j, hj12⟩ := by
        simpa only [featureDeviation, dif_pos hi12, dif_pos hj12] using hij
      have hv := congrArg Fin.val (base_injective heq)
      exact Fin.ext hv
    · have heq : baseDeviation ⟨i, hi12⟩ =
          ridgeDeviation ⟨j - 12, by omega⟩ := by
        simpa only [featureDeviation, dif_pos hi12, dif_neg hj12] using hij
      exact False.elim (base_ne_ridge hcert _ _ heq)
  · by_cases hj12 : j < 12
    · have heq : ridgeDeviation ⟨i - 12, by omega⟩ =
          baseDeviation ⟨j, hj12⟩ := by
        simpa only [featureDeviation, dif_neg hi12, dif_pos hj12] using hij
      exact False.elim (base_ne_ridge hcert _ _ heq.symm)
    · have heq : ridgeDeviation ⟨i - 12, by omega⟩ =
          ridgeDeviation ⟨j - 12, by omega⟩ := by
        simpa only [featureDeviation, dif_neg hi12, dif_neg hj12] using hij
      have hv : i - 12 = j - 12 := congrArg Fin.val (ridge_injective heq)
      apply Fin.ext
      have hi12 : 12 ≤ i := Nat.le_of_not_gt hi12 -- [compile-fix]
      have hj12 : 12 ≤ j := Nat.le_of_not_gt hj12 -- [compile-fix]
      change i = j -- [compile-fix]
      calc -- [compile-fix]
        i = (i - 12) + 12 := (Nat.sub_add_cancel hi12).symm -- [compile-fix]
        _ = (j - 12) + 12 := congrArg (· + 12) hv -- [compile-fix]
        _ = j := Nat.sub_add_cancel hj12 -- [compile-fix]

private theorem all_deviations_bounds (k : Fin 24) :
    0 < featureDeviation k ∧ featureDeviation k < Real.pi / 4 := by
  rcases k with ⟨k, hk⟩
  by_cases hk12 : k < 12
  · simpa only [featureDeviation, dif_pos hk12] using base_bounds ⟨k, hk12⟩
  · simpa only [featureDeviation, dif_neg hk12] using
      ridge_bounds ⟨k - 12, by omega⟩

/-! ## The single unresolved finite-to-continuous bridge -/

/-- Semantic soundness of the oriented native mesh for the concrete Q.

This lemma is narrower than CompleteDihedralList: it supplies only its actual
boundary/dihedral geometry. Coefficient bounds, totality of the classifier,
distinctness, and the range of all real deviations are established above.
It does not take CompleteDihedralList, any Hypotheses record, or any other
residual field as an input.
-/
private theorem complete_native_mesh_dihedral_semantics -- [compile-fix]
    (hmesh : solidMeshCheck = true)
    (haudit : meshAngleAuditCheck = true)
    (hprofile : profileCanonicalCheck = true) :
    (∀ r : Role, nativeFeatureGraph r ⊆ frontier Q ∧
      nativeFeatureSurface r ⊆ frontier Q) ∧
    (∀ r : Role, HasFeatureDihedral Q r .base ∧ HasFeatureDihedral Q r .ridge) ∧
    (∀ key ∈ meshGeometricEdgeKeys, ∀ c : Nat × Nat × Int,
      classifyMeshEdge key = some c → HasMeshDihedralClass Q key c) := by
  exact R44.native_mesh_dihedral_semantics hmesh haudit hprofile -- [compile-fix]

/-! ## Frozen endpoint: no added premises and no changed definitions -/

/-- A-L3.1 endpoint, conditional only on the four premises in the frozen
field. The dependency chain is admission-free. -- [compile-fix] -/
theorem complete_dihedral_list_holds :
    solidMeshCheck = true → meshAngleAuditCheck = true →
      profileCanonicalCheck = true → deviationsDistinctCheck = true →
        CompleteDihedralList Q := by
  intro hmesh haudit hprofile hdistinct
  obtain ⟨hboundary, hfeature, hmeshAngles⟩ :=
    complete_native_mesh_dihedral_semantics hmesh haudit hprofile -- [compile-fix]
  unfold CompleteDihedralList
  refine ⟨hboundary, ?_, ?_, all_deviations_injective hdistinct,
    all_deviations_bounds⟩
  · intro r
    obtain ⟨hne, hle⟩ := coefficient_bounds hprofile r
    exact ⟨hne, hle, (hfeature r).1, (hfeature r).2⟩
  · intro key hkey
    obtain ⟨c, hc⟩ := mesh_classifier_total haudit key hkey
    exact ⟨c, hc, hmeshAngles key hkey c hc⟩

-- The existing exported certificates specialize the endpoint, with no
-- repeated evaluation. -- [compile-fix: exchange 7 closes the endpoint]
example : CompleteDihedralList Q :=
  complete_dihedral_list_holds solid_mesh_exact mesh_angle_audit
    profile_canonical deviations_distinct.1

end
end R44
