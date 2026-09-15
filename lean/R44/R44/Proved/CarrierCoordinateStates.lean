/- -- [compile-fix: promoted to Proved after exchange 7]
# A finite coordinate-state normal form for unchanged carrier edges

A-L2.2/A-L3.1. There are five possible strata in one carrier coordinate:
0, (0,1), 1, (1,2), 2. The 125-entry lookup below is generic Boolean
halfspace algebra, not mesh data. Its soundness is proved by cases and
extensional set equality. Entries 0,1,2 mean right, flat, reentrant;
-- [compile-fix: remove an accidental tactic token from documentation]
3 means that this coordinate state is not an ordinary dihedral stratum.
-/
import R44.Proved.CarrierBoundaryStrata -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeCarrierStrata
open Set DischargeOrdinary DischargeMeridian DischargeGeometry
noncomputable section
set_option maxHeartbeats 0

def coordinateState (s : Fin 5) (x : ℝ) : Prop :=
  match s.val with
  | 0 => x=0
  | 1 => 0<x ∧ x<1
  | 2 => x=1
  | 3 => 1<x ∧ x<2
  | _ => x=2

def coordinateStateCone (a b c : Fin 5) : Set E3 := {d |
  (∀i:Fin 3,((![a,b,c] i)=0 → 0≤d i) ∧ ((![a,b,c] i)=4 → d i≤0)) ∧
  ((∃i:Fin 3,(![a,b,c] i).val<2) ∨ ∃i:Fin 3,![a,b,c] i=2 ∧ d i≤0)}

private def stateCodes : List Nat :=
  [3,0,0,0,3,0,1,1,1,0,0,1,1,1,0,0,1,1,1,0,3,0,0,0,3,0,1,1,1,0,1,3,3,3,1,1,3,3,3,1,1,3,3,3,1,0,1,1,1,0,0,1,1,1,0,1,3,3,3,1,1,3,3,2,3,1,3,2,1,0,0,1,3,0,3,0,1,1,1,0,1,3,3,3,1,1,3,2,1,0,1,3,1,3,3,0,1,0,3,3,3,0,0,0,3,0,1,1,1,0,0,1,3,0,3,0,1,0,3,3,3,0,3,3,3]

def stateCode (a b c : Fin 5) : Nat :=
  R44.getD stateCodes (25*a.val+5*b.val+c.val) 3

-- [compile-fix R10: finite chart code used by the named native table hook]
private inductive CoordinateConeChart where
  | half (i : Fin 3) (positive : Bool)
  | right (i j : Fin 3) (positiveI positiveJ : Bool)
  | reentrant (i j : Fin 3) (positiveI positiveJ : Bool)
  deriving DecidableEq

private def stateCharts : List CoordinateConeChart :=
  [.half 0 false,.right 0 1 false false,.right 0 1 false false,.right 0 1 false false,.half 0 false,.right 0 2 false false,.half 0 false,.half 0 false,.half 0 false,.right 0 2 false true,.right 0 2 false false,.half 0 false,.half 0 false,.half 0 false,.right 0 2 false true,.right 0 2 false false,.half 0 false,.half 0 false,.half 0 false,.right 0 2 false true,.half 0 false,.right 0 1 false true,.right 0 1 false true,.right 0 1 false true,.half 0 false,.right 1 2 false false,.half 1 false,.half 1 false,.half 1 false,.right 1 2 false true,.half 2 false,.half 0 false,.half 0 false,.half 0 false,.half 2 true,.half 2 false,.half 0 false,.half 0 false,.half 0 false,.half 2 true,.half 2 false,.half 0 false,.half 0 false,.half 0 false,.half 2 true,.right 1 2 true false,.half 1 true,.half 1 true,.half 1 true,.right 1 2 true true,.right 1 2 false false,.half 1 false,.half 1 false,.half 1 false,.right 1 2 false true,.half 2 false,.half 0 false,.half 0 false,.half 0 false,.half 2 true,.half 2 false,.half 0 false,.half 0 false,.reentrant 0 1 true true,.half 0 false,.half 2 false,.half 0 false,.reentrant 0 2 true true,.half 0 true,.right 0 2 true true,.right 1 2 true false,.half 1 true,.half 0 false,.right 0 1 true true,.half 0 false,.right 1 2 false false,.half 1 false,.half 1 false,.half 1 false,.right 1 2 false true,.half 2 false,.half 0 false,.half 0 false,.half 0 false,.half 2 true,.half 2 false,.half 0 false,.reentrant 1 2 true true,.half 1 true,.right 1 2 true true,.half 2 false,.half 0 false,.half 2 true,.half 0 false,.half 0 false,.right 1 2 true false,.half 1 true,.right 2 1 true true,.half 0 false,.half 0 false,.half 0 false,.right 0 1 true false,.right 0 1 true false,.right 0 1 true false,.half 0 false,.right 0 2 true false,.half 0 true,.half 0 true,.half 0 true,.right 0 2 true true,.right 0 2 true false,.half 0 true,.half 0 false,.right 1 0 true true,.half 0 false,.right 0 2 true false,.half 0 true,.right 2 0 true true,.half 0 false,.half 0 false,.half 0 false,.right 0 1 true true,.half 0 false,.half 0 false,.half 0 false]

private def stateChart (a b c : Fin 5) : CoordinateConeChart :=
  R44.getD stateCharts (25*a.val+5*b.val+c.val) (.half 0 false)

private def chartCode : CoordinateConeChart → Nat
  | .half .. => 1
  | .right .. => 0
  | .reentrant .. => 2

private def chartValid : CoordinateConeChart → Bool
  | .half .. => true
  | .right i j .. => decide (i ≠ j)
  | .reentrant i j .. => decide (i ≠ j)

private def signedTest (positive lo hi : Bool) : Bool :=
  if positive then hi else lo

private def stateConeBool (a b c : Fin 5)
    (lo hi : Fin 3 → Bool) : Bool :=
  ((!decide (a=0) || lo 0) && (!decide (a=4) || hi 0) &&
   (!decide (b=0) || lo 1) && (!decide (b=4) || hi 1) &&
   (!decide (c=0) || lo 2) && (!decide (c=4) || hi 2)) &&
  (decide (a.val<2) || decide (b.val<2) || decide (c.val<2) ||
   (decide (a=2) && hi 0) || (decide (b=2) && hi 1) ||
   (decide (c=2) && hi 2))

private def chartBool : CoordinateConeChart → (Fin 3 → Bool) →
    (Fin 3 → Bool) → Bool
  | .half i p, lo, hi => signedTest p (lo i) (hi i)
  | .right i j pi pj, lo, hi =>
      signedTest pi (lo i) (hi i) && signedTest pj (lo j) (hi j)
  | .reentrant i j pi pj, lo, hi =>
      signedTest pi (lo i) (hi i) || signedTest pj (lo j) (hi j)

private def chartSet : CoordinateConeChart → Set E3
  | .half i p => {d | (if p then (1:ℝ) else -1) * d i ≤ 0}
  | .right i j pi pj => {d |
      (if pi then (1:ℝ) else -1) * d i ≤ 0 ∧
      (if pj then (1:ℝ) else -1) * d j ≤ 0}
  | .reentrant i j pi pj => {d |
      (if pi then (1:ℝ) else -1) * d i ≤ 0 ∨
      (if pj then (1:ℝ) else -1) * d j ≤ 0}

-- [compile-fix R10: encode the six Boolean inequality tests in one Fin 64]
private def stateLoBit (m : Fin 64) (i : Fin 3) : Bool :=
  decide (m.val.testBit i.val)

private def stateHiBit (m : Fin 64) (i : Fin 3) : Bool :=
  decide (m.val.testBit (i.val + 3))

private def fin5s : List (Fin 5) := List.ofFn id
private def fin64s : List (Fin 64) := List.ofFn id

-- [compile-fix R10: explicit eight valuations avoid compiler expansion of a
-- function-space Fintype while checking the same closed truth table]
private def boolFunctions : List (Fin 3 → Bool) :=
  [![false,false,false], ![false,false,true], ![false,true,false],
   ![false,true,true], ![true,false,false], ![true,false,true],
   ![true,true,false], ![true,true,true]]

private theorem mem_boolFunctions (f : Fin 3 → Bool) : f ∈ boolFunctions := by
  have he : f = ![f 0, f 1, f 2] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  cases f 0 <;> cases f 1 <;> cases f 2 <;> simp [boolFunctions]

private def stateTableEntryCheck (a b c : Fin 5) : Bool :=
  chartValid (stateChart a b c) &&
  decide (chartCode (stateChart a b c) = stateCode a b c) &&
  boolFunctions.all fun lo =>
    boolFunctions.all fun hi =>
      stateConeBool a b c lo hi == chartBool (stateChart a b c) lo hi

def carrierCoordinateStatesTableCheck : Bool :=
  fin5s.all fun a => fin5s.all fun b => fin5s.all fun c =>
    !decide (stateCode a b c < 3) ||
      (decide (a.val ≤ 2 ∨ b.val ≤ 2 ∨ c.val ≤ 2) &&
        stateTableEntryCheck a b c)
    -- [compile-fix R10: the same single table hook also certifies the finite
    -- low-coordinate fact used by the delivered continuous bridge]

/-- [compile-fix R10] The closed decidable 125-state truth table. -/
theorem carrier_coordinate_states_table :
    carrierCoordinateStatesTableCheck = true := by
  native_decide

private theorem state_table_facts (a b c : Fin 5)
    (h : stateCode a b c < 3) :
    decide (a.val ≤ 2 ∨ b.val ≤ 2 ∨ c.val ≤ 2) = true ∧
      stateTableEntryCheck a b c = true := by
  have ha : a ∈ fin5s := by fin_cases a <;> simp [fin5s]
  have hb : b ∈ fin5s := by fin_cases b <;> simp [fin5s]
  have hc : c ∈ fin5s := by fin_cases c <;> simp [fin5s]
  have h1 := List.all_eq_true.mp carrier_coordinate_states_table a ha
  have h2 := List.all_eq_true.mp h1 b hb
  have h3 := List.all_eq_true.mp h2 c hc
  -- [compile-fix R10: expose only the outer Boolean guard; broad `simp`
  -- unfolded the 125-entry chart lookup and exceeded the compile budget]
  change ((!decide (stateCode a b c < 3) ||
    (decide (a.val ≤ 2 ∨ b.val ≤ 2 ∨ c.val ≤ 2) &&
      stateTableEntryCheck a b c)) = true) at h3
  rw [decide_eq_true h] at h3
  simpa only [Bool.not_true, Bool.false_or, Bool.and_eq_true] using h3

private theorem state_table_entry (a b c : Fin 5)
    (h : stateCode a b c < 3) : stateTableEntryCheck a b c = true :=
  (state_table_facts a b c h).2

private theorem state_tag_has_low_coordinate (a b c : Fin 5)
    (h : stateCode a b c < 3) : a.val ≤ 2 ∨ b.val ≤ 2 ∨ c.val ≤ 2 :=
  of_decide_eq_true (state_table_facts a b c h).1

private theorem ordinary_chartSet (ch : CoordinateConeChart)
    (hv : chartValid ch = true) :
    ∃ code : Fin 3, code.val = chartCode ch ∧ OrdinaryCone (chartSet ch) code := by
  cases ch with
  | half i p =>
      cases p
      · exact ⟨1, rfl, by simpa [chartSet] using
          OrdinaryCone.half i (-1:ℝ) (Or.inr rfl)⟩
      · exact ⟨1, rfl, by simpa [chartSet] using
          OrdinaryCone.half i (1:ℝ) (Or.inl rfl)⟩
  | right i j pi pj =>
      have hij : i ≠ j := by simpa [chartValid] using hv
      cases pi <;> cases pj
      · exact ⟨0, rfl, by simpa [chartSet] using
          OrdinaryCone.right i j hij (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl)⟩
      · exact ⟨0, rfl, by simpa [chartSet] using
          OrdinaryCone.right i j hij (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl)⟩
      · exact ⟨0, rfl, by simpa [chartSet] using
          OrdinaryCone.right i j hij (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl)⟩
      · exact ⟨0, rfl, by simpa [chartSet] using
          OrdinaryCone.right i j hij (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl)⟩
  | reentrant i j pi pj =>
      have hij : i ≠ j := by simpa [chartValid] using hv
      cases pi <;> cases pj
      · exact ⟨2, rfl, by simpa [chartSet] using
          OrdinaryCone.reentrant i j hij (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl)⟩
      · exact ⟨2, rfl, by simpa [chartSet] using
          OrdinaryCone.reentrant i j hij (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl)⟩
      · exact ⟨2, rfl, by simpa [chartSet] using
          OrdinaryCone.reentrant i j hij (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl)⟩
      · exact ⟨2, rfl, by simpa [chartSet] using
          OrdinaryCone.reentrant i j hij (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl)⟩

-- [compile-fix R10: factor the continuous interpretation away from the
-- concrete 125-entry lookup, so no dependent case split unfolds the table]
private def lowerTests (d : E3) : Fin 3 → Bool := fun i => decide (0 ≤ d i)

private def upperTests (d : E3) : Fin 3 → Bool := fun i => decide (d i ≤ 0)

-- [compile-fix R10: Boolean-negated decisions interpreted without unfolding
-- the decision procedure for symbolic finite-coordinate equalities]
private theorem not_decide_eq_true_iff_not (p : Prop) [Decidable p] :
    (!decide p) = true ↔ ¬p := by
  by_cases hp : p <;> simp [hp]

private theorem stateConeBool_iff_mem (a b c : Fin 5) (d : E3) :
    (d ∈ coordinateStateCone a b c) ↔
      stateConeBool a b c (lowerTests d) (upperTests d) = true := by
  -- [compile-fix R10: restrict simplification to Boolean semantics and the
  -- three finite coordinates; unrestricted `simp` plus `tauto` was costly]
  simp only [coordinateStateCone, Set.mem_setOf_eq, stateConeBool,
    lowerTests, upperTests, Bool.and_eq_true, Bool.or_eq_true,
    Fin.forall_fin_succ, Fin.exists_fin_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
    decide_eq_true_eq, Fin.forall_fin_zero, Fin.exists_fin_zero,
    not_decide_eq_true_iff_not]
  simp only [and_true, or_false, imp_iff_not_or, and_assoc, or_assoc]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]

private theorem chartBool_iff_mem (ch : CoordinateConeChart) (d : E3) :
    chartBool ch (lowerTests d) (upperTests d) = true ↔ d ∈ chartSet ch := by
  cases ch with
  | half i p => cases p <;>
      simp [chartBool, chartSet, signedTest, lowerTests, upperTests]
  | right i j pi pj => cases pi <;> cases pj <;>
      simp [chartBool, chartSet, signedTest, lowerTests, upperTests]
  | reentrant i j pi pj => cases pi <;> cases pj <;>
      simp [chartBool, chartSet, signedTest, lowerTests, upperTests]


/- Every tag returned as ordinary has a concrete signed coordinate chart.
   [compile-fix: an ordinary comment may precede nested command options] -/
set_option linter.unusedSimpArgs false in -- [compile-fix: suppress finite-dispatch linter cost]
set_option linter.unusedTactic false in -- [compile-fix: suppress finite-dispatch linter cost]
set_option linter.unreachableTactic false in -- [compile-fix: suppress finite-dispatch linter cost]
theorem state_code_sound (a b c : Fin 5) (h : stateCode a b c<3) :
    ∃code:Fin 3,code.val=stateCode a b c ∧
      OrdinaryCone (coordinateStateCone a b c) code := by
  -- [compile-fix R10: derive the exact delivered proposition from the named
  -- finite table hook by a short propositional interpretation]
  have hentry := state_table_entry a b c h
  -- [compile-fix R10: unfold just the outer conjunction. Broad simplification
  -- reduced the symbolic 125-entry `stateChart` table during elaboration.]
  change (chartValid (stateChart a b c) &&
      decide (chartCode (stateChart a b c) = stateCode a b c) &&
      boolFunctions.all (fun lo =>
        boolFunctions.all (fun hi =>
          stateConeBool a b c lo hi ==
            chartBool (stateChart a b c) lo hi))) = true at hentry
  -- [compile-fix R10: project Boolean conjunctions without dependent case
  -- elimination, which tried to reduce the explicit eight-row function table]
  rw [Bool.and_eq_true] at hentry
  obtain ⟨hprefix, htable⟩ := hentry
  rw [Bool.and_eq_true] at hprefix
  obtain ⟨hv, hcodeBool⟩ := hprefix
  have hcode := of_decide_eq_true hcodeBool
  obtain ⟨code, hc, hordinary⟩ := ordinary_chartSet (stateChart a b c) hv
  refine ⟨code, hc.trans hcode, ?_⟩
  rw [show coordinateStateCone a b c = chartSet (stateChart a b c) by
    ext d
    -- [compile-fix R10: select the actual Boolean valuation directly from
    -- the finite function space, avoiding a 64-way kernel tactic split]
    have htlo := List.all_eq_true.mp htable (lowerTests d)
      (mem_boolFunctions (lowerTests d))
    have ht := List.all_eq_true.mp htlo (upperTests d)
      (mem_boolFunctions (upperTests d))
    have ht' : stateConeBool a b c (lowerTests d) (upperTests d) =
        chartBool (stateChart a b c) (lowerTests d) (upperTests d) := by
      simpa using ht
    have hbool : stateConeBool a b c (lowerTests d) (upperTests d) = true ↔
        chartBool (stateChart a b c) (lowerTests d) (upperTests d) = true := by
      rw [ht']
    exact (stateConeBool_iff_mem a b c d).trans
      (hbool.trans (chartBool_iff_mem (stateChart a b c) d))]
  exact hordinary
-- [compile-fix begin: R10 supersedes the exhaustive kernel proof below]
/- Superseded delivered exhaustive proof retained verbatim below.
  -- [compile-fix: choose the finite code before the case split, avoiding
  -- backtracking over an existential witness under the current tactic engine]
  refine ⟨⟨stateCode a b c, h⟩, rfl, ?_⟩
  fin_cases a <;> fin_cases b <;> fin_cases c
  -- [compile-fix: remove `fin_cases` identity wrappers before cone matching]
  all_goals simp only at h ⊢
  all_goals norm_num [stateCode,stateCodes,R44.getD] at h
  -- [compile-fix: normalize the finite lookup in the goal as well]
  all_goals norm_num [stateCode,stateCodes,R44.getD]
  -- [compile-fix: close the three proof-irrelevance-sensitive reentrant cases
  -- before the generic conversion dispatch]
  case «2».«2».«3» =>
    change OrdinaryCone (coordinateStateCone (2:Fin 5) (2:Fin 5) (3:Fin 5)) (2:Fin 3)
    convert OrdinaryCone.reentrant (0:Fin 3) (1:Fin 3) (by omega)
      (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos] <;> tauto
  case «2».«3».«2» =>
    change OrdinaryCone (coordinateStateCone (2:Fin 5) (3:Fin 5) (2:Fin 5)) (2:Fin 3)
    convert OrdinaryCone.reentrant (0:Fin 3) (2:Fin 3) (by omega)
      (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos] <;> tauto
  case «3».«2».«2» =>
    change OrdinaryCone (coordinateStateCone (3:Fin 5) (2:Fin 5) (2:Fin 5)) (2:Fin 3)
    convert OrdinaryCone.reentrant (1:Fin 3) (2:Fin 3) (by omega)
      (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos] <;> tauto
  -- [compile-fix: dispatch each surviving finite state directly; generic
  -- tactic backtracking over the 30 cone forms exceeded the compile budget]
  case «0».«0».«1» =>
    convert OrdinaryCone.right (0 : Fin 3) (1 : Fin 3) (by omega)
      (-1 : ℝ) (-1 : ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«0».«2» =>
    convert OrdinaryCone.right (0 : Fin 3) (1 : Fin 3) (by omega)
      (-1 : ℝ) (-1 : ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«0».«3» =>
    convert OrdinaryCone.right (0 : Fin 3) (1 : Fin 3) (by omega)
      (-1 : ℝ) (-1 : ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«1».«0» =>
    convert OrdinaryCone.right (0 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (-1 : ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«1».«1» =>
    convert OrdinaryCone.half (0 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«1».«2» =>
    convert OrdinaryCone.half (0 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«1».«3» =>
    convert OrdinaryCone.half (0 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«1».«4» =>
    convert OrdinaryCone.right (0 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (1 : ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«2».«0» =>
    convert OrdinaryCone.right (0 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (-1 : ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«2».«1» =>
    convert OrdinaryCone.half (0 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«2».«2» =>
    convert OrdinaryCone.half (0 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«2».«3» =>
    convert OrdinaryCone.half (0 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«2».«4» =>
    convert OrdinaryCone.right (0 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (1 : ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«3».«0» =>
    convert OrdinaryCone.right (0 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (-1 : ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«3».«1» =>
    convert OrdinaryCone.half (0 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«3».«2» =>
    convert OrdinaryCone.half (0 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«3».«3» =>
    convert OrdinaryCone.half (0 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«3».«4» =>
    convert OrdinaryCone.right (0 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (1 : ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«4».«1» =>
    convert OrdinaryCone.right (0 : Fin 3) (1 : Fin 3) (by omega)
      (-1 : ℝ) (1 : ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«4».«2» =>
    convert OrdinaryCone.right (0 : Fin 3) (1 : Fin 3) (by omega)
      (-1 : ℝ) (1 : ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «0».«4».«3» =>
    convert OrdinaryCone.right (0 : Fin 3) (1 : Fin 3) (by omega)
      (-1 : ℝ) (1 : ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«0».«0» =>
    convert OrdinaryCone.right (1 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (-1 : ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«0».«1» =>
    convert OrdinaryCone.half (1 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«0».«2» =>
    convert OrdinaryCone.half (1 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«0».«3» =>
    convert OrdinaryCone.half (1 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«0».«4» =>
    convert OrdinaryCone.right (1 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (1 : ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«1».«0» =>
    convert OrdinaryCone.half (2 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«1».«4» =>
    convert OrdinaryCone.half (2 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«2».«0» =>
    convert OrdinaryCone.half (2 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«2».«4» =>
    convert OrdinaryCone.half (2 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«3».«0» =>
    convert OrdinaryCone.half (2 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«3».«4» =>
    convert OrdinaryCone.half (2 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«4».«0» =>
    convert OrdinaryCone.right (1 : Fin 3) (2 : Fin 3) (by omega)
      (1 : ℝ) (-1 : ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«4».«1» =>
    convert OrdinaryCone.half (1 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«4».«2» =>
    convert OrdinaryCone.half (1 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«4».«3» =>
    convert OrdinaryCone.half (1 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «1».«4».«4» =>
    convert OrdinaryCone.right (1 : Fin 3) (2 : Fin 3) (by omega)
      (1 : ℝ) (1 : ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«0».«0» =>
    convert OrdinaryCone.right (1 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (-1 : ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«0».«1» =>
    convert OrdinaryCone.half (1 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«0».«2» =>
    convert OrdinaryCone.half (1 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«0».«3» =>
    convert OrdinaryCone.half (1 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«0».«4» =>
    convert OrdinaryCone.right (1 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (1 : ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«1».«0» =>
    convert OrdinaryCone.half (2 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«1».«4» =>
    convert OrdinaryCone.half (2 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«2».«0» =>
    convert OrdinaryCone.half (2 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«3».«0» =>
    convert OrdinaryCone.half (2 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«3».«3» =>
    convert OrdinaryCone.half (0 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«3».«4» =>
    convert OrdinaryCone.right (0 : Fin 3) (2 : Fin 3) (by omega)
      (1 : ℝ) (1 : ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«4».«0» =>
    convert OrdinaryCone.right (1 : Fin 3) (2 : Fin 3) (by omega)
      (1 : ℝ) (-1 : ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«4».«1» =>
    convert OrdinaryCone.half (1 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «2».«4».«3» =>
    convert OrdinaryCone.right (0 : Fin 3) (1 : Fin 3) (by omega)
      (1 : ℝ) (1 : ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«0».«0» =>
    convert OrdinaryCone.right (1 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (-1 : ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«0».«1» =>
    convert OrdinaryCone.half (1 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«0».«2» =>
    convert OrdinaryCone.half (1 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«0».«3» =>
    convert OrdinaryCone.half (1 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«0».«4» =>
    convert OrdinaryCone.right (1 : Fin 3) (2 : Fin 3) (by omega)
      (-1 : ℝ) (1 : ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«1».«0» =>
    convert OrdinaryCone.half (2 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«1».«4» =>
    convert OrdinaryCone.half (2 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«2».«0» =>
    convert OrdinaryCone.half (2 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«2».«3» =>
    convert OrdinaryCone.half (1 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«2».«4» =>
    convert OrdinaryCone.right (1 : Fin 3) (2 : Fin 3) (by omega)
      (1 : ℝ) (1 : ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«3».«0» =>
    convert OrdinaryCone.half (2 : Fin 3) (-1 : ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«3».«2» =>
    convert OrdinaryCone.half (2 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«4».«0» =>
    convert OrdinaryCone.right (1 : Fin 3) (2 : Fin 3) (by omega)
      (1 : ℝ) (-1 : ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«4».«1» =>
    convert OrdinaryCone.half (1 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «3».«4».«2» =>
    convert OrdinaryCone.right (2 : Fin 3) (1 : Fin 3) (by omega)
      (1 : ℝ) (1 : ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«0».«1» =>
    convert OrdinaryCone.right (0 : Fin 3) (1 : Fin 3) (by omega)
      (1 : ℝ) (-1 : ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«0».«2» =>
    convert OrdinaryCone.right (0 : Fin 3) (1 : Fin 3) (by omega)
      (1 : ℝ) (-1 : ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«0».«3» =>
    convert OrdinaryCone.right (0 : Fin 3) (1 : Fin 3) (by omega)
      (1 : ℝ) (-1 : ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«1».«0» =>
    convert OrdinaryCone.right (0 : Fin 3) (2 : Fin 3) (by omega)
      (1 : ℝ) (-1 : ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«1».«1» =>
    convert OrdinaryCone.half (0 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«1».«2» =>
    convert OrdinaryCone.half (0 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«1».«3» =>
    convert OrdinaryCone.half (0 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«1».«4» =>
    convert OrdinaryCone.right (0 : Fin 3) (2 : Fin 3) (by omega)
      (1 : ℝ) (1 : ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«2».«0» =>
    convert OrdinaryCone.right (0 : Fin 3) (2 : Fin 3) (by omega)
      (1 : ℝ) (-1 : ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«2».«1» =>
    convert OrdinaryCone.half (0 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«2».«3» =>
    convert OrdinaryCone.right (1 : Fin 3) (0 : Fin 3) (by omega)
      (1 : ℝ) (1 : ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«3».«0» =>
    convert OrdinaryCone.right (0 : Fin 3) (2 : Fin 3) (by omega)
      (1 : ℝ) (-1 : ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«3».«1» =>
    convert OrdinaryCone.half (0 : Fin 3) (1 : ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«3».«2» =>
    convert OrdinaryCone.right (2 : Fin 3) (0 : Fin 3) (by omega)
      (1 : ℝ) (1 : ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto
  case «4».«4».«1» =>
    convert OrdinaryCone.right (0 : Fin 3) (1 : Fin 3) (by omega)
      (1 : ℝ) (1 : ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone, Fin.forall_fin_succ, Fin.exists_fin_succ, neg_nonpos] <;> tauto

  -- [compile-fix: assert that the explicit table closed every surviving case]
  all_goals done
  -- [compile-fix: take the first closing finite-case method without backtracking]
  all_goals first
  | convert OrdinaryCone.half (0:Fin 3) (1:ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.half (0:Fin 3) (-1:ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.half (1:Fin 3) (1:ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.half (1:Fin 3) (-1:ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.half (2:Fin 3) (1:ℝ) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.half (2:Fin 3) (-1:ℝ) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (0:Fin 3) (1:Fin 3) (by omega) (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (0:Fin 3) (1:Fin 3) (by omega) (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (0:Fin 3) (1:Fin 3) (by omega) (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (0:Fin 3) (1:Fin 3) (by omega) (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (0:Fin 3) (2:Fin 3) (by omega) (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (0:Fin 3) (2:Fin 3) (by omega) (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (0:Fin 3) (2:Fin 3) (by omega) (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (0:Fin 3) (2:Fin 3) (by omega) (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (1:Fin 3) (2:Fin 3) (by omega) (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (1:Fin 3) (2:Fin 3) (by omega) (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (1:Fin 3) (2:Fin 3) (by omega) (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.right (1:Fin 3) (2:Fin 3) (by omega) (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (0:Fin 3) (1:Fin 3) (by omega) (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (0:Fin 3) (1:Fin 3) (by omega) (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (0:Fin 3) (1:Fin 3) (by omega) (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (0:Fin 3) (1:Fin 3) (by omega) (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (0:Fin 3) (2:Fin 3) (by omega) (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (0:Fin 3) (2:Fin 3) (by omega) (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (0:Fin 3) (2:Fin 3) (by omega) (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (0:Fin 3) (2:Fin 3) (by omega) (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (1:Fin 3) (2:Fin 3) (by omega) (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (1:Fin 3) (2:Fin 3) (by omega) (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (1:Fin 3) (2:Fin 3) (by omega) (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
  | convert OrdinaryCone.reentrant (1:Fin 3) (2:Fin 3) (by omega) (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [coordinateStateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,
      neg_nonpos] <;> tauto <;> done
-/
-- [compile-fix end]
private theorem state_bounds {i : Fin 5} {x : ℝ} (h : coordinateState i x) :
    0≤x ∧ x≤2 := by
  fin_cases i <;> simp only [coordinateState] at h <;> constructor <;> linarith

private theorem state_tests {i : Fin 5} {x : ℝ} (h : coordinateState i x) :
    (x=0 ↔ i=0) ∧ (x=1 ↔ i=2) ∧ (x=2 ↔ i=4) ∧
      (x<1 ↔ i.val<2) ∧ (x≤1 ↔ i.val≤2) := by
  fin_cases i <;> simp only [coordinateState] at h
  all_goals repeat' constructor
  -- [compile-fix: introduce residual implications before arithmetic]
  all_goals norm_num at *
  all_goals first | assumption | linarith | (intro hh; simp_all <;> linarith)

/-- The finite state calculation is linked to actual real coordinates and
then to the frozen radial tangent cone. -/
theorem carrier_meridian_from_states (x : E3) (a b c : Fin 5)
    (ha : coordinateState a (x 0)) (hb : coordinateState b (x 1))
    (hc : coordinateState c (x 2)) (htag : stateCode a b c<3) :
    ∃code:Fin 3,code.val=stateCode a b c ∧
      Nonempty (AngularMeridian (tangentCone P x)
        (((code.val+1:Nat):ℝ)*Real.pi/2)) := by
  have hn : a.val≤2 ∨ b.val≤2 ∨ c.val≤2 :=
    state_tag_has_low_coordinate a b c htag
    -- [compile-fix R10: derive the identical finite proposition from the
    -- named table hook instead of a second exhaustive kernel case search]
  have hxP : x∈P := by
    rw [mem_P_iff_coordinates]
    refine ⟨(state_bounds ha).1,(state_bounds ha).2,
      (state_bounds hb).1,(state_bounds hb).2,
      (state_bounds hc).1,(state_bounds hc).2,?_⟩
    rcases hn with h|h|h
    · exact Or.inl ((state_tests ha).2.2.2.2.mpr h)
    · exact Or.inr (Or.inl ((state_tests hb).2.2.2.2.mpr h))
    · exact Or.inr (Or.inr ((state_tests hc).2.2.2.2.mpr h))
  have he : carrierCone x=coordinateStateCone a b c := by
    ext d
    simp only [carrierCone,coordinateStateCone,Set.mem_setOf_eq,
      Fin.forall_fin_succ,Fin.exists_fin_succ]
    -- [compile-fix: expose coordinate-test equivalences to propositional closure]
    have ha0 := (state_tests ha).1
    have ha1 := (state_tests ha).2.1
    have ha2 := (state_tests ha).2.2.1
    have hal := (state_tests ha).2.2.2.1
    have hb0 := (state_tests hb).1
    have hb1 := (state_tests hb).2.1
    have hb2 := (state_tests hb).2.2.1
    have hbl := (state_tests hb).2.2.2.1
    have hc0 := (state_tests hc).1
    have hc1 := (state_tests hc).2.1
    have hc2 := (state_tests hc).2.2.1
    have hcl := (state_tests hc).2.2.2.1
    -- [compile-fix R10: rewrite the three coordinates directly; propositional
    -- search over the twelve equivalences exceeded the compile budget]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
      Fin.forall_fin_zero, Fin.exists_fin_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, and_true, or_false, ha0, ha1, ha2, hal,
      hb0, hb1, hb2, hbl, hc0, hc1, hc2, hcl]
  obtain ⟨code,hcode,H⟩ := state_code_sound a b c htag
  refine ⟨code,hcode,?_⟩
  rw [carrier_tangent x hxP,he]
  exact ordinary_meridian H

end
end R44.DischargeCarrierStrata
