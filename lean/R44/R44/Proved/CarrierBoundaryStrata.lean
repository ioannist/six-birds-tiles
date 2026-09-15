/- -- [compile-fix: promoted to Proved after exchange 7]
# Continuous carrier strata outside its coordinate-grid vertices

A-L2.2/A-L3.1. This is an analytic classification of P itself, using
P = [0,2]^3 intersect {x0<=1 or x1<=1 or x2<=1}. The finite five-state
case distinction is generic order algebra, not a new mesh certificate.
Every surviving boundary germ is a halfspace, an orthogonal quadrant,
or the union of two orthogonal halfspaces. All actual radial tangent-set
identities are proved from open-neighborhood germs. No admissions.
-/
import R44.Proved.OrdinaryMeridians -- [compile-fix: promoted after exchange 7]
import R44.Proved.CarrierSymmetries -- [compile-fix: accepted helper was promoted]

namespace R44.DischargeCarrierStrata
open Set Filter DischargeGeometry DischargePolyhedral DischargeOrdinary
open DischargeMeridian
open scoped Topology
noncomputable section
set_option maxHeartbeats 0

private theorem coordinate_upper_germ (x : E3) (i : Fin 3) (c : ℝ) :
    ∀ᶠd in 𝓝 (0:E3), x i+d i≤c ↔ x i<c ∨ (x i=c ∧ d i≤0) := by
  rcases lt_trichotomy (x i) c with h|h|h
  · have hn : ∀ᶠd in 𝓝 (0:E3),x i+d i<c :=
      (show ContinuousAt (fun d:E3 => x i+d i) 0 by fun_prop).eventually
        (gt_mem_nhds (by simpa using h))
    filter_upwards [hn] with d hd
    exact iff_of_true hd.le (Or.inl h)
  · exact Filter.Eventually.of_forall fun d => by simp [h]
  · have hn : ∀ᶠd in 𝓝 (0:E3),c<x i+d i :=
      (show ContinuousAt (fun d:E3 => x i+d i) 0 by fun_prop).eventually
        (lt_mem_nhds (by simpa using h))
    filter_upwards [hn] with d hd
    simp [not_le_of_gt hd,not_lt_of_ge h.le,ne_of_gt h]

private theorem coordinate_lower_germ (x : E3) (i : Fin 3) (c : ℝ) :
    ∀ᶠd in 𝓝 (0:E3), c≤x i+d i ↔ c<x i ∨ (x i=c ∧ 0≤d i) := by
  rcases lt_trichotomy c (x i) with h|h|h
  · have hn : ∀ᶠd in 𝓝 (0:E3),c<x i+d i :=
      (show ContinuousAt (fun d:E3 => x i+d i) 0 by fun_prop).eventually
        (lt_mem_nhds (by simpa using h))
    filter_upwards [hn] with d hd
    exact iff_of_true hd.le (Or.inl h)
  · exact Filter.Eventually.of_forall fun d => by simp [←h]
  · have hn : ∀ᶠd in 𝓝 (0:E3),x i+d i<c :=
      (show ContinuousAt (fun d:E3 => x i+d i) 0 by fun_prop).eventually
        (gt_mem_nhds (by simpa using h))
    filter_upwards [hn] with d hd
    simp [not_le_of_gt hd,not_lt_of_ge h.le,ne_of_lt h]

def carrierCone (x : E3) : Set E3 := {d |
  (∀i:Fin 3,(x i=0 → 0≤d i) ∧ (x i=2 → d i≤0)) ∧
  ((∃i:Fin 3,x i<1) ∨ ∃i:Fin 3,x i=1 ∧ d i≤0)}

theorem carrier_germ (x : E3) (hx : x∈P) :
    ∀ᶠd in 𝓝 (0:E3),x+d∈P ↔ d∈carrierCone x := by
  have hb := (mem_P_iff_box_notch x).mp hx
  have h0 : ∀ᶠd in 𝓝 (0:E3),∀i:Fin 3,
      0≤x i+d i ↔ 0<x i ∨ (x i=0 ∧ 0≤d i) :=
    Filter.eventually_all.mpr (fun i => coordinate_lower_germ x i 0)
  have h1 : ∀ᶠd in 𝓝 (0:E3),∀i:Fin 3,
      x i+d i≤1 ↔ x i<1 ∨ (x i=1 ∧ d i≤0) :=
    Filter.eventually_all.mpr (fun i => coordinate_upper_germ x i 1)
  have h2 : ∀ᶠd in 𝓝 (0:E3),∀i:Fin 3,
      x i+d i≤2 ↔ x i<2 ∨ (x i=2 ∧ d i≤0) :=
    Filter.eventually_all.mpr (fun i => coordinate_upper_germ x i 2)
  filter_upwards [h0,h1,h2] with d hd0 hd1 hd2
  rw [mem_P_iff_box_notch]
  change ((∀i,0≤x i+d i ∧ x i+d i≤2) ∧ ∃i,x i+d i≤1) ↔ _
  simp_rw [hd0,hd1,hd2]
  have hbounds :
      (∀i:Fin 3,(0<x i ∨ (x i=0 ∧ 0≤d i)) ∧
        (x i<2 ∨ (x i=2 ∧ d i≤0))) ↔
      ∀i:Fin 3,(x i=0 → 0≤d i) ∧ (x i=2 → d i≤0) := by
    apply forall_congr'; intro i
    rcases (hb.1 i) with ⟨hl,hu⟩
    -- [compile-fix: separate equality branches before using disequalities]
    by_cases hz : x i=0
    · have ht : x i ≠ 2 := by linarith
      have hlt : x i < 2 := by linarith
      simp [hz, ht, hlt]
    · have hgt : 0 < x i := lt_of_le_of_ne hl (Ne.symm hz)
      by_cases ht : x i=2
      · simp [hz, ht, hgt]
      · have hlt : x i < 2 := lt_of_le_of_ne hu ht
        simp [hz, ht, hgt, hlt]
  rw [hbounds]
  simp only [carrierCone,Set.mem_setOf_eq,exists_or]

theorem carrier_tangent (x : E3) (hx : x∈P) : tangentCone P x=carrierCone x := by
  apply LocalCone.tangent_eq
  · intro a ha d
    change ((∀i,(x i=0 → 0≤a*d i) ∧ (x i=2 → a*d i≤0)) ∧
      ((∃i,x i<1) ∨ ∃i,x i=1 ∧ a*d i≤0)) ↔ _
    -- [compile-fix: current order API exposes the sign-disjunction lemmas]
    simp [carrierCone,mul_nonneg_iff,mul_nonpos_iff,ha.le,not_le_of_gt ha]
  · exact carrier_germ x hx

/-- Only an actual boundary point is classified; a full-space local cone
would instead make the point interior. -/
theorem carrier_cone_ne_univ (x : E3) (hx : x∈frontier P) : carrierCone x≠univ := by
  intro he
  have hxP : x∈P := by simpa [P_compact.isClosed.closure_eq] using hx.1
  have hn := carrier_germ x hxP
  simp only [he,Set.mem_univ,iff_true] at hn
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hn
  apply hx.2
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x hd)
  intro y hy
  have hm : y-x∈Metric.ball (0:E3) d := by
    simpa [Metric.mem_ball,dist_eq_norm] using hy
  simpa using hball hm

private def inState (s : Fin 5) (x : ℝ) : Prop :=
  match s.val with
  | 0 => x=0
  | 1 => 0<x ∧ x<1
  | 2 => x=1
  | 3 => 1<x ∧ x<2
  | _ => x=2

private theorem state_exists {x : ℝ} (hx : 0≤x ∧ x≤2) : ∃s:Fin 5,inState s x := by
  rcases lt_trichotomy x 1 with h|h|h
  · rcases eq_or_lt_of_le hx.1 with hz|hz
    · exact ⟨0,hz.symm⟩
    · exact ⟨1,hz,h⟩
  · exact ⟨2,h⟩
  · rcases eq_or_lt_of_le hx.2 with hz|hz
    · exact ⟨4,hz⟩
    · exact ⟨3,h,hz⟩

private structure StateFacts (s : Fin 5) (x : ℝ) : Prop where
  zero : (x=0 ↔ s=0)
  one : (x=1 ↔ s=2)
  two : (x=2 ↔ s=4)
  low : (x<1 ↔ s.val<2)
  atMostOne : (x≤1 ↔ s.val≤2)

private theorem state_facts {s : Fin 5} {x : ℝ} (h : inState s x) : StateFacts s x := by
  fin_cases s <;> simp only [inState] at h
  -- [compile-fix: construct all five structure fields before normalization]
  all_goals constructor <;> simp_all <;> linarith

private def stateCone (s : Fin 3 → Fin 5) : Set E3 := {d |
  (∀i:Fin 3,(s i=0 → 0≤d i) ∧ (s i=4 → d i≤0)) ∧
  ((∃i:Fin 3,(s i).val<2) ∨ ∃i:Fin 3,s i=2 ∧ d i≤0)}

-- [compile-fix begin: current finite-case elaboration for the delivered proposition]
private theorem state_cone_cases (a b c : Fin 5)
    (hnotch : a.val≤2 ∨ b.val≤2 ∨ c.val≤2)
    (hnotvertex : a=1 ∨ a=3 ∨ b=1 ∨ b=3 ∨ c=1 ∨ c=3) :
    stateCone ![a,b,c]=univ ∨ ∃code:Fin 3,OrdinaryCone (stateCone ![a,b,c]) code := by
  have hnv : a.val=1 ∨ a.val=3 ∨ b.val=1 ∨ b.val=3 ∨
      c.val=1 ∨ c.val=3 := by
    simpa [Fin.ext_iff] using hnotvertex
  fin_cases a <;> fin_cases b <;> fin_cases c
  -- [compile-fix: use value equalities to eliminate inconsistent finite cases]
  all_goals simp only at hnotch hnv
  all_goals try { exfalso; omega }
  all_goals solve -- [compile-fix: require each finite-case method to close its goal]
  | apply Or.inl
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ]
  | refine Or.inr ⟨1, ?_⟩
    convert OrdinaryCone.half (0:Fin 3) (1:ℝ) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨1, ?_⟩
    convert OrdinaryCone.half (0:Fin 3) (-1:ℝ) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨1, ?_⟩
    convert OrdinaryCone.half (1:Fin 3) (1:ℝ) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨1, ?_⟩
    convert OrdinaryCone.half (1:Fin 3) (-1:ℝ) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨1, ?_⟩
    convert OrdinaryCone.half (2:Fin 3) (1:ℝ) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨1, ?_⟩
    convert OrdinaryCone.half (2:Fin 3) (-1:ℝ) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (0:Fin 3) (1:Fin 3) (by omega)
        (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (0:Fin 3) (1:Fin 3) (by omega)
        (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (0:Fin 3) (1:Fin 3) (by omega)
        (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (0:Fin 3) (1:Fin 3) (by omega)
        (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (0:Fin 3) (2:Fin 3) (by omega)
        (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (0:Fin 3) (2:Fin 3) (by omega)
        (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (0:Fin 3) (2:Fin 3) (by omega)
        (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (0:Fin 3) (2:Fin 3) (by omega)
        (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (1:Fin 3) (2:Fin 3) (by omega)
        (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (1:Fin 3) (2:Fin 3) (by omega)
        (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (1:Fin 3) (2:Fin 3) (by omega)
        (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨0, ?_⟩
    convert OrdinaryCone.right (1:Fin 3) (2:Fin 3) (by omega)
        (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (0:Fin 3) (1:Fin 3) (by omega)
        (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (0:Fin 3) (1:Fin 3) (by omega)
        (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (0:Fin 3) (1:Fin 3) (by omega)
        (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (0:Fin 3) (1:Fin 3) (by omega)
        (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (0:Fin 3) (2:Fin 3) (by omega)
        (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (0:Fin 3) (2:Fin 3) (by omega)
        (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (0:Fin 3) (2:Fin 3) (by omega)
        (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (0:Fin 3) (2:Fin 3) (by omega)
        (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (1:Fin 3) (2:Fin 3) (by omega)
        (1:ℝ) (1:ℝ) (Or.inl rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (1:Fin 3) (2:Fin 3) (by omega)
        (1:ℝ) (-1:ℝ) (Or.inl rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (1:Fin 3) (2:Fin 3) (by omega)
        (-1:ℝ) (1:ℝ) (Or.inr rfl) (Or.inl rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
  | refine Or.inr ⟨2, ?_⟩
    convert OrdinaryCone.reentrant (1:Fin 3) (2:Fin 3) (by omega)
        (-1:ℝ) (-1:ℝ) (Or.inr rfl) (Or.inr rfl) using 1
    ext d
    simp [stateCone,Fin.forall_fin_succ,Fin.exists_fin_succ,neg_nonpos]
    <;> tauto <;> done
-- [compile-fix end]

/-- Continuous classification of every nonvertex point of frontier P. -/
theorem carrier_boundary_meridian (x : E3) (hx : x∈frontier P)
    (hv : ¬∀i:Fin 3,x i=0 ∨ x i=1 ∨ x i=2) :
    ∃code:Fin 3,Nonempty (AngularMeridian (tangentCone P x)
      (((code.val+1:Nat):ℝ)*Real.pi/2)) := by
  have hxP : x∈P := by simpa [P_compact.isClosed.closure_eq] using hx.1
  have hb := (mem_P_iff_box_notch x).mp hxP
  choose s hs using fun i : Fin 3 => state_exists (hb.1 i)
  have hc : carrierCone x=stateCone s := by
    ext d
    simp only [carrierCone,stateCone,Set.mem_setOf_eq]
    simp_rw [(state_facts (hs _)).zero,(state_facts (hs _)).two,
      (state_facts (hs _)).one,(state_facts (hs _)).low]
  have hnotch : (s 0).val≤2 ∨ (s 1).val≤2 ∨ (s 2).val≤2 := by
    obtain ⟨i,hi⟩ := hb.2
    have hh := (state_facts (hs i)).atMostOne.mp hi
    fin_cases i <;> tauto
  have hnotvertex : s 0=1 ∨ s 0=3 ∨ s 1=1 ∨ s 1=3 ∨ s 2=1 ∨ s 2=3 := by
    by_contra hn
    push_neg at hn
    apply hv
    intro i
    have hsi := hs i
    have hi1 : s i≠1 := by fin_cases i <;> tauto
    have hi3 : s i≠3 := by fin_cases i <;> tauto
    generalize he : s i = q at hsi hi1 hi3
    fin_cases q <;> simp_all [inState]
  have hsfun : s=![s 0,s 1,s 2] := by funext i; fin_cases i <;> rfl
  have ht := state_cone_cases (s 0) (s 1) (s 2) hnotch hnotvertex
  rw [←hsfun,←hc] at ht
  rcases ht with hu|⟨code,hcode⟩
  · exact False.elim (carrier_cone_ne_univ x hx hu)
  · refine ⟨code,?_⟩
    rw [carrier_tangent x hxP]
    exact ordinary_meridian hcode

end
end R44.DischargeCarrierStrata
