/- -- [compile-fix: promoted to Proved after exchange 7]
# Exact arithmetic of a generic sector partition

Written source: proof/ALIGNMENT_PROOF.md A-L3.2. Once actual incident tiles
have been stratified into ordinary sectors or generic feature sectors, this
file excludes one or three feature sectors and any third ordinary sector.
It also proves type/magnitude/polarity recovery from complementary angles.
This file DOES NOT claim that finite polyhedral stratification follows from
angle values alone. That geometric step is isolated in GenericFeaturePartner.
No mathematical admissions and no new finite certificate computation.
-/
import R44.Proved.FeatureGraphTopology -- [compile-fix]

namespace R44.DischargeSectors
open Set R44.Generated R44.DischargeGeometry R44.DischargeFeatureGraphs
noncomputable section
set_option maxHeartbeats 0

/-- Index into the certified 24-element deviation family. -/
def deviationIndex (h : CompleteDihedralList Q) (r : Role)
    (kind : FeatureEdgeKind) : Fin 24 :=
  let j := (profileCoefficient r).natAbs-1
  have hlo : 0<(profileCoefficient r).natAbs := by
    exact Int.natAbs_pos.mpr (h.2.1 r).1
    -- API?: Int.natAbs_pos: 0 < n.natAbs ↔ n ≠ 0.
  have hhi := (h.2.1 r).2.1
  match kind with
  | .base => ⟨j,by omega⟩
  | .ridge => ⟨12+j,by omega⟩

def deviationSign (r : Role) : FeatureEdgeKind → Bool
  | .base => if 0<profileCoefficient r then true else false
  | .ridge => if 0<profileCoefficient r then false else true

/-- This identity connects native magnitudes to the certified index, rather
than assuming that equal decimal feature heights have different angles. -/
theorem feature_angle_formula (h : CompleteDihedralList Q)
    (r : Role) (kind : FeatureEdgeKind) :
    featureInteriorAngle r kind = Real.pi +
      (if deviationSign r kind then featureDeviation (deviationIndex h r kind)
       else -featureDeviation (deviationIndex h r kind)) := by
  have hlo : 0<(profileCoefficient r).natAbs :=
    Int.natAbs_pos.mpr (h.2.1 r).1
  have hhi := (h.2.1 r).2.1
  have hj : (profileCoefficient r).natAbs-1+1=(profileCoefficient r).natAbs := by omega
  have habs : |(profileCoefficient r:Real)|=((profileCoefficient r).natAbs:Real) := -- [compile-fix begin: expose natAbs arithmetic]
    calc
      |(profileCoefficient r:Real)|=((|(profileCoefficient r)|:Int):Real) := Int.cast_abs.symm
      _=((profileCoefficient r).natAbs:Real) :=
        (Nat.cast_natAbs (α := Real) (profileCoefficient r)).symm
  have hsplit : ((profileCoefficient r).natAbs:Real)=
      1+((profileCoefficient r).natAbs-1:Nat) := by
    norm_cast
    omega
  cases kind <;>
    simp [featureInteriorAngle,deviationSign,deviationIndex,featureDeviation,
      baseDeviation,ridgeDeviation,featureSlope,hj,show
      (profileCoefficient r).natAbs-1<12 by omega] <;>
    split_ifs
  all_goals try omega
  all_goals rw [habs,hsplit]
  all_goals ring
  -- [compile-fix end]

/-- Every feature angle is strictly between 3π/4 and 5π/4, and is not π. -/
theorem feature_angle_bounds (h : CompleteDihedralList Q)
    (r : Role) (kind : FeatureEdgeKind) :
    3*Real.pi/4<featureInteriorAngle r kind ∧
    featureInteriorAngle r kind<5*Real.pi/4 ∧
    featureInteriorAngle r kind≠Real.pi := by
  have hd := h.2.2.2.2 (deviationIndex h r kind)
  rw [feature_angle_formula h]
  split_ifs <;> constructor
  all_goals try linarith
  all_goals constructor <;> linarith

/-- The numerical index determines both the edge type and the magnitude. -/
theorem deviation_index_injective (h : CompleteDihedralList Q)
    (r s : Role) (k l : FeatureEdgeKind)
    (he : deviationIndex h r k=deviationIndex h s l) :
    k=l ∧ (profileCoefficient r).natAbs=(profileCoefficient s).natAbs := by
  have hr0 : 0<(profileCoefficient r).natAbs :=
    Int.natAbs_pos.mpr (h.2.1 r).1
  have hs0 : 0<(profileCoefficient s).natAbs :=
    Int.natAbs_pos.mpr (h.2.1 s).1
  have hr := (h.2.1 r).2.1
  have hs := (h.2.1 s).2.1
  have hh := congrArg Fin.val he
  cases k <;> cases l <;>
    simp only [deviationIndex] at hh <;> constructor <;> (first | rfl | omega)

/-- Complementary feature angles force the same type and opposite signed
height, using the finite distinctness theorem only through the given list. -/
theorem complementary_feature_angles (h : CompleteDihedralList Q)
    (r s : Role) (k l : FeatureEdgeKind)
    (he : featureInteriorAngle r k+featureInteriorAngle s l=2*Real.pi) :
    k=l ∧ profileCoefficient r = -profileCoefficient s := by
  have hr := h.2.2.2.2 (deviationIndex h r k)
  have hs := h.2.2.2.2 (deviationIndex h s l)
  rw [feature_angle_formula h,feature_angle_formula h] at he
  have hsign : deviationSign r k≠deviationSign s l := by
    intro hh
    rw [hh] at he
    cases heq : deviationSign s l <;> simp [heq] at he <;> linarith
  have hdev : featureDeviation (deviationIndex h r k)=
      featureDeviation (deviationIndex h s l) := by
    cases hrsg : deviationSign r k <;> cases hssg : deviationSign s l <;>
      simp [hrsg,hssg] at hsign he <;> linarith
  obtain ⟨hkind,habs⟩ := deviation_index_injective h r s k l (h.2.2.2.1 hdev)
  refine ⟨hkind,?_⟩
  subst l
  have hrnz := (h.2.1 r).1
  have hsnz := (h.2.1 s).1
  have habs' : profileCoefficient r=profileCoefficient s ∨
      profileCoefficient r = -profileCoefficient s := by
    exact Int.natAbs_eq_natAbs_iff.mp habs
    -- API?: expected Int.natAbs_eq_natAbs_iff: |a|_N=|b|_N ↔ a=b ∨ a=-b.
  rcases habs' with heq | heq
  · exfalso
    apply hsign
    cases k <;> simp [deviationSign,heq]
  · exact heq

inductive SectorLabel where
  | ordinary (code : Fin 3)
  | feature (kind : FeatureEdgeKind) (role : Role)
  deriving DecidableEq

def SectorLabel.angle : SectorLabel → ℝ
  | .ordinary k => ((k.val+1:ℕ):ℝ)*Real.pi/2
  | .feature k r => featureInteriorAngle r k

def SectorLabel.isFeature : SectorLabel → Prop
  | .ordinary _ => False
  | .feature _ _ => True

/-- Data from the generic polyhedral cross-section. In particular the sum
is a sum of actual real dihedral angles, not of a newly defined angle proxy. -/
structure SectorPacket (T : Tiling Q) (g : RigidMotion) (r : Role)
    (kind : FeatureEdgeKind) (x : E3) where
  incident : Finset RigidMotion
  incident_iff : ∀h,h∈incident ↔ h∈T.placements ∧ x∈h '' Q
  label : RigidMotion → SectorLabel
  feature_location : ∀h∈incident,∀k s,label h=.feature k s →
    x∈genericEdgesOfKindAt h s k
  root_mem : g∈incident
  root_label : label g=.feature kind r
  angle_sum : ∑h∈incident,(label h).angle=2*Real.pi

/-- Arithmetic consequence of the packet: exactly two incident tiles, both
feature sectors. The proof does not enumerate geometric configurations. -/
local instance : DecidableEq RigidMotion := Classical.decEq _ -- [compile-fix]
theorem packet_two_features (hlist : CompleteDihedralList Q)
    {T : Tiling Q} {g : RigidMotion} {r : Role} {kind : FeatureEdgeKind} {x : E3}
    (p : SectorPacket T g r kind x) :
    ∃h∈p.incident,h≠g ∧ (p.label h).isFeature ∧ p.incident={g,h} := by
  classical
  let F := p.incident.filter (fun h => (p.label h).isFeature)
  let O := p.incident\F
  have hgF : g∈F := by simp [F,p.root_mem,p.root_label,SectorLabel.isFeature]
  have hFne : F.Nonempty := ⟨g,hgF⟩
  have hpart : F∪O=p.incident := by
    ext h; simp [F,O]; tauto
  have hdisj : Disjoint F O := Finset.disjoint_sdiff -- [compile-fix]
    -- API?: disjointness of a finset and its right-hand set difference.
  have hsum : (∑h∈F,(p.label h).angle)+(∑h∈O,(p.label h).angle)=2*Real.pi := by
    rw [← Finset.sum_union hdisj,hpart,p.angle_sum]
  have hfeature : ∀h∈F,3*Real.pi/4<(p.label h).angle := by
    intro h hh
    have ht := (Finset.mem_filter.mp hh).2
    cases heq : p.label h with
    | ordinary k => simp [heq,SectorLabel.isFeature] at ht
    | feature k s => simpa [heq,SectorLabel.angle] using (feature_angle_bounds hlist s k).1
  have hord : ∀h∈O,∃k:Fin 3,p.label h=.ordinary k := by
    intro h hh
    have hi := (Finset.mem_sdiff.mp hh).1
    have hn := (Finset.mem_sdiff.mp hh).2
    cases heq : p.label h with
    | ordinary k => exact ⟨k,rfl⟩ -- [compile-fix]
    | feature k s => exact False.elim (hn (by simp [F,hi,heq,SectorLabel.isFeature]))
  have hloO : ∀h∈O,Real.pi/2≤(p.label h).angle := by
    intro h hh
    obtain ⟨k,hk⟩ := hord h hh
    rw [hk,SectorLabel.angle]
    have hk0 : (1:ℝ)≤((k.val+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    nlinarith [Real.pi_pos]
  have hsF : (F.card:ℝ)*(3*Real.pi/4)<∑h∈F,(p.label h).angle := by
    simpa using Finset.sum_lt_sum_of_nonempty hFne hfeature
    -- API?: strict finite-sum comparison when every summand is strict and F is nonempty.
  have hsO : (O.card:ℝ)*(Real.pi/2)≤∑h∈O,(p.label h).angle := by
    simpa using Finset.sum_le_sum hloO
  have hcF : F.card≤2 := by
    by_contra hn
    have hc : (3:ℝ)≤F.card := by exact_mod_cast (show 3≤F.card by omega)
    have ho : 0≤(O.card:ℝ) := Nat.cast_nonneg _
    nlinarith [Real.pi_pos]
  have hcFpos : 0<F.card := Finset.card_pos.mpr hFne
  have hcFne1 : F.card≠1 := by
    intro h1
    have hFg : F={g} := by
      obtain ⟨q,hq⟩ := Finset.card_eq_one.mp h1
      have hqg : g=q := by simpa [hq] using hgF
      simpa [hqg] using hq
    let n : RigidMotion → ℕ := fun h => match p.label h with
      | .ordinary k => k.val+1
      | .feature _ _ => 0
    let N := ∑h∈O,n h
    have hoSum : ∑h∈O,(p.label h).angle=(N:ℝ)*Real.pi/2 := by
      dsimp [N]
      rw [Nat.cast_sum,Finset.sum_mul,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro h hh
      obtain ⟨k,hk⟩ := hord h hh
      simp [n,hk,SectorLabel.angle]
    rw [hFg,Finset.sum_singleton,p.root_label,SectorLabel.angle,hoSum] at hsum
    have hb := feature_angle_bounds hlist r kind
    have hnlo : (1:ℝ)<N := by nlinarith [Real.pi_pos]
    have hnhi : (N:ℝ)<3 := by nlinarith [Real.pi_pos]
    have hn : N=2 := by
      have := (show 1<N by exact_mod_cast hnlo)
      have := (show N<3 by exact_mod_cast hnhi)
      omega
    rw [hn] at hsum
    norm_num at hsum
    exact hb.2.2 (by linarith)
  have hcF2 : F.card=2 := by omega
  have hO : O=∅ := by
    by_contra hn
    have hnpos : 1≤O.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn)
    have hnreal : (1:ℝ)≤O.card := by exact_mod_cast hnpos
    rw [hcF2] at hsF
    norm_num at hsF
    nlinarith [Real.pi_pos]
  have hI : F=p.incident := by simpa [hO] using hpart
  have hIc : p.incident.card=2 := by simpa [hI] using hcF2
  have herase : (p.incident.erase g).card=1 := by
    rw [Finset.card_erase_of_mem p.root_mem,hIc]
  obtain ⟨h,hh⟩ := Finset.card_eq_one.mp herase
  have hm : h∈p.incident.erase g := by simp [hh]
  have hne := (Finset.mem_erase.mp hm).1
  have hi := (Finset.mem_erase.mp hm).2
  refine ⟨h,hi,hne,?_,?_⟩
  · have hiF : h∈F := by rw [hI]; exact hi -- [compile-fix begin: orient the finset transport]
    exact (Finset.mem_filter.mp hiF).2
    -- [compile-fix end]
  · calc
      p.incident=insert g (p.incident.erase g) := (Finset.insert_erase p.root_mem).symm
      _ = {g,h} := by rw [hh]

end
end R44.DischargeSectors
