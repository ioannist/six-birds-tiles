/- -- [compile-fix: promoted to Proved after exchange 7]
# Continuous interpretation of the mesh incidence trace

A-L3.1/A-L2.2. The finite trace supplies only integer endpoint equalities,
coordinate intervals and strict separation witnesses. This file proves
what those data mean for EVERY point of the open mesh segment. Named edges
use the fully oriented native feature theorem. Other segments lie outside
all closed edits and have the carrier's explicit ordinary tangent germ.
No finite sample is substituted for a segment and no surface-area equality
is assumed. No mathematical admissions.
-/
import R44.Proved.MeshChartIncidence -- [compile-fix: promoted after exchange 7]
import R44.Proved.NativeBoundaryLocal -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeMeshTrace
open Set DischargeGeometry DischargeVertexData DischargeCarrierStrata
open DischargeMeridian DischargeBoundaryLocal DischargeCharts
noncomputable section
set_option maxHeartbeats 0

-- [compile-fix: the former transitive `LogicalSpine` import supplied a private
-- V3 lawfulness instance; prove the needed direction directly after removing
-- that cyclic import]
private theorem v3_eq_of_beq {a b : V3} (h : (a == b) = true) : a = b := by
  rcases a with ⟨ax, ay, az⟩
  rcases b with ⟨bx, byv, bz⟩
  unfold instBEqV3 instBEqV3.beq at h
  simp at h
  simp_all

private theorem weighted_gt (l a b s t : ℝ) (hs : 0<s) (ht : 0<t)
    (hst : s+t=1) (ha : l≤a) (hb : l≤b) (hstrict : l<a ∨ l<b) :
    l<s*a+t*b := by
  have he : s*a+t*b-l=s*(a-l)+t*(b-l) := by
    nlinarith [congrArg (fun z:ℝ => z*l) hst]
  rw [←sub_pos,he]
  rcases hstrict with h|h
  · exact add_pos_of_pos_of_nonneg (mul_pos hs (sub_pos.mpr h))
      (mul_nonneg ht.le (sub_nonneg.mpr hb))
  · exact add_pos_of_nonneg_of_pos (mul_nonneg hs.le (sub_nonneg.mpr ha))
      (mul_pos ht (sub_pos.mpr h))

private theorem weighted_lt (l a b s t : ℝ) (hs : 0<s) (ht : 0<t)
    (hst : s+t=1) (ha : a≤l) (hb : b≤l) (hstrict : a<l ∨ b<l) :
    s*a+t*b<l := by
  have h := weighted_gt (-l) (-a) (-b) s t hs ht hst
    (neg_le_neg ha) (neg_le_neg hb)
    (hstrict.imp neg_lt_neg neg_lt_neg)
  nlinarith

/-- The coordinate tag is valid on the whole OPEN segment, even when one
endpoint lies on a stratum boundary. -/
private theorem segment_state_sound (a b : Int) (s t : ℝ)
    (hs : 0<s) (ht : 0<t) (hst : s+t=1)
    (hcode : segmentCoordinateState a b<5) :
    coordinateState ⟨segmentCoordinateState a b,hcode⟩
      ((s*(a:ℝ)+t*(b:ℝ))/10000) := by
  unfold segmentCoordinateState at hcode ⊢
  split_ifs with h0 h1 h2 h3 h4
  · have h : a=0 ∧ b=0 := by simpa using h0
    simp [h.1,h.2,coordinateState]
  · have h : 0≤a ∧ 0≤b ∧ a≤10000 ∧ b≤10000 ∧
        (0<a ∨ 0<b) ∧ (a<10000 ∨ b<10000) := by
      simpa only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,and_assoc] using h1
    have ra : (0:ℝ)≤a := by exact_mod_cast h.1
    have rb : (0:ℝ)≤b := by exact_mod_cast h.2.1
    have ra' : (a:ℝ)≤10000 := by exact_mod_cast h.2.2.1
    have rb' : (b:ℝ)≤10000 := by exact_mod_cast h.2.2.2.1
    have hlo : (0:ℝ)<a ∨ (0:ℝ)<b := by exact_mod_cast h.2.2.2.2.1
    have hhi : (a:ℝ)<10000 ∨ (b:ℝ)<10000 := by exact_mod_cast h.2.2.2.2.2
    have hp := weighted_gt 0 a b s t hs ht hst ra rb hlo
    have hq := weighted_lt 10000 a b s t hs ht hst ra' rb' hhi
    change 0<(s*(a:ℝ)+t*(b:ℝ))/10000 ∧ (s*(a:ℝ)+t*(b:ℝ))/10000<1
    constructor <;> linarith
  · have h : a=10000 ∧ b=10000 := by simpa using h2
    simp only [coordinateState,h.1,h.2]
    nlinarith
  · have h : 10000≤a ∧ 10000≤b ∧ a≤20000 ∧ b≤20000 ∧
        (10000<a ∨ 10000<b) ∧ (a<20000 ∨ b<20000) := by
      simpa only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,and_assoc] using h3
    have ra : (10000:ℝ)≤a := by exact_mod_cast h.1
    have rb : (10000:ℝ)≤b := by exact_mod_cast h.2.1
    have ra' : (a:ℝ)≤20000 := by exact_mod_cast h.2.2.1
    have rb' : (b:ℝ)≤20000 := by exact_mod_cast h.2.2.2.1
    have hlo : (10000:ℝ)<a ∨ (10000:ℝ)<b := by exact_mod_cast h.2.2.2.2.1
    have hhi : (a:ℝ)<20000 ∨ (b:ℝ)<20000 := by exact_mod_cast h.2.2.2.2.2
    have hp := weighted_gt 10000 a b s t hs ht hst ra rb hlo
    have hq := weighted_lt 20000 a b s t hs ht hst ra' rb' hhi
    change 1<(s*(a:ℝ)+t*(b:ℝ))/10000 ∧ (s*(a:ℝ)+t*(b:ℝ))/10000<2
    constructor <;> linarith
  · have h : a=20000 ∧ b=20000 := by simpa using h4
    simp only [coordinateState,h.1,h.2]
    nlinarith
  · exfalso
    simp_all -- [compile-fix: reduce the original Boolean guard in the impossible state-5 branch]

private theorem point_coordinate (key : V3×V3) (x : E3)
    (s t : ℝ) (h : s • scaledV3 10000 key.1+t • scaledV3 10000 key.2=x)
    (i : Fin 3) : x i=(s*(key.1.get i:ℝ)+t*(key.2.get i:ℝ))/10000 := by
  rw [←h]
  simp [scaledV3]; ring

private theorem states_on_open_edge (key : V3×V3) (x : E3)
    (hx : x∈nativeGenericMeshEdge key) (h : ∀i:Fin 3,edgeState key i<5) :
    ∀i:Fin 3,coordinateState (edgeStateFin key i) (x i) := by
  rcases hx with ⟨s,t,hs,ht,hst,he⟩
  intro i
  have H := segment_state_sound (key.1.get i) (key.2.get i) s t hs ht hst (h i)
  have heFin : edgeStateFin key i=⟨edgeState key i,h i⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (h i)
  rw [heFin,point_coordinate key x s t he i]
  exact H

private theorem separation_on_open_edge (key : V3×V3) (r : Role) (i : Fin 3)
    (hsep : separatedCoordinate key r i=true) (x : E3)
    (hx : x∈nativeGenericMeshEdge key) : ¬featureTubeSupport r x := by
  rcases hx with ⟨s,t,hs,ht,hst,he⟩
  let a : Int := key.1.get i-1250*(nativeFeatureData r).center8.get i
  let b : Int := key.2.get i-1250*(nativeFeatureData r).center8.get i
  have hdiff : x i-featureCenter r i=(s*(a:ℝ)+t*(b:ℝ))/10000 := by
    rw [point_coordinate key x s t he i]
    simp only [a,b,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,featureCenter,scaledV3]
    have hh := congrArg (fun z:ℝ => z*((nativeFeatureData r).center8.get i:ℝ)) hst
    nlinarith
  have H : (100≤a ∧ 100≤b ∧ (100<a ∨ 100<b)) ∨
      (a≤(-100) ∧ b≤(-100) ∧ (a<(-100) ∨ b<(-100))) := by
    simpa only [separatedCoordinate,Bool.or_eq_true,Bool.and_eq_true,
      decide_eq_true_eq,and_assoc,a,b] using hsep
  intro hxT
  have hbnd := featureTubeSupport_coordinate_bound hxT i
  rw [hdiff,abs_le] at hbnd
  rcases H with H|H
  · have ha : (100:ℝ)≤a := by exact_mod_cast H.1
    have hb : (100:ℝ)≤b := by exact_mod_cast H.2.1
    have hc : (100:ℝ)<a ∨ (100:ℝ)<b := by exact_mod_cast H.2.2
    have hp := weighted_gt 100 a b s t hs ht hst ha hb hc
    norm_num [eta] at hbnd
    linarith [hbnd.2]
  · have ha : (a:ℝ)≤(-100) := by exact_mod_cast H.1
    have hb : (b:ℝ)≤(-100) := by exact_mod_cast H.2.1
    have hc : (a:ℝ)<(-100) ∨ (b:ℝ)<(-100) := by exact_mod_cast H.2.2
    have hp := weighted_lt (-100) a b s t hs ht hst ha hb hc
    norm_num [eta] at hbnd
    linarith [hbnd.1]

private theorem native_from_integer_endpoints (key : V3×V3) (r : Role)
    (k : Fin 4) (kind : FeatureEdgeKind)
    (he : endpointsEqual key (nativeCorner10000 r k)
      (match kind with | .base => nativeCorner10000 r (nextCorner k)
                       | .ridge => nativeApex10000 r)=true)
    (x : E3) (hx : x∈nativeGenericMeshEdge key) :
    x∈nativeGenericEdgesOfKind r kind := by
  -- [compile-fix: split the endpoint kind before Boolean interpretation;
  -- simplification under the dependent `match kind` changed proof indices]
  cases kind with
  | base =>
      have h : (key.1=nativeCorner10000 r k ∧
          key.2=nativeCorner10000 r (nextCorner k)) ∨
          (key.2=nativeCorner10000 r k ∧
          key.1=nativeCorner10000 r (nextCorner k)) := by
        have he' := he
        simp only [endpointsEqual,Bool.and_eq_true,Bool.or_eq_true] at he'
        exact he'.imp
          (fun h => ⟨v3_eq_of_beq h.1, v3_eq_of_beq h.2⟩)
          (fun h => ⟨v3_eq_of_beq h.2, v3_eq_of_beq h.1⟩)
          -- [compile-fix: direct V3 Boolean-equality interpretation]
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      rcases h with ⟨h1,h2⟩|⟨h1,h2⟩
      · simpa [nativeGenericMeshEdge,h1,h2,scaled_native_corner] using hx
      · simpa [nativeGenericMeshEdge,h1,h2,scaled_native_corner,
          openSegment_symm] using hx
  | ridge =>
      have h : (key.1=nativeCorner10000 r k ∧ key.2=nativeApex10000 r) ∨
          (key.2=nativeCorner10000 r k ∧ key.1=nativeApex10000 r) := by
        have he' := he
        simp only [endpointsEqual,Bool.and_eq_true,Bool.or_eq_true] at he'
        exact he'.imp
          (fun h => ⟨v3_eq_of_beq h.1, v3_eq_of_beq h.2⟩)
          (fun h => ⟨v3_eq_of_beq h.2, v3_eq_of_beq h.1⟩)
          -- [compile-fix: direct V3 Boolean-equality interpretation]
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      rcases h with ⟨h1,h2⟩|⟨h1,h2⟩
      · simpa [nativeGenericMeshEdge,h1,h2,scaled_native_corner,
          scaled_native_apex] using hx
      · simpa [nativeGenericMeshEdge,h1,h2,scaled_native_corner,
          scaled_native_apex,openSegment_symm] using hx

private theorem feature_angle_matches (r : Role) (kind : FeatureEdgeKind)
    (c : Nat×Nat×Int) (hc : c.1=(match kind with | .base=>0 | .ridge=>1))
    (hj : (profileCoefficient r).natAbs=c.2.1) :
    MeshAngleValue c (featureInteriorAngle r kind) := by
  cases kind <;> by_cases hs : 0<profileCoefficient r <;>
    simp [MeshAngleValue,featureInteriorAngle,featureSlope,hc,hj,hs]

/-- All continuous consequences of the trace, before it is applied to the
frozen mesh. This is a generic implication for arbitrary integer endpoints. -/
theorem trace_oriented_meridian (key : V3×V3) (c : Nat×Nat×Int)
    (htrace : edgeChartTrace key c=true) (x : E3)
    (hx : x∈nativeGenericMeshEdge key) :
    ∃theta:ℝ,MeshAngleValue c theta ∧
      Nonempty (AngularMeridian (tangentCone Q x) theta) := by
  by_cases hk : c.1=0 ∨ c.1=1
  · have hm : ∃r:Role,∃k:Fin 4,featureEdgeMatch key c r k=true := by
      simpa [edgeChartTrace,hk,List.any_eq_true,List.mem_finRange,
        Bool.or_eq_true,beq_iff_eq] using htrace
    obtain ⟨r,k,hrk⟩ := hm
    have hj : (profileCoefficient r).natAbs=c.2.1 := by
      have hrk' := hrk -- [compile-fix: `Bool.and_eq_true` is a proposition equality in Lean 4.31]
      unfold featureEdgeMatch at hrk'
      rw [Bool.and_eq_true] at hrk'
      have hh := hrk'.1
      exact beq_iff_eq.mp hh
    rcases hk with hk|hk
    · have he : endpointsEqual key (nativeCorner10000 r k)
          (nativeCorner10000 r (nextCorner k))=true := by
        simpa [featureEdgeMatch,hk,hj] using hrk
      have hn := native_from_integer_endpoints key r k .base he x hx
      exact ⟨featureInteriorAngle r .base,feature_angle_matches r .base c hk hj,
        native_feature_oriented_meridian r .base x hn⟩
    · have he : endpointsEqual key (nativeCorner10000 r k) (nativeApex10000 r)=true := by
        simpa [featureEdgeMatch,hk,hj] using hrk
      have hn := native_from_integer_endpoints key r k .ridge he x hx
      exact ⟨featureInteriorAngle r .ridge,feature_angle_matches r .ridge c hk hj,
        native_feature_oriented_meridian r .ridge x hn⟩
  · have H : (∀i:Fin 3,edgeState key i<5) ∧
        (∀r:Role,∃i:Fin 3,separatedCoordinate key r i=true) ∧
        ((c.1=2 ∧ edgeOrdinaryCode key=1) ∨
         (c.1=3 ∧ (edgeOrdinaryCode key=0 ∨ edgeOrdinaryCode key=2))) := by
      simpa [edgeChartTrace,hk,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,
        List.all_eq_true,List.any_eq_true,List.mem_finRange,and_assoc] using htrace
    have hout : ∀r:Role,¬featureTubeSupport r x := by
      intro r
      obtain ⟨i,hi⟩ := H.2.1 r
      exact separation_on_open_edge key r i hi x hx
    have hstates := states_on_open_edge key x hx H.1
    have htag : edgeOrdinaryCode key<3 := by rcases H.2.2 with h|h <;> omega
    obtain ⟨code,hcode,m⟩ := carrier_meridian_from_states x
      (edgeStateFin key 0) (edgeStateFin key 1) (edgeStateFin key 2)
      (hstates 0) (hstates 1) (hstates 2) htag
    have hcode' : code.val = edgeOrdinaryCode key := by
      simpa only [edgeOrdinaryCode] using hcode -- [compile-fix: expose the definitional endpoint code once]
    obtain ⟨U,hU,hxU,he⟩ := open_carrier_off_tubes x hout
    have ht : tangentCone Q x=tangentCone P x :=
      tangentCone_of_open_agreement hU hxU he
    refine ⟨((code.val+1:Nat):ℝ)*Real.pi/2,?_,?_⟩
    -- [compile-fix begin: normalize the same edge-code proposition directly]
    · rcases H.2.2 with ⟨hclass,hval⟩|⟨hclass,hval⟩
      · have hc1 : code=1 := by
          apply Fin.ext
          exact hcode'.trans hval -- [compile-fix: use the named edge-code equality]
        simp [MeshAngleValue,hclass,hc1]
      · have hc02 : code=0 ∨ code=2 := by
          rcases hval with hval|hval
          · left; apply Fin.ext; exact hcode'.trans hval -- [compile-fix: identical finite code]
          · right; apply Fin.ext; exact hcode'.trans hval -- [compile-fix: identical finite code]
        rcases hc02 with rfl|rfl <;> simp [MeshAngleValue,hclass] <;> ring
    -- [compile-fix end]
    · rw [ht]
      exact m

/-- Complete edge-to-chart interpretation of the accepted literal mesh. -/
theorem every_mesh_edge_oriented (key : V3×V3) (hk : key∈meshGeometricEdgeKeys)
    (c : Nat×Nat×Int) (hc : classifyMeshEdge key=some c)
    (x : E3) (hx : x∈nativeGenericMeshEdge key) :
    ∃theta:ℝ,MeshAngleValue c theta ∧
      Nonempty (AngularMeridian (tangentCone Q x) theta) :=
  trace_oriented_meridian key c (edge_chart_trace key hk c hc) x hx

end
end R44.DischargeMeshTrace
