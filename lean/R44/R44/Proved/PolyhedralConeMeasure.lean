/- -- [compile-fix: promoted to Proved after exchange 7]
# Null cone boundaries and the actual solid-angle sum

Sources: A-L2.2 and A-L3.2 of proof/ALIGNMENT_PROOF.md. This supplies the
measure-theoretic passage from the frozen ConeSectorBudgets to an exact
real angle sum. It does NOT infer local edge strata from angle values.

A finite Boolean affine set has a null frontier. The proof first evaluates
an affine hyperplane by one-dimensional singleton slices (Tonelli), then
uses the finite Boolean construction. The locally homogeneous model is
proved polyhedral as well; this connects the calculation to the frozen
radial tangentCone rather than a replacement notion of tangent cone.

No admissions. No mesh, generic-stratification or other residual hypothesis
is imported. API-sensitive measure identities are marked inline.
-/
import R44.Proved.PolyhedralGerms -- [compile-fix]
import R44.Proved.ConeSectorBudgets -- [compile-fix]
import R44.Proved.SectorArithmetic -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeConeMeasure
open Set Filter MeasureTheory R44.DischargePolyhedral R44.DischargeSectors
open scoped Topology ENNReal
noncomputable section
set_option maxHeartbeats 0

private abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- Split the selected coordinate off as the LAST real factor. -/
private def splitAxis (i : Fin 3) : E3 ≃ᵐ (E2 × ℝ) :=
  (((((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))).trans
    MeasurableEquiv.prodComm) -- [compile-fix]
    -- API?: prodComm is the measurable equivalence (x,y) ↦ (y,x).

private theorem splitAxis_preserves (i : Fin 3) :
    MeasurePreserving (splitAxis i) volume volume := by
  have h3 : MeasurePreserving
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm (volume : Measure E3) volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)
  have h2back : MeasurePreserving
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm (volume : Measure E2) volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)
  have h2 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) volume volume := by
    simpa using MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm h2back
  have hp := (MeasurePreserving.id (volume : Measure ℝ)).prod h2
  have hc := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  have hs : MeasurePreserving (MeasurableEquiv.prodComm : (ℝ × E2) ≃ᵐ (E2 × ℝ)) -- [compile-fix]
      ((volume : Measure ℝ).prod volume) ((volume : Measure E2).prod volume) :=
    Measure.measurePreserving_swap
    -- API?: product Lebesgue measures are exchanged by Prod.swap; expected
    -- measurePreserving_swap / Measure.measurePreserving_swap.
  change MeasurePreserving (splitAxis i) volume ((volume : Measure E2).prod volume)
  apply (hs.comp (hp.comp (hc.comp h3))).congr (splitAxis i).measurable
  exact Filter.Eventually.of_forall fun _ => rfl

private def basisVector (i : Fin 3) : E3 :=
  WithLp.toLp 2 fun j : Fin 3 => if j=i then 1 else 0

private theorem splitAxis_line (i : Fin 3) (u : E2) (t : ℝ) :
    (splitAxis i).symm (u,t)=t • basisVector i+(splitAxis i).symm (u,0) := by
  ext k -- [compile-fix begin: reason by the distinguished coordinate and succAbove complement]
  by_cases h : k=i
  · subst k
    simp [splitAxis,basisVector,MeasurableEquiv.piFinSuccAbove,
      MeasurableEquiv.prodComm,Prod.swap,MeasurableEquiv.prodCongr,
      Equiv.prodCongr_apply,Equiv.prodCongr_symm,MeasurableEquiv.refl,
      MeasurableEquiv.toLp,WithLp.equiv,Fin.insertNth_apply_same]
  · obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq h
    subst k
    simp [splitAxis,basisVector,MeasurableEquiv.piFinSuccAbove,
      MeasurableEquiv.prodComm,Prod.swap,MeasurableEquiv.prodCongr,
      Equiv.prodCongr_apply,Equiv.prodCongr_symm,MeasurableEquiv.refl,
      MeasurableEquiv.toLp,WithLp.equiv,Fin.insertNth_apply_succAbove] -- [compile-fix end]
    -- API?: unfolding piFinSuccAbove inserts the separated coordinate at i;
    -- all source and target indices here are explicit finite indices.

private theorem affine_split_line (f : ScalarAffine) (i : Fin 3) (u : E2) (t : ℝ) :
    f ((splitAxis i).symm (u,t))=
      t*f.linear (basisVector i)+f ((splitAxis i).symm (u,0)) := by
  rw [splitAxis_line]
  change f.linear (t • basisVector i+(splitAxis i).symm (u,0))+f.offset=_
  rw [map_add,map_smul]
  simp only [smul_eq_mul]
  ring

private theorem some_nonzero_coefficient (f : ScalarAffine) (hf:f.linear≠0) :
    ∃i : Fin 3,f.linear (basisVector i)≠0 := by
  by_contra hn
  push_neg at hn
  apply hf
  ext x
  have hd : x=x 0 • basisVector 0+x 1 • basisVector 1+x 2 • basisVector 2 := by
    ext k; fin_cases k <;> simp [basisVector]
  conv_lhs => rw [hd]
  simp [map_add,map_smul,hn]

/-- Affine hyperplanes have zero ambient volume, proved by actual sections. -/
theorem affine_zero_volume (f : ScalarAffine) (hf:f.linear≠0) :
    volume {x:E3 | f x=0}=0 := by
  obtain ⟨i,hi⟩ := some_nonzero_coefficient f hf
  let S : Set (E2 × ℝ) := {p | f ((splitAxis i).symm p)=0}
  have hS : MeasurableSet S := -- [compile-fix]
    (measurableSet_singleton (0:ℝ)).preimage -- [compile-fix]
      (f.continuous.measurable.comp (splitAxis i).symm.measurable) -- [compile-fix]
  have he : {x:E3 | f x=0}=(splitAxis i) ⁻¹' S := by
    ext x; simp [S]
  rw [he,(splitAxis_preserves i).measure_preimage hS.nullMeasurableSet,
    Measure.volume_eq_prod,Measure.prod_apply hS]
  have hsection (u:E2) : {t:ℝ | (u,t)∈S}=
      { -f ((splitAxis i).symm (u,0))/f.linear (basisVector i)} := by
    ext t
    change f ((splitAxis i).symm (u,t))=0 ↔ -- [compile-fix begin: avoid recursive simp on affine_split_line]
      t = -f ((splitAxis i).symm (u,0))/f.linear (basisVector i)
    rw [affine_split_line] -- [compile-fix end]
    constructor
    · intro h
      apply (eq_div_iff hi).mpr
      linarith
    · intro h
      rw [h]
      field_simp [hi]
      ring
  -- [compile-fix begin: rewrite every Tonelli fiber to a null singleton]
  have hfiber (u:E2) : volume (Prod.mk u ⁻¹' S)=0 := by
    rw [show Prod.mk u ⁻¹' S = {t:ℝ | (u,t)∈S} by rfl,hsection,measure_singleton]
  simp_rw [hfiber]
  exact lintegral_zero -- [compile-fix]
  -- [compile-fix end]

private theorem halfspace_frontier_null (f : ScalarAffine) :
    volume (frontier {x:E3 | f x≤0})=0 := by
  by_cases hz : f.linear=0
  · have he : {x:E3 | f x≤0}=if f.offset≤0 then Set.univ else ∅ := by
      ext x; simp [hz] -- [compile-fix]
    rw [he]; split_ifs <;> simp
  · have hc : IsClosed {x:E3 | f x≤0} := isClosed_le f.continuous continuous_const
    have hsub : frontier {x:E3 | f x≤0}⊆{x:E3 | f x=0} := by
      intro x hx
      have hle : f x≤0 := hc.closure_subset hx.1 -- [compile-fix]
      by_contra hn
      have hlt : f x<0 := lt_of_le_of_ne hle hn
      have ho : IsOpen {y:E3 | f y<0} := isOpen_lt f.continuous continuous_const
      have hstrict : {y:E3 | f y<0} ⊆ {y:E3 | f y≤0} := -- [compile-fix begin: type the strict-halfspace inclusion]
        fun y hy => by
          change f y < 0 at hy
          change f y ≤ 0
          exact hy.le
      have hint : x∈interior {y:E3 | f y≤0} :=
        (interior_maximal hstrict ho) hlt -- [compile-fix end]
      exact hx.2 hint
    exact le_antisymm ((measure_mono hsub).trans_eq (affine_zero_volume f hz)) bot_le -- [compile-fix]

private theorem null_union {S T : Set E3} (hS:volume S=0) (hT:volume T=0) :
    volume (S∪T)=0 := by
  apply le_antisymm _ bot_le -- [compile-fix]
  calc
    volume (S∪T)≤volume S+volume T := measure_union_le _ _
    _=0 := by rw [hS,hT]; simp

/-- The Boolean chart language is measurable and has a null frontier. -/
theorem polyhedral_measure {S:Set E3} (hS:PolyhedralPredicate S) :
    MeasurableSet S ∧ volume (frontier S)=0 := by
  induction hS with
  | halfspace f =>
      exact ⟨(isClosed_le f.continuous continuous_const).measurableSet,
        halfspace_frontier_null f⟩
  | compl hs ih =>
      exact ⟨ih.1.compl,by simpa only [frontier_compl] using ih.2⟩
  | inter hs ht ihs iht =>
      refine ⟨ihs.1.inter iht.1,?_⟩
      apply le_antisymm ?_ bot_le -- [compile-fix begin: weaken Mathlib's closure-sensitive frontier bound]
      apply (measure_mono ?_).trans_eq (null_union ihs.2 iht.2)
      intro x hx
      exact (frontier_inter_subset _ _ hx).elim
        (fun h => Or.inl h.1) (fun h => Or.inr h.2) -- [compile-fix end]
      -- API?: frontier_inter_subset : frontier (S∩T)⊆frontier S∪frontier T.
  | union hs ht ihs iht =>
      refine ⟨ihs.1.union iht.1,?_⟩
      apply le_antisymm ?_ bot_le -- [compile-fix begin: weaken Mathlib's closure-sensitive frontier bound]
      apply (measure_mono ?_).trans_eq (null_union ihs.2 iht.2)
      intro x hx
      exact (frontier_union_subset _ _ hx).elim
        (fun h => Or.inl h.1) (fun h => Or.inr h.2) -- [compile-fix end]
      -- API?: corresponding frontier_union_subset.
  | @iUnion ι _ S hs ih =>
      classical
      letI : Fintype ι := Fintype.ofFinite ι
      have hfinite : ∀s:Finset ι,volume (frontier (⋃i∈s,S i))=0 := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi hind =>
            simp only [Finset.set_biUnion_insert]
            apply le_antisymm ?_ bot_le -- [compile-fix begin: finite-union form of the same weakening]
            apply (measure_mono ?_).trans_eq (null_union (ih i).2 hind)
            intro x hx
            exact (frontier_union_subset _ _ hx).elim
              (fun h => Or.inl h.1) (fun h => Or.inr h.2) -- [compile-fix end]
            -- API?: set_biUnion_insert rewrites the bounded finite union.
      exact ⟨MeasurableSet.iUnion (fun i => (ih i).1),by simpa using hfinite Finset.univ⟩

/-- Strengthening of the local-germ induction: the homogeneous model itself
is still a finite Boolean affine set. -/
theorem local_polyhedral_cone {S:Set E3} (hS:PolyhedralPredicate S) (x:E3) :
    ∃C:Set E3,PolyhedralPredicate C ∧
      (∀a:ℝ,0<a → ∀v:E3,a • v∈C ↔ v∈C) ∧
      (∀ᶠv in 𝓝 (0:E3),x+v∈S ↔ v∈C) := by
  induction hS with
  | halfspace f =>
      rcases lt_trichotomy (f x) 0 with hn|he|hp
      · refine ⟨univ,PolyhedralPredicate.univ,by simp,?_⟩
        have h : ContinuousAt (fun v:E3 => f (x+v)) 0 := -- [compile-fix]
          (f.continuous.comp (continuous_const.add continuous_id)).continuousAt -- [compile-fix]
        have hn' : ∀ᶠv in 𝓝 (0:E3),f (x+v)<0 :=
          h.eventually (gt_mem_nhds (by simpa using hn))
        filter_upwards [hn'] with v hv
        exact iff_of_true hv.le trivial
      · let a : ScalarAffine := ⟨f.linear,0⟩
        refine ⟨{v | f.linear v≤0},?_,?_,?_⟩
        · simpa [a] using PolyhedralPredicate.halfspace a
        · intro t ht v
          change f.linear (t • v)≤0 ↔ f.linear v≤0 -- [compile-fix begin: expose linear-map homogeneity]
          rw [map_smul]
          simp only [smul_eq_mul] -- [compile-fix end]
          constructor -- [compile-fix begin: prove the positive-scalar equivalence directly]
          · intro hmul
            by_contra hn
            have hv : 0 < f.linear v := lt_of_not_ge hn
            nlinarith
          · exact fun hv => mul_nonpos_of_nonneg_of_nonpos ht.le hv -- [compile-fix end]
        · exact Filter.Eventually.of_forall fun v => by -- [compile-fix begin: reassociate the affine evaluation explicitly]
            change f.linear x+f.offset=0 at he
            change f.linear (x+v)+f.offset≤0 ↔ f.linear v≤0
            rw [map_add]
            constructor <;> intro hv <;> linarith [he] -- [compile-fix end]
      · refine ⟨∅,PolyhedralPredicate.empty,by simp,?_⟩
        have h : ContinuousAt (fun v:E3 => f (x+v)) 0 := -- [compile-fix]
          (f.continuous.comp (continuous_const.add continuous_id)).continuousAt -- [compile-fix]
        have hp' : ∀ᶠv in 𝓝 (0:E3),0<f (x+v) :=
          h.eventually (lt_mem_nhds (by simpa using hp))
        filter_upwards [hp'] with v hv
        exact iff_of_false (not_le_of_gt hv) (by simp)
  | compl h ih =>
      obtain ⟨C,hp,hc,hg⟩ := ih
      refine ⟨Cᶜ,hp.compl,fun a ha v => not_congr (hc a ha v),?_⟩
      filter_upwards [hg] with v hv
      exact not_congr hv
  | inter h k ih ik =>
      obtain ⟨C,hp,hc,hg⟩ := ih
      obtain ⟨D,kp,kc,kg⟩ := ik
      refine ⟨C∩D,hp.inter kp,fun a ha v => and_congr (hc a ha v) (kc a ha v),?_⟩
      filter_upwards [hg,kg] with v hv kv
      exact and_congr hv kv
  | union h k ih ik =>
      obtain ⟨C,hp,hc,hg⟩ := ih
      obtain ⟨D,kp,kc,kg⟩ := ik
      refine ⟨C∪D,hp.union kp,fun a ha v => or_congr (hc a ha v) (kc a ha v),?_⟩
      filter_upwards [hg,kg] with v hv kv
      exact or_congr hv kv
  | @iUnion ι _ S h ih =>
      choose C hp hc hg using ih
      refine ⟨⋃i,C i,PolyhedralPredicate.iUnion _ hp,?_,?_⟩
      · intro a ha v
        simp only [Set.mem_iUnion]
        exact exists_congr fun i => hc i a ha v
      · have hall : ∀ᶠv in 𝓝 (0:E3),∀i,x+v∈S i ↔ v∈C i :=
          Filter.eventually_all.mpr hg
        filter_upwards [hall] with v hv
        simp only [Set.mem_iUnion]
        exact exists_congr hv

private theorem preimage_rigid_poly {S:Set E3} (hS:PolyhedralPredicate S)
    (g:RigidMotion) : PolyhedralPredicate (g ⁻¹' S) := by
  induction hS with
  | halfspace f =>
      let a : ScalarAffine := ⟨f.linear.comp g.linearIsometryEquiv.toLinearMap,f (g 0)⟩
      have he : {x:E3 | a x≤0}=g ⁻¹' {y:E3 | f y≤0} := by
        ext x
        simp only [Set.mem_preimage,Set.mem_setOf_eq]
        have hg := g.map_vadd (0:E3) x
        simp only [vadd_eq_add,add_zero] at hg
        rw [hg]
        change f.linear (g.linearIsometryEquiv x)+f (g 0)≤0 ↔ _
        simp only [map_add]
        rw [add_assoc] -- [compile-fix]
      rw [←he]
      exact PolyhedralPredicate.halfspace a
  | compl h ih => simpa using ih.compl
  | inter h k ih ik => simpa using ih.inter ik
  | union h k ih ik => simpa using ih.union ik
  | iUnion S h ih => simpa only [Set.preimage_iUnion] using PolyhedralPredicate.iUnion _ ih

theorem placed_tangent_measurable_null_frontier (g:RigidMotion) (x:E3) :
    MeasurableSet (tangentCone (g '' Q) x) ∧
      volume (frontier (tangentCone (g '' Q) x))=0 := by
  have hpoly : PolyhedralPredicate (g '' Q) := by
    have he : g '' Q = g.symm ⁻¹' Q := by -- [compile-fix begin: avoid coercion-sensitive image_eq_preimage_symm]
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        simpa using hz
      · intro hy
        exact ⟨g.symm y,hy,g.apply_symm_apply y⟩
    rw [he] -- [compile-fix end]
    exact preimage_rigid_poly Q_polyhedral g.symm
  obtain ⟨C,hC,hscale,hgerm⟩ := local_polyhedral_cone hpoly x
  rw [LocalCone.tangent_eq hscale hgerm]
  exact polyhedral_measure hC

/-- Disjoint open interiors suffice for finite additivity once the null
boundaries are proved. This theorem preserves all boundary directions. -/
theorem finite_cone_solidAngle_sum {ι:Type} [Fintype ι]
    (C:ι→Set E3)
    (hm:∀i,MeasurableSet (C i)) (hn:∀i,volume (frontier (C i))=0)
    (hd:Pairwise (fun i j => Disjoint (interior (C i)) (interior (C j))))
    (hc:∀v:E3,∃i,v∈C i) :
    ∑i,solidAngle (C i)=ENNReal.ofReal (4*Real.pi) := by
  classical
  let B : Set E3 := Metric.closedBall (0:E3) 1
  let O (i:ι) := interior (C i)∩B
  have hav (i:ι) : ∀ᵐv ∂volume,v∉frontier (C i) := by
    apply ae_iff.mpr
    simpa using hn i
    -- API?: ae_iff identifies the exceptional-set measure with zero.
  have heq (i:ι) : volume (C i∩B)=volume (O i) := by
    apply measure_congr
    filter_upwards [hav i] with v hv
    have hcint : v∈C i ↔ v∈interior (C i) := by
      constructor
      · intro hcv
        by_contra hi
        exact hv ⟨subset_closure hcv,hi⟩
      · intro hiv -- [compile-fix]
        exact interior_subset hiv -- [compile-fix]
    exact propext (and_congr hcint Iff.rfl) -- [compile-fix]
  have hmu : volume (⋃i,O i)=volume B := by
    apply measure_congr
    have hall : ∀ᵐv ∂volume,∀i,v∉frontier (C i) :=
      Filter.eventually_all.mpr hav
    filter_upwards [hall] with v hv
    apply propext -- [compile-fix]
    constructor
    · intro h
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp h
      exact hi.2
    · intro hb
      obtain ⟨i,hi⟩ := hc v
      apply Set.mem_iUnion.mpr
      refine ⟨i,?_,hb⟩
      by_contra hnint
      exact hv i ⟨subset_closure hi,hnint⟩
  have hdisj : Pairwise (fun i j => Disjoint (O i) (O j)) := by
    intro i j hij
    exact (hd hij).mono inter_subset_left inter_subset_left
  have hmeas (i:ι) : MeasurableSet (O i) :=
    isOpen_interior.measurableSet.inter measurableSet_closedBall
  have hsum : ∑i,volume (C i∩B)=volume B := by
    simp_rw [heq]
    rw [←hmu]
    simpa only [tsum_fintype] using (measure_iUnion hdisj hmeas).symm
    -- API?: measure_iUnion for disjoint measurable sets, finite tsum.
  simp only [solidAngle]
  rw [←Finset.mul_sum,hsum]
  dsimp [B]
  rw [EuclideanSpace.volume_closedBall_fin_three]
    -- API?: actual three-dimensional Euclidean closed-ball volume formula,
    -- as already used in the accepted ConnectedFeatureCompanion proof.
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
    _=4*ENNReal.ofReal Real.pi := by rw [hnum] -- [compile-fix end]

/-- Turn geometric label semantics into the REAL sector sum. -/
theorem incident_angle_sum (hbudget:ConeSectorBudgets Q) (hlist:CompleteDihedralList Q)
    (T:Tiling Q) (x:E3) (I:Finset RigidMotion)
    (hI:∀h,h∈I ↔ h∈T.placements ∧ x∈h '' Q)
    (label:RigidMotion→SectorLabel)
    (hangle:∀h∈I,solidAngle (tangentCone (h '' Q) x)=
      ENNReal.ofReal (2*(label h).angle)) :
    ∑h∈I,(label h).angle=2*Real.pi := by
  classical
  let ι := {h:RigidMotion // h∈I}
  have hmem (i:ι) := (hI i.1).mp i.2
  have hdata (i:ι) := placed_tangent_measurable_null_frontier i.1 x
  have hd : Pairwise (fun i j:ι => Disjoint
      (interior (tangentCone (i.1 '' Q) x))
      (interior (tangentCone (j.1 '' Q) x))) := by
    intro i j hij
    exact (hbudget T x).2.1 (hmem i).1 (hmem j).1 (hmem i).2 (hmem j).2
      (fun h => hij (Subtype.ext h))
  have hcover (v:E3) : ∃i:ι,v∈tangentCone (i.1 '' Q) x := by
    obtain ⟨h,hh,hx,hv⟩ := (hbudget T x).2.2 v
    exact ⟨⟨h,(hI h).mpr ⟨hh,hx⟩⟩,hv⟩
  have he := finite_cone_solidAngle_sum
    (fun i:ι => tangentCone (i.1 '' Q) x)
    (fun i => (hdata i).1) (fun i => (hdata i).2) hd hcover
  have hnonneg (h:RigidMotion) : 0≤(label h).angle := by
    cases hl : label h with
    | ordinary k => simp [hl,SectorLabel.angle]; positivity
    | feature k r =>
        have hb := (feature_angle_bounds hlist r k).1
        change 0≤featureInteriorAngle r k
        linarith [Real.pi_pos]
  have he' : ENNReal.ofReal (∑i:ι,2*(label i.1).angle)=
      ENNReal.ofReal (4*Real.pi) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (by norm_num) (hnonneg i.1))]
      -- API?: ofReal_sum_of_nonneg for a finite real sum.
    calc
      (∑i:ι,ENNReal.ofReal (2*(label i.1).angle)) =
          ∑i:ι,solidAngle (tangentCone (i.1 '' Q) x) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hangle i.1 i.2).symm
      _ = _ := he
  have hreal : (∑i:ι,2*(label i.1).angle)=4*Real.pi := -- [compile-fix]
    (ENNReal.ofReal_eq_ofReal_iff -- [compile-fix]
      (Finset.sum_nonneg (fun i _ => mul_nonneg (by norm_num) (hnonneg i.1))) -- [compile-fix]
      (mul_nonneg (by norm_num) Real.pi_pos.le)).mp he' -- [compile-fix]
    -- API?: injectivity of ENNReal.ofReal on nonnegative reals.
  have hsum : (∑i:ι,(label i.1).angle)=∑h∈I,(label h).angle := by
    exact Finset.sum_coe_sort I (fun h => (label h).angle)
    -- API?: sum over the subtype of a finset equals the bounded finite sum.
  rw [←Finset.mul_sum,hsum] at hreal
  linarith

end
end R44.DischargeConeMeasure
