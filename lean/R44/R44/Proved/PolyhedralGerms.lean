/- -- [compile-fix]
# Finite affine predicates have exact local conical germs

Written source: proof/ALIGNMENT_PROOF.md A-L2.2.  This expands the sentence
"locally every polyhedral tile agrees with a cone" for the actual set Q.
No mesh/dihedral-volume admission is imported.  Boolean operations are
allowed: the signed-tent definition contains implications and recesses.
The cone is the frozen R44.tangentCone, not Mathlib's contingent cone.

This is a new helper file, not a change to any frozen definition.  All
proofs are supplied; API-sensitive calls are identified inline.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.FeatureLocalCharts -- [compile-fix]
import R44.Proved.FeatureTubeMapsGlue -- [compile-fix]
import R44.Proved.FeatureTubeMapCarriesCarrier -- [compile-fix]

namespace R44.DischargePolyhedral
open Set Filter R44.DischargeGeometry R44.DischargeCharts
open scoped Topology
noncomputable section
set_option maxHeartbeats 0

/-- Continuous affine scalar functions, with explicit linear part. -/
structure ScalarAffine where
  linear : E3 →ₗ[ℝ] ℝ
  offset : ℝ

namespace ScalarAffine
instance : CoeFun ScalarAffine (fun _ => E3 → ℝ) := ⟨fun f x => f.linear x + f.offset⟩

theorem continuous (f : ScalarAffine) : Continuous f := by
  exact f.linear.continuous_of_finiteDimensional.add continuous_const
  -- API?: expected LinearMap.continuous_of_finiteDimensional.

def const (c : ℝ) : ScalarAffine := ⟨0,c⟩
def add (f g : ScalarAffine) : ScalarAffine := ⟨f.linear+g.linear,f.offset+g.offset⟩
def mul (a : ℝ) (f : ScalarAffine) : ScalarAffine := ⟨a • f.linear,a*f.offset⟩
def sub (f g : ScalarAffine) : ScalarAffine := add f (mul (-1) g)
def coord (i : Fin 3) : ScalarAffine :=
  ⟨{ toFun := fun x => x i
     map_add' := by intros; simp
     map_smul' := by intros; simp },0⟩
def coordN (i : Nat) : ScalarAffine := if h : i < 3 then coord ⟨i,h⟩ else const 0

@[simp] theorem const_apply (c : ℝ) (x : E3) : const c x = c := by simp [const] -- [compile-fix]
@[simp] theorem add_apply (f g : ScalarAffine) (x : E3) : add f g x = f x+g x := by
  simp [add]; ring
@[simp] theorem mul_apply (a : ℝ) (f : ScalarAffine) (x : E3) : mul a f x = a*f x := by
  simp [mul]; ring
@[simp] theorem sub_apply (f g : ScalarAffine) (x : E3) : sub f g x = f x-g x := by
  simp [sub]; ring
@[simp] theorem coord_apply (i : Fin 3) (x : E3) : coord i x = x i := by simp [coord]
@[simp] theorem coordN_apply (i : Nat) (x : E3) : coordN i x = frameCoordinate x i := by
  by_cases h : i < 3 <;> simp [coordN,frameCoordinate,h,coord,const] -- [compile-fix]
@[simp] theorem eval_add (f : ScalarAffine) (x u : E3) :
    f (x+u) = f x+f.linear u := by
  change f.linear (x+u)+f.offset = _
  rw [map_add]; ring
end ScalarAffine

/-- A finite Boolean combination of affine halfspaces. Finite indexed union
is a constructor so no flattening into a giant DNF is needed. -/
inductive PolyhedralPredicate : Set E3 → Prop
  | halfspace (f : ScalarAffine) : PolyhedralPredicate {x | f x ≤ 0}
  | compl {S : Set E3} : PolyhedralPredicate S → PolyhedralPredicate Sᶜ
  | inter {S T : Set E3} : PolyhedralPredicate S → PolyhedralPredicate T →
      PolyhedralPredicate (S ∩ T)
  | union {S T : Set E3} : PolyhedralPredicate S → PolyhedralPredicate T →
      PolyhedralPredicate (S ∪ T)
  | iUnion {ι : Type} [Finite ι] (S : ι → Set E3) :
      (∀ i, PolyhedralPredicate (S i)) → PolyhedralPredicate (⋃ i, S i)

namespace PolyhedralPredicate

theorem univ : PolyhedralPredicate (Set.univ : Set E3) := by
  simpa using halfspace (ScalarAffine.const 0)

theorem empty : PolyhedralPredicate (∅ : Set E3) := by simpa using univ.compl

theorem iInter {ι : Type} [Finite ι] (S : ι → Set E3)
    (hS : ∀ i, PolyhedralPredicate (S i)) : PolyhedralPredicate (⋂ i,S i) := by
  have h := (PolyhedralPredicate.iUnion (fun i => (S i)ᶜ) (fun i => (hS i).compl)).compl
  simpa only [Set.compl_iUnion,compl_compl] using h -- [compile-fix]

theorem le_affine (f g : ScalarAffine) : PolyhedralPredicate {x | f x ≤ g x} := by
  simpa only [ScalarAffine.sub_apply,sub_nonpos] using halfspace (f.sub g)
end PolyhedralPredicate

/-- A finite affine chart cover for a real-valued piecewise-affine function.
The cover is NOT required to be disjoint; ties in max/min are harmless. -/
structure AffineCover (f : E3 → ℝ) where
  Index : Type
  finite : Finite Index
  cell : Index → Set E3
  poly : ∀ i, PolyhedralPredicate (cell i)
  form : Index → ScalarAffine
  covers : ∀ x, ∃ i, x ∈ cell i
  agrees : ∀ i x, x ∈ cell i → f x = form i x

namespace AffineCover

def affine (a : ScalarAffine) : AffineCover a where
  Index := Unit
  finite := inferInstance
  cell := fun _ => univ
  poly := fun _ => PolyhedralPredicate.univ
  form := fun _ => a
  covers := fun _ => ⟨(), trivial⟩
  agrees := by intros; rfl

def constant (c : ℝ) : AffineCover (fun _ => c) := by -- [compile-fix]
  simpa only [ScalarAffine.const_apply] using affine (.const c) -- [compile-fix]

def add {f g : E3 → ℝ} (A : AffineCover f) (B : AffineCover g) :
    AffineCover (fun x => f x+g x) := by
  letI := A.finite; letI := B.finite
  exact {
    Index := A.Index × B.Index
    finite := inferInstance
    cell := fun ij => A.cell ij.1 ∩ B.cell ij.2
    poly := fun ij => (A.poly ij.1).inter (B.poly ij.2)
    form := fun ij => (A.form ij.1).add (B.form ij.2)
    covers := by intro x; obtain ⟨i,hi⟩ := A.covers x; obtain ⟨j,hj⟩ := B.covers x
                 exact ⟨(i,j),hi,hj⟩
    agrees := by intro ij x hx; simp only [ScalarAffine.add_apply]
                 rw [A.agrees _ _ hx.1,B.agrees _ _ hx.2] }

def smul {f : E3 → ℝ} (a : ℝ) (A : AffineCover f) :
    AffineCover (fun x => a*f x) where
  Index := A.Index
  finite := A.finite
  cell := A.cell
  poly := A.poly
  form := fun i => ScalarAffine.mul a (A.form i)
  covers := A.covers
  agrees := by intro i x hx; simp only [ScalarAffine.mul_apply]; rw [A.agrees _ _ hx]

def max {f g : E3 → ℝ} (A : AffineCover f) (B : AffineCover g) :
    AffineCover (fun x => max (f x) (g x)) := by
  letI := A.finite; letI := B.finite
  refine {
    Index := A.Index × B.Index × Bool
    finite := inferInstance
    cell := fun ijb => A.cell ijb.1 ∩ B.cell ijb.2.1 ∩
      (if ijb.2.2 then {x | A.form ijb.1 x ≤ B.form ijb.2.1 x}
       else {x | B.form ijb.2.1 x ≤ A.form ijb.1 x})
    poly := ?_
    form := fun ijb => if ijb.2.2 then B.form ijb.2.1 else A.form ijb.1
    covers := ?_
    agrees := ?_ }
  · intro ⟨i,j,b⟩
    cases b <;> simp only [Bool.false_eq_true,if_false,if_true]
    · exact ((A.poly i).inter (B.poly j)).inter (PolyhedralPredicate.le_affine _ _)
    · exact ((A.poly i).inter (B.poly j)).inter (PolyhedralPredicate.le_affine _ _)
  · intro x
    obtain ⟨i,hi⟩ := A.covers x; obtain ⟨j,hj⟩ := B.covers x
    rcases le_total (A.form i x) (B.form j x) with h | h
    · exact ⟨(i,j,true),⟨hi,hj⟩,h⟩
    · exact ⟨(i,j,false),⟨hi,hj⟩,h⟩
  · rintro ⟨i,j,b⟩ x hx
    rw [A.agrees i x hx.1.1,B.agrees j x hx.1.2]
    cases b
    · exact max_eq_left hx.2
    · exact max_eq_right hx.2

def abs {f : E3 → ℝ} (A : AffineCover f) : AffineCover (fun x => |f x|) := by
  simpa only [neg_one_mul, ← abs_eq_max_neg] using A.max (A.smul (-1)) -- [compile-fix]
  -- API?: expected max_neg_self x : max x (-x) = |x|.

theorem le_poly {f g : E3 → ℝ} (A : AffineCover f) (B : AffineCover g) :
    PolyhedralPredicate {x | f x ≤ g x} := by
  letI := A.finite; letI := B.finite
  have heq : {x | f x ≤ g x} =
      ⋃ ij : A.Index × B.Index,
        (A.cell ij.1 ∩ B.cell ij.2 ∩ {x | A.form ij.1 x ≤ B.form ij.2 x}) := by
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_inter_iff]
    constructor
    · intro h
      obtain ⟨i,hi⟩ := A.covers x; obtain ⟨j,hj⟩ := B.covers x
      exact ⟨(i,j),⟨hi,hj⟩,by -- [compile-fix]
        change A.form i x ≤ B.form j x -- [compile-fix]
        rwa [← A.agrees i x hi,← B.agrees j x hj]⟩ -- [compile-fix]
    · rintro ⟨⟨i,j⟩,⟨hi,hj⟩,h⟩
      rwa [A.agrees i x hi,B.agrees j x hj]
  rw [heq]
  exact PolyhedralPredicate.iUnion _ fun ij =>
    ((A.poly ij.1).inter (B.poly ij.2)).inter (PolyhedralPredicate.le_affine _ _)
end AffineCover

private def coordCover (i : Nat) : AffineCover (fun x => frameCoordinate x i) :=
  by simpa only [ScalarAffine.coordN_apply] using AffineCover.affine (.coordN i) -- [compile-fix]

private def shiftedCoordCover (c : E3) (i : Nat) :
    AffineCover (fun x => frameCoordinate (x-c) i) := by
  have h := (coordCover i).add (AffineCover.constant (-frameCoordinate c i))
  convert h using 1
  funext x
  unfold frameCoordinate
  split_ifs <;> simp [sub_eq_add_neg] -- [compile-fix]

private def normalCover (r : Role) : AffineCover (featureNormalCoordinate r) :=
  (shiftedCoordCover (featureCenter r) (featureAxis r)).smul
    ((nativeFeatureData r).normal.get (featureAxis r) : ℝ)

private def radiusCover (r : Role) : AffineCover (featureRadius r) :=
  ((shiftedCoordCover (featureCenter r) (featureTangentAxes r).1).abs).max
    ((shiftedCoordCover (featureCenter r) (featureTangentAxes r).2).abs)

private def heightCover (r : Role) : AffineCover (featureHeight r) := by
  have h := ((AffineCover.constant 0).max
    ((AffineCover.constant 1).add ((radiusCover r).smul (-1/eta)))).smul
      ((profileCoefficient r : ℝ)/10000)
  convert h using 1
  funext x
  simp only [featureHeight]
  congr 2
  ring

private theorem tube_poly (r : Role) :
    PolyhedralPredicate {x | featureTubeSupport r x} :=
  ((radiusCover r).le_poly (AffineCover.constant eta)).inter
    ((normalCover r).abs.le_poly (AffineCover.constant eta))

private theorem height_ineq_poly (r : Role) :
    PolyhedralPredicate {x | featureNormalCoordinate r x ≤ featureHeight r x} :=
  (normalCover r).le_poly (heightCover r)

private theorem normal_nonneg_poly (r : Role) :
    PolyhedralPredicate {x | 0 ≤ featureNormalCoordinate r x} :=
  (AffineCover.constant 0).le_poly (normalCover r)

theorem P_polyhedral : PolyhedralPredicate P := by
  classical
  let I := {a : V3 // a ∈ chairCells}
  haveI : Finite I := (List.finite_toSet chairCells).to_subtype
    -- API?: expected finite subtype from finiteness of list membership.
  have hcube (a : V3) : PolyhedralPredicate (unitCube a) := by
    have heq : unitCube a = ⋂ i : Fin 3,
        ({x | (a.get i : ℝ) ≤ x i} ∩ {x | x i ≤ (a.get i : ℝ)+1}) := by
      ext x; simp [unitCube]
    rw [heq]
    apply PolyhedralPredicate.iInter
    intro i
    simpa [frameCoordinate] using ((AffineCover.constant (a.get i : ℝ)).le_poly -- [compile-fix]
      (coordCover i)).inter -- [compile-fix]
      ((coordCover i).le_poly -- [compile-fix]
        (AffineCover.constant ((a.get i : ℝ)+1))) -- [compile-fix]
  have heq : P = ⋃ a : I, unitCube a.1 := by
    ext x; simp only [P,Set.mem_setOf_eq,Set.mem_iUnion]
    exact ⟨fun ⟨a,ha,hx⟩ => ⟨⟨a,ha⟩,hx⟩,fun ⟨a,hx⟩ => ⟨a.1,a.2,hx⟩⟩
  rw [heq]
  exact PolyhedralPredicate.iUnion _ fun a => hcube a.1

/-- Interpret the ACTUAL global Q predicate as a finite affine predicate.
No surface mesh, dihedral classifier, or assumed alignment enters. -/
theorem Q_polyhedral : PolyhedralPredicate Q := by
  classical
  let recess (r : Role) : Set E3 :=
    if profileCoefficient r < 0 then
      ({x | featureTubeSupport r x}ᶜ ∪
       {x | featureNormalCoordinate r x ≤ featureHeight r x}) else univ
  let bump (r : Role) : Set E3 :=
    if 0 < profileCoefficient r then
      ({x | featureTubeSupport r x} ∩ {x | 0 ≤ featureNormalCoordinate r x} ∩
       {x | featureNormalCoordinate r x ≤ featureHeight r x}) else ∅
  have hr (r : Role) : PolyhedralPredicate (recess r) := by
    dsimp [recess]; split_ifs
    · exact (tube_poly r).compl.union (height_ineq_poly r)
    · exact PolyhedralPredicate.univ
  have hb (r : Role) : PolyhedralPredicate (bump r) := by
    dsimp [bump]; split_ifs
    · exact ((tube_poly r).inter (normal_nonneg_poly r)).inter (height_ineq_poly r)
    · exact PolyhedralPredicate.empty
  have heq : Q = (P ∩ ⋂ r, recess r) ∪ ⋃ r, bump r := by
    ext x
    simp only [Q,recess,bump,Set.mem_union,Set.mem_inter_iff,
      Set.mem_iInter,Set.mem_iUnion,Set.mem_setOf_eq]
    constructor
    · rintro (⟨hx,hrx⟩ | ⟨r,hpos,ht,h0,h1⟩)
      · left; refine ⟨hx,?_⟩; intro r; split_ifs with hn
        · by_cases ht : featureTubeSupport r x
          · exact Or.inr (hrx r hn ht)
          · exact Or.inl ht
        · trivial
      · right; exact ⟨r,by simp only [hpos,if_pos]; exact ⟨⟨ht,h0⟩,h1⟩⟩
    · rintro (⟨hx,hrx⟩ | ⟨r,hrx⟩)
      · left; refine ⟨hx,?_⟩; intro r hn ht
        have h := hrx r
        simp only [hn,if_pos] at h
        exact h.resolve_left (not_not_intro ht) -- [compile-fix]
      · right; by_cases hp : 0 < profileCoefficient r
        · simp only [hp,if_pos] at hrx
          exact ⟨r,hp,hrx.1.1,hrx.1.2,hrx.2⟩
        · simpa [hp] using hrx
  rw [heq]
  exact (P_polyhedral.inter (PolyhedralPredicate.iInter _ hr)).union
    (PolyhedralPredicate.iUnion _ hb)

/-- Exact positive-homogeneous local model; germ is in all ambient directions. -/
def LocalCone (S : Set E3) (x : E3) : Prop :=
  ∃ C : Set E3,
    (∀ (a : ℝ), 0 < a → ∀ v : E3, a • v ∈ C ↔ v ∈ C) ∧
    (∀ᶠ v in 𝓝 (0 : E3), x+v ∈ S ↔ v ∈ C)

private theorem localCone_halfspace (f : ScalarAffine) (x : E3) :
    LocalCone {y | f y ≤ 0} x := by
  rcases lt_trichotomy (f x) 0 with hneg | hzero | hpos
  · refine ⟨univ,by simp,?_⟩
    have ht : ContinuousAt (fun v : E3 => f (x+v)) 0 :=
      (f.continuous.comp (continuous_const.add continuous_id)).continuousAt
    have hn : ∀ᶠ v in 𝓝 (0 : E3), f (x+v)<0 :=
      ht.eventually (gt_mem_nhds (by simpa using hneg))
      -- API?: ContinuousAt.eventually pulls back the open order neighborhood.
    filter_upwards [hn] with v hv
    exact iff_of_true hv.le trivial
  · refine ⟨{v | f.linear v ≤ 0},?_,?_⟩
    · intro a ha v -- [compile-fix]
      change f.linear (a • v) ≤ 0 ↔ f.linear v ≤ 0 -- [compile-fix]
      rw [map_smul] -- [compile-fix]
      simp only [smul_eq_mul] -- [compile-fix]
      constructor <;> intro h <;> nlinarith -- [compile-fix]
      -- API?: expected positivity cancellation on mul ≤ 0.
    · exact Filter.Eventually.of_forall fun v => by
        simp only [Set.mem_setOf_eq,ScalarAffine.eval_add,hzero,zero_add]
  · refine ⟨∅,by simp,?_⟩
    have ht : ContinuousAt (fun v : E3 => f (x+v)) 0 :=
      (f.continuous.comp (continuous_const.add continuous_id)).continuousAt
    have hn : ∀ᶠ v in 𝓝 (0 : E3), 0<f (x+v) :=
      ht.eventually (lt_mem_nhds (by simpa using hpos))
      -- API?: same continuous order-neighborhood pullback.
    filter_upwards [hn] with v hv
    exact iff_of_false (not_le_of_gt hv) (by simp)

/-- A-L2.2's local conicality, including points on arbitrary intersections
of face charts and carrier edges. -/
theorem PolyhedralPredicate.localCone {S : Set E3}
    (hS : PolyhedralPredicate S) (x : E3) : LocalCone S x := by
  induction hS with
  | halfspace f => exact localCone_halfspace f x
  | compl h ih =>
      obtain ⟨C,hC,hg⟩ := ih
      refine ⟨Cᶜ,?_,?_⟩
      · intro a ha v; exact not_congr (hC a ha v)
      · filter_upwards [hg] with v hv; exact not_congr hv
  | inter hS hT ihS ihT =>
      obtain ⟨C,hC,hg⟩ := ihS; obtain ⟨D,hD,hh⟩ := ihT
      refine ⟨C∩D,?_,?_⟩
      · intro a ha v; exact and_congr (hC a ha v) (hD a ha v)
      · filter_upwards [hg,hh] with v hv hw; exact and_congr hv hw
  | union hS hT ihS ihT =>
      obtain ⟨C,hC,hg⟩ := ihS; obtain ⟨D,hD,hh⟩ := ihT
      refine ⟨C∪D,?_,?_⟩
      · intro a ha v; exact or_congr (hC a ha v) (hD a ha v)
      · filter_upwards [hg,hh] with v hv hw; exact or_congr hv hw
  | @iUnion ι _ S hS ih =>
      choose C hC hg using ih
      refine ⟨⋃ i,C i,?_,?_⟩
      · intro a ha v; simp only [Set.mem_iUnion]
        exact exists_congr fun i => hC i a ha v
      · have hall : ∀ᶠ v in 𝓝 (0 : E3), ∀ i, x+v ∈ S i ↔ v ∈ C i :=
          (Filter.eventually_all).mpr hg
          -- API?: eventually_all for a finite index type.
        filter_upwards [hall] with v hv
        simp only [Set.mem_iUnion]
        exact exists_congr hv

/-- Affine-isometric transport does not require a registered orientation. -/
theorem LocalCone.image {S : Set E3} {x : E3} (h : LocalCone S x)
    (g : RigidMotion) : LocalCone (g '' S) (g x) := by
  obtain ⟨C,hC,hg⟩ := h
  let A := g.linearIsometryEquiv
  refine ⟨A '' C,?_,?_⟩
  · intro a ha v
    rw [A.image_eq_preimage_symm] -- [compile-fix]
    simp only [Set.mem_preimage, map_smul] -- [compile-fix]
    exact hC a ha (A.symm v)
  · have he : Tendsto A.symm (𝓝 (0 : E3)) (𝓝 (0 : E3)) := by
      simpa using A.symm.continuous.tendsto (0 : E3)
    have hp := he.eventually hg
    filter_upwards [hp] with v hv
    have hmap : g (x+A.symm v)=g x+v := by
      simpa [A,vadd_eq_add,add_comm] using g.map_vadd x (A.symm v)
    have hleft : g x+v ∈ g '' S ↔ x+A.symm v ∈ S := by
      rw [← hmap]
      constructor
      · rintro ⟨y,hy,heq⟩
        exact g.injective heq ▸ hy
      · intro hy; exact ⟨x+A.symm v,hy,rfl⟩
    have hright : v ∈ A '' C ↔ A.symm v ∈ C := by
      constructor
      · rintro ⟨y,hy,heq⟩
        have hh : A.symm v=y := by rw [← heq]; simp
        exact hh.symm ▸ hy
      · intro hy; exact ⟨A.symm v,hy,by simp⟩
    exact hleft.trans (hv.trans hright.symm)

/-- The local model is exactly the frozen radial tangent cone. -/
theorem LocalCone.tangent_eq {S C : Set E3} {x : E3}
    (hC : ∀ a : ℝ, 0<a → ∀ v : E3, a • v ∈ C ↔ v ∈ C)
    (hg : ∀ᶠ v in 𝓝 (0 : E3), x+v ∈ S ↔ v ∈ C) :
    tangentCone S x = C := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hg
    -- API?: Metric.mem_nhds_iff: ball of positive radius included in the event set.
  ext v
  let ε := δ/(‖v‖+1)
  have he : 0<ε := div_pos hδ (by positivity)
  have hsmall {t : ℝ} (ht : 0<t) (htε : t<ε) : t • v ∈ Metric.ball 0 δ := by
    simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    have hm : t*(‖v‖+1)<δ := (lt_div_iff₀ (by positivity)).mp htε
    nlinarith [norm_nonneg v]
  constructor
  · rintro ⟨e,he0,hev⟩
    let t := min e ε / 2
    have ht : 0<t := half_pos (lt_min he0 he)
    have hte : t<e := (half_lt_self (lt_min he0 he)).trans_le (min_le_left _ _)
    have htε : t<ε := (half_lt_self (lt_min he0 he)).trans_le (min_le_right _ _)
    exact (hC t ht v).mp ((hball (hsmall ht htε)).mp (hev t ht hte))
  · intro hv
    exact ⟨ε,he,fun t ht hte => (hball (hsmall ht hte)).mpr ((hC t ht v).mpr hv)⟩

/-- All moved copies of Q are locally conical, with no alignment premise. -/
theorem Q_placed_localCone (g : RigidMotion) (x : E3) :
    LocalCone (g '' Q) x := by
  simpa using (Q_polyhedral.localCone (g.symm x)).image g

/-- Concrete object facts from the three previously discharged F2 maps. -/
theorem Q_object : CompactRegularClosedBall Q :=
  compactRegularClosedBall_of_tube_homeomorphism
    (hasTubeHomeomorphism_of_tube_construction per_tube_homeomorphisms_holds
      feature_tube_maps_glue_holds feature_tube_map_carries_carrier_holds)

end
end R44.DischargePolyhedral
