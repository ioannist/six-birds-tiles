/- -- [compile-fix: promoted to Proved after exchange 7]
# Halfspace and right/reentrant carrier-edge meridians

Written source: A-L2.2/A-L3.1. The ordinary angles are interpreted as
orthogonal images of ACTUAL angular sectors and use the accepted sector
area and wedge-volume theorem. None is assigned by definition to solidAngle.
This includes the affine (sloping) interiors of the pyramid faces.
No mathematical admissions; no mesh or dihedral premise.
-/
import R44.Proved.NativeFeatureMeridians -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeOrdinary
open Set DischargePyramid DischargeAngular DischargeMeridian
open DischargeMeridianFrames DischargeTentCones DischargeWedge DischargePlanar
noncomputable section
set_option maxHeartbeats 0

def halfDown : Set E3 := {w | w 2≤0}
def rightDown : Set E3 := {w | w 0≤0 ∧ w 1≤0}
def reentrantDown : Set E3 := {w | w 0≤0 ∨ w 1≤0}

def halfDown_meridian : AngularMeridian halfDown Real.pi := by -- [compile-fix: structure-valued declaration]
  simpa [baseCone,halfDown] using canonical_base_meridian 0

private theorem quarter_cos :
    Real.cos (-Real.pi/4)=Real.sqrt 2/2 ∧
    Real.sin (-Real.pi/4)=-(Real.sqrt 2/2) := by
  simp [neg_div,Real.cos_neg,Real.sin_neg,Real.cos_pi_div_four,Real.sin_pi_div_four]
  -- API?: the special-angle values sin(pi/4)=cos(pi/4)=sqrt(2)/2.

-- [compile-fix begin: use the current sign-disjunction API]
private theorem quarter_right :
    rightDown=turn (-Real.pi/4) '' {w:E3 | w 1≤-|w 0|} := by
  apply set_image_of_test
  intro w
  have hc : 0<Real.sqrt 2/2 := by positivity
  have ha : -|w 0|=min (w 0) (-(w 0)) := by
    -- [compile-fix: prove the min/absolute-value identity by signs]
    by_cases h : 0 ≤ w 0
    · rw [abs_of_nonneg h, min_eq_right (by linarith)]
    · have h' : w 0 ≤ 0 := le_of_not_ge h
      rw [abs_of_nonpos h', min_eq_left (by linarith)]
      ring
  simp only [rightDown,Set.mem_setOf_eq,turn_apply,pt,
    Matrix.cons_val_zero,Matrix.cons_val_one,
    quarter_cos.1,quarter_cos.2]
  rw [show Real.sqrt 2/2*w 0-(-(Real.sqrt 2/2))*w 1=
      (Real.sqrt 2/2)*(w 0+w 1) by ring,
    show -(Real.sqrt 2/2)*w 0+Real.sqrt 2/2*w 1=
      (Real.sqrt 2/2)*(w 1-w 0) by ring,
    mul_nonpos_iff,mul_nonpos_iff,ha,le_min_iff]
  simp only [hc.le, true_and, not_le_of_gt hc, false_and, or_false]
  constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith
-- [compile-fix end]

-- [compile-fix begin: use the current sign-disjunction API]
private theorem quarter_reentrant :
    reentrantDown=turn (-Real.pi/4) '' {w:E3 | w 1≤|w 0|} := by
  apply set_image_of_test
  intro w
  have hc : 0<Real.sqrt 2/2 := by positivity
  simp only [reentrantDown,Set.mem_setOf_eq,turn_apply,pt,
    Matrix.cons_val_zero,Matrix.cons_val_one,
    quarter_cos.1,quarter_cos.2]
  rw [show Real.sqrt 2/2*w 0-(-(Real.sqrt 2/2))*w 1=
      (Real.sqrt 2/2)*(w 0+w 1) by ring,
    show -(Real.sqrt 2/2)*w 0+Real.sqrt 2/2*w 1=
      (Real.sqrt 2/2)*(w 1-w 0) by ring,
    mul_nonpos_iff,mul_nonpos_iff,
    abs_eq_max_neg,le_max_iff]
  simp only [hc.le, true_and, not_le_of_gt hc, false_and, or_false]
  constructor <;> rintro (h|h) <;> first
  | exact Or.inl (by linarith)
  | exact Or.inr (by linarith)
-- [compile-fix end]

def rightDown_meridian : AngularMeridian rightDown (Real.pi/2) := by -- [compile-fix: structure-valued declaration]
  obtain ⟨hl,hu,he⟩ := lowerV_angular 1
  have ha : Real.pi-2*Real.arctan (1:ℝ)=Real.pi/2 := by
    rw [Real.arctan_one]; ring
  rw [ha] at he hl hu
  refine ⟨turn (-Real.pi/4)*turn (-Real.pi/2),hl.le,hu,?_⟩
  rw [quarter_right,show {w:E3 | w 1≤-|w 0|}=
      {w:E3 | w 1≤-(1:ℝ)*|w 0|} by simp,he,Set.image_image]
  rfl

def reentrantDown_meridian : AngularMeridian reentrantDown (3*Real.pi/2) := by -- [compile-fix: structure-valued declaration]
  obtain ⟨hl,hu,he⟩ := lowerV_angular (-1)
  have ha : Real.pi-2*Real.arctan (-1:ℝ)=3*Real.pi/2 := by
    rw [Real.arctan_neg,Real.arctan_one]; ring
  rw [ha] at he hl hu
  refine ⟨turn (-Real.pi/4)*turn (-Real.pi/2),hl.le,hu,?_⟩
  rw [quarter_reentrant,show {w:E3 | w 1≤|w 0|}=
      {w:E3 | w 1≤-(-1:ℝ)*|w 0|} by simp,he,Set.image_image]
  rfl

/-- The remaining coordinate in three dimensions. -/
def third (i j : Fin 3) (hij : i≠j) : Fin 3 :=
  ⟨3-i.val-j.val, by fin_cases i <;> fin_cases j <;> simp_all <;> omega⟩

private def coordVec (i : Fin 3) : E3 := WithLp.toLp 2 fun k => if k=i then 1 else 0
private def coordinateLinear (i j : Fin 3) (hij : i≠j) (si sj : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun := fun w => (si*w 0) • coordVec i+(sj*w 1) • coordVec j+
    w 2 • coordVec (third i j hij)
  map_add' := by intros; simp; module
  map_smul' := by intros; simp; module

/-- Native axes i,j receive signed meridian coordinates 0,1. -/
def coordinateAxes (i j : Fin 3) (hij : i≠j) (si sj : ℝ)
    (hsi : si=1 ∨ si= -1) (hsj : sj=1 ∨ sj= -1) : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.ofSurjective
    ({toLinearMap := coordinateLinear i j hij si sj
      norm_map' := by
        intro w
        have he : ‖coordinateLinear i j hij si sj w‖^2=‖w‖^2 := by
          -- [compile-fix: eliminate impossible equal-index cases before reducing `third`]
          fin_cases i <;> fin_cases j
          all_goals try { exact (hij rfl).elim }
          all_goals
            rcases hsi with rfl|rfl <;> rcases hsj with rfl|rfl <;>
            simp [DischargePyramid.norm_sq,coordinateLinear,coordVec,third,pt] <;> ring
        nlinarith [norm_nonneg (coordinateLinear i j hij si sj w),norm_nonneg w]}
      : E3 →ₗᵢ[ℝ] E3)
    (by
      intro x
      refine ⟨pt (si*x i) (sj*x j) (x (third i j hij)),?_⟩
      -- [compile-fix: eliminate impossible equal-index cases before reducing `third`]
      fin_cases i <;> fin_cases j
      all_goals try { exact (hij rfl).elim }
      all_goals
        rcases hsi with rfl|rfl <;> rcases hsj with rfl|rfl <;>
        ext k <;> fin_cases k <;> simp [coordinateLinear,coordVec,third,pt])

@[simp] theorem coordinateAxes_i (i j : Fin 3) (hij : i≠j) (si sj : ℝ)
    (hsi : si=1 ∨ si= -1) (hsj : sj=1 ∨ sj= -1) (w : E3) :
    coordinateAxes i j hij si sj hsi hsj w i=si*w 0 := by
  -- [compile-fix: avoid dependent reduction of `third` in impossible cases]
  fin_cases i <;> fin_cases j
  all_goals try { exact (hij rfl).elim }
  all_goals simp [coordinateAxes,coordinateLinear,coordVec,third]

@[simp] theorem coordinateAxes_j (i j : Fin 3) (hij : i≠j) (si sj : ℝ)
    (hsi : si=1 ∨ si= -1) (hsj : sj=1 ∨ sj= -1) (w : E3) :
    coordinateAxes i j hij si sj hsi hsj w j=sj*w 1 := by
  -- [compile-fix: avoid dependent reduction of `third` in impossible cases]
  fin_cases i <;> fin_cases j
  all_goals try { exact (hij rfl).elim }
  all_goals simp [coordinateAxes,coordinateLinear,coordVec,third]

/-- A coded ordinary germ is a halfspace, an orthogonal quadrant, or the
union of two orthogonal halfspaces. The code is precisely SectorLabel's code. -/
inductive OrdinaryCone : Set E3 → Fin 3 → Prop where
  | half (i : Fin 3) (s : ℝ) (hs : s=1 ∨ s= -1) :
      OrdinaryCone {w | s*w i≤0} 1
  | right (i j : Fin 3) (hij : i≠j) (si sj : ℝ)
      (hsi : si=1 ∨ si= -1) (hsj : sj=1 ∨ sj= -1) :
      OrdinaryCone {w | si*w i≤0 ∧ sj*w j≤0} 0
  | reentrant (i j : Fin 3) (hij : i≠j) (si sj : ℝ)
      (hsi : si=1 ∨ si= -1) (hsj : sj=1 ∨ sj= -1) :
      OrdinaryCone {w | si*w i≤0 ∨ sj*w j≤0} 2

theorem ordinary_meridian {C : Set E3} {code : Fin 3} (h : OrdinaryCone C code) :
    Nonempty (AngularMeridian C (((code.val+1:Nat):ℝ)*Real.pi/2)) := by
  cases h with
  | half i s hs =>
      let j : Fin 3 := ⟨(i.val+1)%3,Nat.mod_lt _ (by norm_num)⟩
      have hij : i≠j := by fin_cases i <;> norm_num [j]
      let E := coordinateAxes i j hij s 1 hs (Or.inl rfl)
      let B := turn (-Real.pi/2)*baseAxes
      have he : {w:E3 | s*w i≤0}=E '' {w:E3 | w 0≤0} := by
        apply set_image_of_test
        intro w; simp [E,coordinateAxes_i]
        rcases hs with rfl|rfl <;> simp
      have h0 : {w:E3 | w 0≤0}=B '' halfDown := by
        apply set_image_of_test
        intro w
        have hangle : -Real.pi/2 = -(Real.pi/2) := by ring
        -- [compile-fix: multiplication application is reduced definitionally]
        simp [B,baseAxes_apply,halfDown,turn_apply,pt,hangle,
          Real.cos_neg,Real.sin_neg,Real.cos_pi_div_two,Real.sin_pi_div_two]
      rw [he,h0]
      refine ⟨?_⟩ -- [compile-fix: expose the Nonempty witness]
      convert (halfDown_meridian.map B).map E using 1 <;> norm_num
  | right i j hij si sj hsi hsj =>
      let E := coordinateAxes i j hij si sj hsi hsj
      have he : {w:E3 | si*w i≤0 ∧ sj*w j≤0}=E '' rightDown := by
        apply set_image_of_test
        intro w
        simp [E,rightDown,coordinateAxes_i,coordinateAxes_j]
        rcases hsi with rfl|rfl <;> rcases hsj with rfl|rfl <;> simp
      rw [he]
      refine ⟨?_⟩ -- [compile-fix: expose the Nonempty witness]
      convert rightDown_meridian.map E using 1 <;> norm_num
  | reentrant i j hij si sj hsi hsj =>
      let E := coordinateAxes i j hij si sj hsi hsj
      have he : {w:E3 | si*w i≤0 ∨ sj*w j≤0}=E '' reentrantDown := by
        apply set_image_of_test
        intro w
        simp [E,reentrantDown,coordinateAxes_i,coordinateAxes_j]
        rcases hsi with rfl|rfl <;> rcases hsj with rfl|rfl <;> simp
      rw [he]
      refine ⟨?_⟩ -- [compile-fix: expose the Nonempty witness]
      convert reentrantDown_meridian.map E using 1 <;> norm_num

/-- A sloped facet is still a halfspace, at its actual Euclidean angle. -/
theorem sloped_facet_meridian (q : ℝ) :
    Nonempty (AngularMeridian {w:E3 | w 2≤q*w 0} Real.pi) := by
  let E := baseAxes*turn (Real.arctan q)*baseAxes
  have hc : 0<Real.cos (Real.arctan q) := by rw [Real.cos_arctan]; positivity
  have hs : Real.sin (Real.arctan q)=q*Real.cos (Real.arctan q) := by
    rw [Real.sin_arctan,Real.cos_arctan]; ring
  have he : {w:E3 | w 2≤q*w 0}=E '' halfDown := by
    apply set_image_of_test
    intro w
    -- [compile-fix: multiplication application is reduced definitionally]
    simp [E,baseAxes_apply,turn_apply,halfDown,Set.mem_setOf_eq,pt]
      -- [compile-fix: reduce isometry composition]
    rw [hs]
    have hpos : 0<(1+q^2)*Real.cos (Real.arctan q) := by positivity
    have hid : (q*Real.cos (Real.arctan q)*w 0+Real.cos (Real.arctan q)*w 2)-
        q*(Real.cos (Real.arctan q)*w 0-q*Real.cos (Real.arctan q)*w 2)=
        ((1+q^2)*Real.cos (Real.arctan q))*w 2 := by ring
    rw [←sub_nonpos,hid,mul_nonpos_iff]
    simp [hpos.le, not_le_of_gt hpos] -- [compile-fix: current order API]
  rw [he]
  exact ⟨halfDown_meridian.map E⟩

end
end R44.DischargeOrdinary
