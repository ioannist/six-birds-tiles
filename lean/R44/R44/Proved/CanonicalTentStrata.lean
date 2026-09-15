/- -- [compile-fix: promoted to Proved after exchange 7]
# Every canonical signed-tent boundary point is classified

A-L2.2/A-L3.1. At a nonvertex point the boundary is either a named base
edge, a named ridge, or a locally affine facet. This is a continuous
classification of the tent graph, not a classification of sampled points.
The two strict max branches give the affine germs; the ties give the ridge
segments; radius eta gives the four base segments. No admissions.
-/
import R44.Proved.NativeBoundaryLocal -- [compile-fix: promoted after exchange 7]

namespace R44.DischargeTentStrata
open Set Filter DischargePyramid DischargeTentCones DischargeAngular
open DischargeMeridian DischargeOrdinary DischargePolyhedral
open DischargeMeridianFrames
open scoped Topology
noncomputable section
set_option maxHeartbeats 0

def openBases : Set E3 := ⋃k:Fin 4,openSegment ℝ (B k) (B (nextCorner k))
def openRidges (a : ℝ) : Set E3 := ⋃k:Fin 4,openSegment ℝ (B k) (A a)
def flatCone (q : ℝ) (i : Fin 2) : Set E3 := {d | d 2≤q*d i.castSucc}

private def xySwapLinear : E3 →ₗ[ℝ] E3 where
  toFun := fun w => pt (w 1) (w 0) (w 2)
  map_add' := by intros; ext i; fin_cases i <;> simp [pt]
  map_smul' := by intros; ext i; fin_cases i <;> simp [pt]

def xySwap : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.ofSurjective
    ({toLinearMap := xySwapLinear
      norm_map' := by
        intro w
        have he : ‖xySwapLinear w‖^2=‖w‖^2 := by
          simp [DischargePyramid.norm_sq,xySwapLinear,pt]; ring
        nlinarith [norm_nonneg (xySwapLinear w),norm_nonneg w]} : E3 →ₗᵢ[ℝ] E3)
    (by intro w; refine ⟨pt (w 1) (w 0) (w 2),?_⟩; ext i; fin_cases i <;> rfl)

@[simp] theorem xySwap_apply (w : E3) : xySwap w=pt (w 1) (w 0) (w 2) := rfl

theorem flatCone_meridian (q : ℝ) (i : Fin 2) :
    Nonempty (AngularMeridian (flatCone q i) Real.pi) := by
  fin_cases i
  · -- [compile-fix: remove the finite-case identity wrapper]
    change Nonempty (AngularMeridian (flatCone q (0 : Fin 2)) Real.pi)
    exact sloped_facet_meridian q
  · obtain ⟨m⟩ := sloped_facet_meridian q
    have he : flatCone q 1=xySwap '' {w:E3 | w 2≤q*w 0} := by
      apply set_image_of_test
      intro w; simp [flatCone,xySwap_apply,pt]
    -- [compile-fix: normalize the finite-case index before rewriting]
    change Nonempty (AngularMeridian (flatCone q (1:Fin 2)) Real.pi)
    rw [he]
    exact ⟨m.map xySwap⟩

private def other (i : Fin 2) : Fin 3 := if i=0 then 1 else 0

/-- The actual affine face germ, with signed slope and a strict dominant
coordinate. The amplitude a can be positive, negative or zero. -/
theorem flat_tangent (a : ℝ) (y : E3) (i : Fin 2) (s : ℝ)
    (hs : s=1 ∨ s= -1) (hpos : 0<s*y i.castSucc)
    (hdom : |y (other i)|<s*y i.castSucc) (hin : s*y i.castSucc<eta)
    (hz : y 2=tent a y) :
    tangentCone (H a) y=flatCone (-(a/eta)*s) i := by
  have habs : |y i.castSucc|=s*y i.castSucc := by
    rcases hs with rfl|rfl
    · -- [compile-fix: normalize multiplication by one]
      simpa only [one_mul] using (abs_of_pos (by simpa only [one_mul] using hpos))
    · have hh : y i.castSucc<0 := by linarith
      simpa using abs_of_neg hh
  have hrad : max |y 0| |y 1|=s*y i.castSucc := by
    fin_cases i
    · -- [compile-fix: remove the finite-case identity wrapper]
      change |y 0| = s * y 0 at habs
      change |y 1| < s * y 0 at hdom
      change max |y 0| |y 1| = s * y 0
      rw [habs,max_eq_left hdom.le]
    · -- [compile-fix: remove the finite-case identity wrapper]
      change |y 1| = s * y 1 at habs
      change |y 0| < s * y 1 at hdom
      change max |y 0| |y 1| = s * y 1
      rw [habs,max_eq_right hdom.le]
  have hyz : y 2=a*(1-(s*y i.castSucc)/eta) := by
    rw [hz,tent,hrad,max_eq_right]
    exact (sub_nonneg.mpr ((div_le_one (by norm_num [eta] : 0<eta)).mpr hin.le))
  have hO : IsOpen {d:E3 | 0<s*(y i.castSucc+d i.castSucc) ∧
      |y (other i)+d (other i)|<s*(y i.castSucc+d i.castSucc) ∧
      s*(y i.castSucc+d i.castSucc)<eta} := by
    -- [compile-fix: expose the conjunction as nested intersections]
    change IsOpen ({d:E3 | 0<s*(y i.castSucc+d i.castSucc)} ∩
      ({d:E3 | |y (other i)+d (other i)|<s*(y i.castSucc+d i.castSucc)} ∩
       {d:E3 | s*(y i.castSucc+d i.castSucc)<eta}))
    exact (isOpen_lt (by fun_prop) (by fun_prop)).inter
      ((isOpen_lt (by fun_prop) (by fun_prop)).inter
        (isOpen_lt (by fun_prop) (by fun_prop)))
  have hn : {d:E3 | 0<s*(y i.castSucc+d i.castSucc) ∧
      |y (other i)+d (other i)|<s*(y i.castSucc+d i.castSucc) ∧
      s*(y i.castSucc+d i.castSucc)<eta}∈𝓝 (0:E3) :=
    hO.mem_nhds (by simpa using And.intro hpos (And.intro hdom hin))
  apply LocalCone.tangent_eq
  · intro t ht d
    change t*d 2≤(-(a/eta)*s)*(t*d i.castSucc) ↔ _
    rw [show (-(a/eta)*s)*(t*d i.castSucc)=t*((-(a/eta)*s)*d i.castSucc) by ring]
    -- [compile-fix: discharge positive-factor cancellation explicitly]
    constructor
    · intro hh
      exact le_of_mul_le_mul_left hh ht
    · intro hh
      change d 2 ≤ (-(a / eta) * s) * d i.castSucc at hh
      exact mul_le_mul_of_nonneg_left hh ht.le
    -- API?: cancellation equivalence (t*a <= t*b) iff (a<=b), t>0.
  · filter_upwards [hn] with d hd
    have ha : |y i.castSucc+d i.castSucc|=s*(y i.castSucc+d i.castSucc) := by
      rcases hs with rfl|rfl
      · -- [compile-fix: normalize multiplication by one]
        simpa only [one_mul] using (abs_of_pos (by simpa only [one_mul] using hd.1))
      · rw [abs_of_neg (by linarith [hd.1])]; ring
    have hr : max |y 0+d 0| |y 1+d 1|=s*(y i.castSucc+d i.castSucc) := by
      fin_cases i
      · -- [compile-fix: remove the finite-case identity wrapper]
        change |y 0 + d 0| = s * (y 0 + d 0) at ha
        have hother : |y 1 + d 1| < s * (y 0 + d 0) := by
          -- [compile-fix: unfold the dependent finite-case identity]
          simpa [other] using hd.2.1
        change max |y 0 + d 0| |y 1 + d 1| = s * (y 0 + d 0)
        rw [ha,max_eq_left hother.le]
      · -- [compile-fix: remove the finite-case identity wrapper]
        change |y 1 + d 1| = s * (y 1 + d 1) at ha
        have hother : |y 0 + d 0| < s * (y 1 + d 1) := by
          -- [compile-fix: unfold the dependent finite-case identity]
          simpa [other] using hd.2.1
        change max |y 0 + d 0| |y 1 + d 1| = s * (y 1 + d 1)
        rw [ha,max_eq_right hother.le]
    change y 2+d 2≤a*max 0 (1-max |y 0+d 0| |y 1+d 1|/eta) ↔ _
    rw [hr,max_eq_right (by
      have hh := (div_le_one (show 0<eta by norm_num [eta])).mpr hd.2.2.le
      linarith),hyz]
    change a*(1-(s*y i.castSucc)/eta)+d 2≤
      a*(1-(s*(y i.castSucc+d i.castSucc))/eta) ↔ d 2≤-(a/eta)*s*d i.castSucc
    have he : a*(1-(s*(y i.castSucc+d i.castSucc))/eta)-
        a*(1-(s*y i.castSucc)/eta)=-(a/eta)*s*d i.castSucc := by ring
    constructor <;> intro hh <;> linarith

private def basePoint (k : Fin 4) (b : ℝ) : E3 :=
  match k.val with
  | 0 => pt (-eta) b 0
  | 1 => pt b eta 0
  | 2 => pt eta (-b) 0
  | _ => pt (-b) (-eta) 0

private theorem basePoint_mem (k : Fin 4) (b : ℝ) (hb : |b|≤eta) :
    basePoint k b∈segment ℝ (B k) (B (nextCorner k)) := by
  have hb' := abs_le.mp hb
  refine ⟨(eta-b)/(2*eta),(eta+b)/(2*eta),
    div_nonneg (by linarith [hb'.2]) (by norm_num [eta]),
    div_nonneg (by linarith [hb'.1]) (by norm_num [eta]),?_,?_⟩
  · norm_num [eta]; ring
  · ext i; fin_cases i <;> fin_cases k <;>
      norm_num [basePoint,B,nextCorner,pt,eta] <;> ring

private theorem square_perimeter (u v : ℝ) (hu : |u|≤eta) (hv : |v|≤eta)
    (he : max |u| |v|=eta) : ∃k:Fin 4,pt u v 0∈segment ℝ (B k) (B (nextCorner k)) := by
  have hcases : |u|=eta ∨ |v|=eta := by
    rcases le_total |u| |v| with h|h
    · right; simpa [max_eq_right h] using he
    · left; simpa [max_eq_left h] using he
  rcases hcases with h|h
  · rcases le_total 0 u with hp|hn
    · have hu' : u=eta := by rwa [abs_of_nonneg hp] at h
      refine ⟨2,?_⟩
      simpa [basePoint,hu'] using basePoint_mem 2 (-v) (by simpa using hv)
    · have hu' : u= -eta := by rw [abs_of_nonpos hn] at h; linarith
      refine ⟨0,?_⟩
      simpa [basePoint,hu'] using basePoint_mem 0 v hv
  · rcases le_total 0 v with hp|hn
    · have hv' : v=eta := by rwa [abs_of_nonneg hp] at h
      refine ⟨1,?_⟩
      simpa [basePoint,hv'] using basePoint_mem 1 u hu
    · have hv' : v= -eta := by rw [abs_of_nonpos hn] at h; linarith
      refine ⟨3,?_⟩
      simpa [basePoint,hv'] using basePoint_mem 3 (-u) (by simpa using hu)

private theorem ridgePoint_mem (a sx sy b : ℝ)
    (hx : sx=1 ∨ sx= -1) (hy : sy=1 ∨ sy= -1) (hb : 0≤b ∧ b≤eta) :
    ∃k:Fin 4,pt (sx*b) (sy*b) (a*(1-b/eta))∈segment ℝ (B k) (A a) := by
  have hp : 0<eta := by norm_num [eta]
  have hcoeff : 0≤b/eta ∧ 0≤1-b/eta :=
    ⟨div_nonneg hb.1 hp.le,sub_nonneg.mpr ((div_le_one hp).mpr hb.2)⟩
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
  · refine ⟨2,b/eta,1-b/eta,hcoeff.1,hcoeff.2,by ring,?_⟩
    ext i; fin_cases i <;> norm_num [B,A,pt,eta] <;> ring
  · refine ⟨3,b/eta,1-b/eta,hcoeff.1,hcoeff.2,by ring,?_⟩
    ext i; fin_cases i <;> norm_num [B,A,pt,eta] <;> ring
  · refine ⟨1,b/eta,1-b/eta,hcoeff.1,hcoeff.2,by ring,?_⟩
    ext i; fin_cases i <;> norm_num [B,A,pt,eta] <;> ring
  · refine ⟨0,b/eta,1-b/eta,hcoeff.1,hcoeff.2,by ring,?_⟩
    ext i; fin_cases i <;> norm_num [B,A,pt,eta] <;> ring

private theorem segment_end_or_open {u v x : E3} (hx : x∈segment ℝ u v) :
    x=u ∨ x=v ∨ x∈openSegment ℝ u v := by
  rcases hx with ⟨s,t,hs,ht,hst,he⟩
  by_cases hz : s=0
  · have ht' : t=1 := by linarith
    exact Or.inr (Or.inl (by simpa [hz,ht'] using he.symm))
  · by_cases hz' : t=0
    · have hs' : s=1 := by linarith
      exact Or.inl (by simpa [hz',hs'] using he.symm)
    · exact Or.inr (Or.inr ⟨s,t,lt_of_le_of_ne hs (Ne.symm hz),
        lt_of_le_of_ne ht (Ne.symm hz'),hst,he⟩)

/-- Every point in the closed base square on the tent graph is classified.
The only exceptional points are precisely the apex and four base corners. -/
theorem canonical_boundary_cases (a : ℝ) (y : E3)
    (hr : max |y 0| |y 1|≤eta) (hz : y 2=tent a y) :
    (y=A a ∨ ∃k:Fin 4,y=B k) ∨ y∈openBases ∨ y∈openRidges a ∨
      Nonempty (AngularMeridian (tangentCone (H a) y) Real.pi) := by
  have hyrepr : y=pt (y 0) (y 1) (y 2) := by ext i; fin_cases i <;> rfl
  by_cases he : max |y 0| |y 1|=eta
  · have hz0 : y 2=0 := by rw [hz,tent,he]; norm_num [eta]
    obtain ⟨k,hk⟩ := square_perimeter (y 0) (y 1)
      ((le_max_left _ _).trans hr) ((le_max_right _ _).trans hr) he
    have hy : y=pt (y 0) (y 1) 0 := by simpa [hz0] using hyrepr
    rw [←hy] at hk
    rcases segment_end_or_open hk with h|h|h
    · exact Or.inl (Or.inr ⟨k,h⟩)
    · exact Or.inl (Or.inr ⟨nextCorner k,h⟩)
    · exact Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨k,h⟩))
  · have hstrict : max |y 0| |y 1|<eta := lt_of_le_of_ne hr he
    by_cases ht : |y 0|=|y 1|
    · let b := |y 0|
      let sx : ℝ := if 0≤y 0 then 1 else -1
      let sy : ℝ := if 0≤y 1 then 1 else -1
      have hxsg : sx=1 ∨ sx= -1 := by dsimp [sx]; split_ifs <;> simp
      have hysg : sy=1 ∨ sy= -1 := by dsimp [sy]; split_ifs <;> simp
      have hxv : sx*b=y 0 := by
        dsimp [sx,b]; split_ifs with h
        · simp [abs_of_nonneg h]
        · simp [abs_of_neg (lt_of_not_ge h)]
      have hyv : sy*b=y 1 := by
        dsimp [sy,b]; rw [ht]; split_ifs with h
        · simp [abs_of_nonneg h]
        · simp [abs_of_neg (lt_of_not_ge h)]
      have hb : 0≤b ∧ b≤eta := ⟨abs_nonneg _,(le_max_left _ _).trans hr⟩
      have hyz : y 2=a*(1-b/eta) := by
        rw [hz,tent,ht,max_self,max_eq_right]
        · dsimp [b]; rw [ht]
        · have hh := (div_le_one (show 0<eta by norm_num [eta])).mpr
            ((le_max_right _ _).trans hr)
          linarith
      obtain ⟨k,hk⟩ := ridgePoint_mem a sx sy b hxsg hysg hb
      have hyp : y=pt (sx*b) (sy*b) (a*(1-b/eta)) := by
        ext i; fin_cases i <;> simp [pt,hxv,hyv,hyz]
      rw [←hyp] at hk
      rcases segment_end_or_open hk with h|h|h
      · exact Or.inl (Or.inr ⟨k,h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨k,h⟩)))
    · have choose_face (i : Fin 2) (hdom : |y (other i)| < |y i.castSucc|) :
          -- [compile-fix: spaces prevent the absolute-value bars from parsing as application]
          Nonempty (AngularMeridian (tangentCone (H a) y) Real.pi) := by
        let s : ℝ := if 0≤y i.castSucc then 1 else -1
        have hs : s=1 ∨ s= -1 := by dsimp [s]; split_ifs <;> simp
        have ha : |y i.castSucc|=s*y i.castSucc := by
          dsimp [s]; split_ifs with h
          · simp [abs_of_nonneg h]
          · simp [abs_of_neg (lt_of_not_ge h)]
        have hpos : 0<s*y i.castSucc := by rw [←ha]; linarith [abs_nonneg (y (other i))]
        have hin : s*y i.castSucc<eta := by
          rw [←ha]
          fin_cases i
          · exact (le_max_left _ _).trans_lt hstrict
          · exact (le_max_right _ _).trans_lt hstrict
        rw [flat_tangent a y i s hs hpos (by simpa [←ha] using hdom) hin hz]
        exact flatCone_meridian _ i
      apply Or.inr; apply Or.inr; apply Or.inr
      rcases lt_or_gt_of_ne ht with h|h
      · exact choose_face 1 (by simpa [other] using h)
      · exact choose_face 0 (by simpa [other] using h)

end
end R44.DischargeTentStrata
