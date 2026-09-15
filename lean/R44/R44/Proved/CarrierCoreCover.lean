/- -- [compile-fix]
# A coarse carrier covering excludes additional physical tiles

Written sources: A-L5.1 and A-L6.2 in proof/ALIGNMENT_PROOF.md; ERRATA E6.
EXPLICIT ALTERNATIVE ARGUMENT FOR A-L6.2: rather than gluing the infinite
family of tube maps, use retained cores. Every point of P is within 1/10 of
an interior point of Q, whereas Q contains an open ball of radius 1/4. A
family of physical copies already belonging to a packing and whose carriers
cover space therefore leaves no room for an additional copy of Q. Since the
ambient family is a TILING, all physical points are consequently covered by
that same subfamily. Packing alone would not give the final coverage; the
argument uses the supplied tiling at exactly that last step.

Neither the mesh bridge nor generic-companion stratification is imported.
No statement, solid, or scale parameter has changed. No admissions.
-/
import R44.Proved.NativeGeometry -- [compile-fix]
import R44.GlobalPredicates -- [compile-fix]

namespace R44.DischargeCoreCover
open Set Generated DischargeGeometry
noncomputable section
set_option maxHeartbeats 0

def core (a : V3) : Set E3 :=
  {x | ∀ i : Fin 3, (a.get i : ℝ)+eta < x i ∧ x i < (a.get i : ℝ)+1-eta}

theorem core_open (a : V3) : IsOpen (core a) := by
  have he : core a = ⋂ i : Fin 3,
      {x : E3 | (a.get i : ℝ)+eta < x i ∧ x i < (a.get i : ℝ)+1-eta} := by
    ext x; simp [core]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  have hc : Continuous (fun x : E3 => x i) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i
  exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)

theorem core_avoids {a : V3} {x : E3} (hx : x ∈ core a) :
    ∀ r : Role, ¬ featureTubeSupport r x := by
  intro r hr
  obtain ⟨i,k,_hi,hk⟩ := normal_plane_integer r
  have hn := featureTubeSupport_coordinate_bound hr i
  rw [hk] at hn
  obtain ⟨hlo,hup⟩ := hx i
  by_cases hka : k ≤ a.get i
  · have hc : (k : ℝ) ≤ (a.get i : ℝ) := by exact_mod_cast hka
    have hp := (abs_le.mp hn).2
    linarith
  · have hak : a.get i + 1 ≤ k := by omega
    have hc : (a.get i : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast hak
    have hp := (abs_le.mp hn).1
    linarith

theorem core_subset_Q {a : V3} (ha : a ∈ chairCells) :
    core a ⊆ interior Q := by
  apply interior_maximal -- [compile-fix]
  · intro x hx
    apply (mem_Q_iff_outside (core_avoids hx)).mpr
    refine ⟨a,ha,?_⟩
    intro i
    have h := hx i
    have he : 0 < eta := by norm_num [eta]
    constructor <;> linarith
  · exact core_open a

private theorem dist_sq (x y : E3) :
    dist x y ^ 2 = (x 0-y 0)^2+(x 1-y 1)^2+(x 2-y 2)^2 := by
  simp [dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_succ,
    Real.norm_eq_abs,sq_abs,add_assoc]

/-- A coordinatewise clamped point lies strictly in a retained core. -/
def corePoint (a : V3) (x : E3) : E3 :=
  WithLp.toLp 2 fun i : Fin 3 =>
    max ((a.get i : ℝ)+1/50) (min (x i) ((a.get i : ℝ)+49/50))

private theorem clamp_bounds (a x : ℝ) (hx : a ≤ x ∧ x ≤ a+1) :
    a+1/50 ≤ max (a+1/50) (min x (a+49/50)) ∧
    max (a+1/50) (min x (a+49/50)) ≤ a+49/50 ∧
    |max (a+1/50) (min x (a+49/50))-x| ≤ 1/50 := by
  constructor
  · exact le_max_left _ _
  constructor
  · exact max_le (by linarith) (min_le_right _ _)
  · rw [abs_le]
    constructor
    · have hmin : x-1/50 ≤ min x (a+49/50) :=
        le_min (by linarith) (by linarith)
      have hm := hmin.trans (le_max_right (a+1/50) (min x (a+49/50)))
      linarith
    · have hm : max (a+1/50) (min x (a+49/50)) ≤ x+1/50 := by
        apply max_le
        · linarith
        · exact (min_le_left _ _).trans (by linarith)
      linarith

/-- Uniform interior-core approximation; no grid registration is assumed. -/
theorem near_core {x : E3} (hx : x ∈ P) :
    ∃ y ∈ interior Q, dist x y < (1/10 : ℝ) := by
  obtain ⟨a,ha,hx⟩ := hx
  let y := corePoint a x
  have hb (i : Fin 3) := clamp_bounds (a.get i : ℝ) (x i) (hx i)
  have hy : y ∈ core a := by
    intro i
    have hlo := (hb i).1 -- [compile-fix begin: name the two clamp bounds before unfolding the coordinate]
    have hup := (hb i).2.1
    change (a.get i : ℝ)+eta < corePoint a x i ∧
      corePoint a x i < (a.get i : ℝ)+1-eta
    dsimp [corePoint] -- [compile-fix]
    constructor -- [compile-fix]
    · have hgap : (a.get i:ℝ)+eta < (a.get i:ℝ)+1/50 := by
        norm_num [eta]
      exact hgap.trans_le hlo
    · have hgap : (a.get i:ℝ)+49/50 < (a.get i:ℝ)+1-eta := by
        norm_num [eta]
        linarith -- [compile-fix]
      exact hup.trans_lt hgap -- [compile-fix end]
  refine ⟨y,core_subset_Q ha hy,?_⟩
  have hs (i : Fin 3) : (x i-y i)^2 ≤ (1/50 : ℝ)^2 := by
    have h := (hb i).2.2
    change |y i-x i| ≤ (1/50 : ℝ) at h
    have hlo := (abs_le.mp h).1
    have hup := (abs_le.mp h).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ y i-x i+1/50)
      (by linarith : 0 ≤ 1/50-(y i-x i))]
  have hd := dist_sq x y
  nlinarith [hs 0,hs 1,hs 2,dist_nonneg (x:=x) (y:=y)]

def ballCenter : E3 := cellCenter (v 0 0 0)

/-- An explicit inscribed ball used to rule out an extra component. -/
theorem ball_interior : Metric.ball ballCenter (1/4 : ℝ) ⊆ interior Q := by
  intro x hx
  apply core_subset_Q (a:=v 0 0 0) (by -- [compile-fix begin: use the head-membership proof without a LawfulBEq instance]
    rw [chairCells]
    exact List.mem_cons_self
    ) -- [compile-fix end]
  have hd : dist x ballCenter < (1/4 : ℝ) := Metric.mem_ball.mp hx
  have hs := dist_sq x ballCenter
  have hcoord (i : Fin 3) : |x i-(1/2 : ℝ)| < 1/4 := by
    have hsq : (x i-(1/2 : ℝ))^2 ≤ dist x ballCenter ^ 2 := by
      fin_cases i <;>
        simp [ballCenter,cellCenter,scaledV3,cellCorner,V3.get,v] at hs ⊢ <;>
        nlinarith [sq_nonneg (x 0-1/2),sq_nonneg (x 1-1/2),sq_nonneg (x 2-1/2)]
    rw [abs_lt]
    constructor <;> nlinarith [dist_nonneg (x:=x) (y:=ballCenter)]
  intro i -- [compile-fix begin: eliminate the finite coordinate before normalizing V3.get]
  have hc := abs_lt.mp (hcoord i)
  fin_cases i <;> norm_num [eta,V3.get,v] at hc ⊢ <;>
    constructor <;> linarith -- [compile-fix end]

/-- General geometric principle specialized only in its two proved numerical
constants: a carrier-covering subfamily of a Q tiling is the entire family. -/
theorem carrier_cover_forces_all_members
    (T : Tiling Q) (B : Set RigidMotion) (hB : B ⊆ T.placements)
    (hcover : ∀ x : E3, ∃ h ∈ B, x ∈ h '' P) :
    T.placements ⊆ B := by
  intro k hk
  obtain ⟨h,hh,u,hu,heq⟩ := hcover (k ballCenter)
  obtain ⟨v,hv,hd⟩ := near_core hu
  have hiH : h v ∈ interior (h '' Q) := by -- [compile-fix begin: normalize the affine-isometry coercion before image_interior]
    rw [← AffineIsometryEquiv.coe_toHomeomorph h]
    rw [←h.toHomeomorph.image_interior]
    exact ⟨v,hv,rfl⟩ -- [compile-fix end]
  have hd' : dist (h v) (k ballCenter) < (1/4 : ℝ) := by
    rw [←heq,h.isometry.dist_eq,dist_comm]
    exact hd.trans (by norm_num)
  have hiK : h v ∈ interior (k '' Q) := by -- [compile-fix begin: normalize the affine-isometry coercion before image_interior]
    rw [← AffineIsometryEquiv.coe_toHomeomorph k]
    rw [←k.toHomeomorph.image_interior]
    refine ⟨k.symm (h v),ball_interior ?_,k.apply_symm_apply _⟩
    rw [Metric.mem_ball]
    rw [← k.isometry.dist_eq (k.symm (h v)) ballCenter, k.apply_symm_apply]
    exact hd' -- [compile-fix end]
  by_cases hkh : k=h
  · simpa [hkh] using hh
  · exact False.elim (Set.disjoint_left.mp
      (T.disjoint_interiors hk (hB hh) hkh) hiK hiH)

end
end R44.DischargeCoreCover
