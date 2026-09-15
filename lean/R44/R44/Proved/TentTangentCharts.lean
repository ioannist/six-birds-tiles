/- -- [compile-fix: promoted to Proved after exchange 7]
# Actual radial tangent sets at open tent base/ridge points

Written source: proof/ALIGNMENT_PROOF.md A§1, A-L2.2 and A-L3.1.
These are set-germ proofs for the signed square tent, including negative
heights and the flat continuation beyond a base edge. They do NOT assign a
solid-angle number by definition. The separate wedge-volume interpretation
and all-mesh-edge interpretation remain recorded in MeshSemantics.
No mathematical admissions.
-/
import R44.Proved.PolyhedralGerms -- [compile-fix]
import R44.Proved.PyramidGeometry -- [compile-fix]

namespace R44.DischargeTentCones
open Set Filter R44.DischargePolyhedral R44.DischargePyramid
open scoped Topology
noncomputable section

/-- The actual signed tent, not its derivative. -/
def tent (a : ℝ) (w : E3) : ℝ :=
  a*max 0 (1-max |w 0| |w 1|/eta)
def H (a : ℝ) : Set E3 := {w | w 2≤tent a w}

/-- Along the left base edge the inward planar coordinate is coordinate 0. -/
def baseCone (a : ℝ) : Set E3 :=
  {d | d 2≤(a/eta)*max 0 (d 0)}

/-- On a ridge its two active planar faces are determined by sx,sy=±1. -/
def ridgeCone (a sx sy : ℝ) : Set E3 :=
  {d | d 2≤-(a/eta)*max (sx*d 0) (sy*d 1)}

private theorem base_homogeneous (a : ℝ) :
    ∀t:ℝ,0<t→∀d:E3,t • d∈baseCone a ↔ d∈baseCone a := by
  intro t ht d
  change t*d 2≤(a/eta)*max 0 (t*d 0) ↔ _
  rw [show max 0 (t*d 0)=t*max 0 (d 0) by
    rw [mul_max_of_nonneg _ _ ht.le]; simp]
    -- API?: mul_max_of_nonneg distributes positive multiplication over max.
  have he : (a/eta)*(t*max 0 (d 0))=t*((a/eta)*max 0 (d 0)) := by ring
  rw [he]
  change t*d 2≤t*((a/eta)*max 0 (d 0)) ↔ d 2≤(a/eta)*max 0 (d 0)
  constructor <;> intro h <;> nlinarith

private theorem ridge_homogeneous (a sx sy : ℝ) :
    ∀t:ℝ,0<t→∀d:E3,t • d∈ridgeCone a sx sy ↔ d∈ridgeCone a sx sy := by
  intro t ht d
  change t*d 2≤-(a/eta)*max (sx*(t*d 0)) (sy*(t*d 1)) ↔ _
  rw [show max (sx*(t*d 0)) (sy*(t*d 1))=
      t*max (sx*d 0) (sy*d 1) by
    rw [mul_max_of_nonneg _ _ ht.le]; congr 1 <;> ring]
  have he : -(a/eta)*(t*max (sx*d 0) (sy*d 1))=
      t*(-(a/eta)*max (sx*d 0) (sy*d 1)) := by ring
  rw [he]
  change t*d 2≤t*(-(a/eta)*max (sx*d 0) (sy*d 1)) ↔
    d 2≤-(a/eta)*max (sx*d 0) (sy*d 1)
  constructor <;> intro h <;> nlinarith

/-- A complete ambient germ at any OPEN left base-edge point. The signed
height may have either sign. The crossing from tent to flat is retained. -/
theorem base_germ (a b : ℝ) (hb : |b|<eta) :
    ∀ᶠ d in 𝓝 (0:E3),pt (-eta) b 0+d∈H a ↔ d∈baseCone a := by
  let x := pt (-eta) b 0
  have h0 : ∀ᶠ d in 𝓝 (0:E3),x 0+d 0<0 := by
    have hc : Continuous (fun d:E3 => x 0+d 0) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simp [x,pt,eta]))
    -- API?: ContinuousAt.eventually applied to the open interval (-∞,0).
  have hdom : ∀ᶠ d in 𝓝 (0:E3), |x 1+d 1| < -(x 0+d 0) := by -- [compile-fix begin: disambiguate abs and unary negation]
    have ho : IsOpen {d:E3 | |x 1+d 1| < -(x 0+d 0)} := by
      apply isOpen_lt <;> fun_prop
    exact ho.mem_nhds (by simpa [x,pt] using hb)
    -- [compile-fix end]
  filter_upwards [h0,hdom] with d hd0 hdd
  have hrad : max |x 0+d 0| |x 1+d 1|=eta-d 0 := by
    rw [abs_of_neg hd0,max_eq_left hdd.le]
    simp [x,pt]; ring
  have hmax : max 0 (1-(eta-d 0)/eta)=(1/eta)*max 0 (d 0) := by
    have he : 1-(eta-d 0)/eta=(1/eta)*d 0 := by norm_num [eta]; ring
    rw [he,mul_max_of_nonneg _ _ (by norm_num [eta] : (0:ℝ)≤1/eta)]
    simp
  change x 2+d 2≤a*max 0 (1-max |x 0+d 0| |x 1+d 1|/eta) ↔ _
  rw [hrad,hmax]
  simp [x,pt] -- [compile-fix]
  change d 2 ≤ a * (eta⁻¹ * max 0 (d 0)) ↔ d 2 ≤ (a / eta) * max 0 (d 0) -- [compile-fix]
  congr 1; ring

theorem tangent_at_base (a b : ℝ) (hb : |b|<eta) :
    tangentCone (H a) (pt (-eta) b 0)=baseCone a :=
  LocalCone.tangent_eq (base_homogeneous a) (base_germ a b hb)

/-- Every open ridge point has the stated max-of-two-linear-forms germ.
This treats positive and negative pyramids without reversing an inequality
by an unproved sign convention. -/
theorem ridge_germ (a sx sy b : ℝ)
    (hsx : sx=1 ∨ sx=-1) (hsy : sy=1 ∨ sy=-1)
    (hb0 : 0<b) (hb1 : b<eta) :
    ∀ᶠ d in 𝓝 (0:E3),
      pt (sx*b) (sy*b) (a*(1-b/eta))+d∈H a ↔ d∈ridgeCone a sx sy := by
  let x := pt (sx*b) (sy*b) (a*(1-b/eta))
  have hx0 : sx*x 0=b := by rcases hsx with rfl|rfl <;> simp [x,pt]
  have hx1 : sy*x 1=b := by rcases hsy with rfl|rfl <;> simp [x,pt]
  have hxx : |x 0|=b := by rcases hsx with rfl|rfl <;> simp [x,pt,hb0.le]
  have hyy : |x 1|=b := by rcases hsy with rfl|rfl <;> simp [x,pt,hb0.le]
  have ho : IsOpen {d:E3 |
      0<sx*(x 0+d 0) ∧ 0<sy*(x 1+d 1) ∧
        max |x 0+d 0| |x 1+d 1|<eta} := by
    have hsxC : Continuous (fun d:E3 => sx*(x 0+d 0)) := by fun_prop -- [compile-fix begin: supply ordered continuous sides]
    have hsyC : Continuous (fun d:E3 => sy*(x 1+d 1)) := by fun_prop
    have hradC : Continuous (fun d:E3 => max |x 0+d 0| |x 1+d 1|) := by fun_prop
    have hzeroC : Continuous (fun _d:E3 => (0:Real)) := continuous_const
    have hetaC : Continuous (fun _d:E3 => eta) := continuous_const
    exact (isOpen_lt hzeroC hsxC).inter
      ((isOpen_lt hzeroC hsyC).inter (isOpen_lt hradC hetaC))
    -- [compile-fix end]
  have hn : {d:E3 | 0<sx*(x 0+d 0) ∧ 0<sy*(x 1+d 1) ∧
      max |x 0+d 0| |x 1+d 1|<eta}∈𝓝 (0:E3) := by
    apply ho.mem_nhds
    simpa [hx0,hx1,hxx,hyy] using And.intro hb0 (And.intro hb0 hb1)
  filter_upwards [hn] with d hd
  have habsx : |x 0+d 0|=b+sx*d 0 := by
    rcases hsx with rfl|rfl
    · rw [abs_of_pos (by simpa using hd.1)]
      simpa [x,pt] using (show b+d 0=b+d 0 from rfl)
    · have hh : x 0+d 0<0 := by nlinarith [hd.1]
      rw [abs_of_neg hh]
      simp [x,pt]; ring
  have habsy : |x 1+d 1|=b+sy*d 1 := by
    rcases hsy with rfl|rfl
    · rw [abs_of_pos (by simpa using hd.2.1)]
      simp [x,pt]
    · have hh : x 1+d 1<0 := by nlinarith [hd.2.1]
      rw [abs_of_neg hh]
      simp [x,pt]; ring
  have hrad : max |x 0+d 0| |x 1+d 1|=b+max (sx*d 0) (sy*d 1) := by
    rw [habsx,habsy,max_add_add_left]
    -- API?: max_add_add_left: max (b+p) (b+q)=b+max p q.
  have hpos : 0<1-max |x 0+d 0| |x 1+d 1|/eta := by
    have hη : (0:ℝ)<eta := by norm_num [eta]
    exact sub_pos.mpr ((div_lt_one hη).mpr hd.2.2)
  change x 2+d 2≤a*max 0 (1-max |x 0+d 0| |x 1+d 1|/eta) ↔ _
  rw [max_eq_right hpos.le,hrad]
  simp only [x,pt,Matrix.cons_val_two] -- [compile-fix]
  change a*(1-b/eta)+d 2≤a*(1-(b+max (sx*d 0) (sy*d 1))/eta) ↔
    d 2≤-(a/eta)*max (sx*d 0) (sy*d 1)
  norm_num only [eta]
  constructor <;> intro h <;> nlinarith [h]

theorem tangent_at_ridge (a sx sy b : ℝ)
    (hsx : sx=1 ∨ sx=-1) (hsy : sy=1 ∨ sy=-1)
    (hb0 : 0<b) (hb1 : b<eta) :
    tangentCone (H a) (pt (sx*b) (sy*b) (a*(1-b/eta)))=
      ridgeCone a sx sy :=
  LocalCone.tangent_eq (ridge_homogeneous a sx sy)
    (ridge_germ a sx sy b hsx hsy hb0 hb1)

/-- The sign distinction explains the convex/reentrant ridge polarity. -/
theorem ridge_positive (a sx sy : ℝ) (ha : 0≤a) :
    ridgeCone a sx sy =
      {d:E3 | d 2≤-(a/eta)*(sx*d 0)} ∩
      {d:E3 | d 2≤-(a/eta)*(sy*d 1)} := by
  ext d
  change d 2≤-(a/eta)*max (sx*d 0) (sy*d 1) ↔ -- [compile-fix begin: prove the nonpositive max law directly]
    d 2≤-(a/eta)*(sx*d 0) ∧ d 2≤-(a/eta)*(sy*d 1)
  have heta : 0<eta := by norm_num [eta]
  have hc : -(a/eta)≤0 := neg_nonpos.mpr (div_nonneg ha heta.le)
  by_cases hxy : sx*d 0 ≤ sy*d 1
  · rw [max_eq_right hxy]
    constructor
    · intro h
      exact ⟨h.trans (mul_le_mul_of_nonpos_left hxy hc),h⟩
    · exact fun h => h.2
  · have hyx : sy*d 1 ≤ sx*d 0 := le_of_not_ge hxy
    rw [max_eq_left hyx]
    constructor
    · intro h
      exact ⟨h,h.trans (mul_le_mul_of_nonpos_left hyx hc)⟩
    · exact fun h => h.1
  -- [compile-fix end]

theorem ridge_negative (a sx sy : ℝ) (ha : a≤0) :
    ridgeCone a sx sy =
      {d:E3 | d 2≤-(a/eta)*(sx*d 0)} ∪
      {d:E3 | d 2≤-(a/eta)*(sy*d 1)} := by
  ext d
  change d 2≤-(a/eta)*max (sx*d 0) (sy*d 1) ↔ -- [compile-fix begin: expose union membership]
    d 2≤-(a/eta)*(sx*d 0) ∨ d 2≤-(a/eta)*(sy*d 1)
  have hc : 0≤-(a/eta) := neg_nonneg.mpr
    (div_nonpos_of_nonpos_of_nonneg ha (by norm_num [eta]))
  rw [mul_max_of_nonneg _ _ hc,le_max_iff]
  -- [compile-fix end]

end
end R44.DischargeTentCones
