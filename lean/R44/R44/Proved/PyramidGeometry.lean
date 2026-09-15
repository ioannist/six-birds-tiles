/- -- [compile-fix]
# Intrinsic rigidity of the square-pyramid graph

Written source: A-L4.3, A-C4.4 in proof/ALIGNMENT_PROOF.md; ERRATA E1.
ALTERNATIVE ARGUMENT for the equal-graph step: after polarity fixes the two
heights, normalize to congruent compact graphs and use compact isometric
containment, rather than integrating one-dimensional Hausdorff length.
The rest is the same geometric rigidity: recover the base square and apex.
The center is recovered by its enclosing-ball property, the four corners by
maximum norm, and the apex by equal distance to the four corners. No valence
classification, mesh semantics, or conjectured frame alignment is assumed.
This is the external agent's proof integrated verbatim except for `[compile-fix]` lines. -- [compile-fix]
-/
import R44.Proved.FeatureGraphTopology -- [compile-fix]
import R44.Proved.CompactCongruent -- [compile-fix]

namespace R44.DischargePyramid
open Set R44.Generated R44.DischargeGeometry R44.DischargeCharts
noncomputable section
set_option maxHeartbeats 0

abbrev pt (x y z : ℝ) : E3 := WithLp.toLp 2 ![x,y,z]
def B (k : Fin 4) : E3 :=
  pt ((if k.val=0 ∨ k.val=1 then -1 else 1)*eta)
    ((if k.val=0 ∨ k.val=3 then -1 else 1)*eta) 0
def A (a : ℝ) : E3 := pt 0 0 a
def G (a : ℝ) : Set E3 :=
  (⋃ k : Fin 4,segment ℝ (B k) (B (nextCorner k))) ∪
    ⋃ k : Fin 4,segment ℝ (B k) (A a)
def S (a : ℝ) : Set E3 :=
  ⋃ k : Fin 4,convexHull ℝ ({B k,B (nextCorner k),A a} : Set E3)

theorem norm_sq (w : E3) : ‖w‖^2 = w 0^2+w 1^2+w 2^2 := by
  rw [EuclideanSpace.norm_sq_eq] -- [compile-fix]
  simp [Fin.sum_univ_succ] -- [compile-fix]
  ring -- [compile-fix]
    -- API?: EuclideanSpace.norm_sq_eq is the sum of squared real coordinates.

theorem B_mem (a : ℝ) (k : Fin 4) : B k∈G a :=
  Or.inr (Set.mem_iUnion.mpr ⟨k,left_mem_segment ℝ _ _⟩)
theorem A_mem (a : ℝ) : A a∈G a :=
  Or.inr (Set.mem_iUnion.mpr ⟨0,right_mem_segment ℝ _ _⟩)

theorem graph_compact (a : ℝ) : IsCompact (G a) := by -- [compile-fix]
  have hsegment (u v : E3) : IsCompact (segment ℝ u v) := by -- [compile-fix]
    rw [segment_eq_image] -- [compile-fix]
    exact isCompact_Icc.image (by fun_prop) -- [compile-fix]
  exact (isCompact_iUnion fun k : Fin 4 => hsegment (B k) (B (nextCorner k))).union -- [compile-fix]
    (isCompact_iUnion fun k : Fin 4 => hsegment (B k) (A a)) -- [compile-fix]

/-- The corners, and only the corners, attain the enclosing radius. -/
theorem graph_radius {a : ℝ} (ha : a^2<2*eta^2) {w : E3} (hw : w∈G a) :
    ‖w‖^2≤2*eta^2 ∧ (‖w‖^2=2*eta^2 → ∃k : Fin 4,w=B k) := by
  rcases hw with hw | hw
  · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hw
    rcases hk with ⟨u,v,hu,hv,huv,rfl⟩
    have huv' : u≤1 := by linarith
    have hv' : v≤1 := by linarith
    have huvprod : 0≤u*v := mul_nonneg hu hv
    have hsumSq : (u+v)^2=1 := by rw [huv]; norm_num
    have hn : ‖u • B k+v • B (nextCorner k)‖^2 =
        2*eta^2-4*eta^2*(u*v) := by
      rw [norm_sq]
      fin_cases k <;> simp [B,nextCorner,pt,eta] <;> nlinarith [hsumSq]
    rw [hn]
    refine ⟨by nlinarith [sq_nonneg eta],?_⟩
    intro heq
    have heta : 0 < eta^2 := by norm_num [eta] -- [compile-fix]
    have hz : u*v=0 := by nlinarith [heq] -- [compile-fix]
    rcases mul_eq_zero.mp hz with hz | hz
    · refine ⟨nextCorner k,?_⟩
      have hv1 : v=1 := by linarith
      simp [hz,hv1]
    · refine ⟨k,?_⟩
      have hu1 : u=1 := by linarith
      simp [hz,hu1]
  · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hw
    rcases hk with ⟨u,v,hu,hv,huv,rfl⟩
    have hu1 : u≤1 := by linarith
    have hv1 : v≤1 := by linarith
    have hn : ‖u • B k+v • A a‖^2 = 2*eta^2*u^2+a^2*v^2 := by
      rw [norm_sq]
      fin_cases k <;> simp [B,A,pt] <;> ring
    have hv2 : v^2≤v := by nlinarith
    have hu2 : u^2≤u := by nlinarith
    have hstrict : 0<v → 2*eta^2*u^2+a^2*v^2<2*eta^2 := by
      intro hvpos
      have ha' := mul_lt_mul_of_pos_right ha hvpos
      have hvnonneg : 0≤a^2*v^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have hle := mul_le_mul_of_nonneg_left hv2 (sq_nonneg a)
      have hle' := mul_le_mul_of_nonneg_left hu2 (by positivity : 0≤2*eta^2)
      nlinarith
    rw [hn]
    by_cases hvz : v=0
    · have huz : u=1 := by linarith
      simpa [hvz,huz] -- [compile-fix]
    · have h := hstrict (lt_of_le_of_ne hv (Ne.symm hvz))
      exact ⟨h.le,fun heq => False.elim (h.ne heq)⟩

/-- A point of the edge graph lying on the normal axis is the apex. -/
theorem graph_on_axis {a : ℝ} {w : E3} (hw : w∈G a)
    (h0 : w 0=0) (h1 : w 1=0) : w=A a := by
  rcases hw with hw | hw
  · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hw
    rcases hk with ⟨u,v,hu,hv,huv,rfl⟩
    fin_cases k <;> simp [B,nextCorner,pt,eta] at h0 h1 <;> linarith
  · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hw
    rcases hk with ⟨u,v,hu,hv,huv,rfl⟩
    have huz : u=0 := by
      fin_cases k <;> simp [B,A,pt,eta] at h0 <;> linarith
    have hvone : v=1 := by linarith
    simp [huz,hvone]

/-- The obvious native rigid chart, with translation applied after rotation. -/
def chartPose (r : Role) : RigidMotion :=
  (chartEquiv r).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ E3 (featureCenter r))
    -- API?: constVAdd ℝ E3 c is x↦c+x; .trans applies its RHS second.

@[simp] theorem chartPose_apply (r : Role) (w : E3) :
    chartPose r w = featureCenter r + chartEquiv r w := rfl

@[simp] theorem chartPose_B (r : Role) (k : Fin 4) :
    chartPose r (B k)=featureCorner r k := by
  simp [chartPose_apply,B,chartEquiv_apply,chartLinear_apply,featureCorner,pt] <;> abel -- [compile-fix]

@[simp] theorem chartPose_A (r : Role) :
    chartPose r (A ((profileCoefficient r:ℝ)/10000))=featureApex r := by
  simp [chartPose_apply,A,chartEquiv_apply,chartLinear_apply,featureApex,pt]

theorem chart_graph (r : Role) :
    chartPose r '' G ((profileCoefficient r:ℝ)/10000)=nativeFeatureGraph r := by
  simp only [G,nativeFeatureGraph,nativeFeatureBaseEdges,nativeFeatureRidgeEdges,
    Set.image_union,Set.image_iUnion]
  congr 1 <;> apply congrArg (fun f : Fin 4 → Set E3 => ⋃ k,f k) <;>
    funext k <;>
    change (chartPose r).toAffineMap '' segment ℝ _ _ = _ <;> -- [compile-fix]
    rw [image_segment] -- [compile-fix]
      -- API?: affine image of segment equals segment of images.
  · apply congrArg₂ (segment ℝ) -- [compile-fix]
    · exact chartPose_B r k -- [compile-fix]
    · exact chartPose_B r (nextCorner k) -- [compile-fix]
  · apply congrArg₂ (segment ℝ) -- [compile-fix]
    · exact chartPose_B r k -- [compile-fix]
    · exact chartPose_A r -- [compile-fix]

theorem chart_surface (r : Role) :
    chartPose r '' S ((profileCoefficient r:ℝ)/10000)=nativeFeatureSurface r := by
  simp only [S,Set.image_iUnion,nativeFeatureSurface]
  congr 1; funext k
  change (chartPose r).toAffineMap '' convexHull ℝ _ = _ -- [compile-fix]
  rw [AffineMap.image_convexHull] -- [compile-fix]
    -- API?: affineMap.image_convexHull ℝ commutes with the image.
  simp only [Set.image_insert_eq,Set.image_singleton] -- [compile-fix]
  apply congrArg (convexHull ℝ) -- [compile-fix]
  rw [show (chartPose r).toAffineMap (B k) = featureCorner r k by exact chartPose_B r k, -- [compile-fix]
    show (chartPose r).toAffineMap (B (nextCorner k)) = featureCorner r (nextCorner k) by -- [compile-fix]
      exact chartPose_B r (nextCorner k), -- [compile-fix]
    show (chartPose r).toAffineMap (A ((profileCoefficient r : ℝ) / 10000)) = -- [compile-fix]
      featureApex r by exact chartPose_A r] -- [compile-fix]

/-- Reflection only in the normal coordinate. -/
def normalFlip : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.ofSurjective
    ({ toLinearMap :=
        { toFun := fun w => pt (w 0) (w 1) (-w 2)
          map_add' := by intros; ext i; fin_cases i <;> simp [pt] <;> ring -- [compile-fix]
          map_smul' := by intros; ext i; fin_cases i <;> simp [pt] }
       norm_map' := by
         intro w
         have hh : ‖pt (w 0) (w 1) (-w 2)‖^2=‖w‖^2 := by
           simp [norm_sq,pt]
         exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh } -- [compile-fix]
       : E3 →ₗᵢ[ℝ] E3)
    (by intro w; refine ⟨pt (w 0) (w 1) (-w 2),?_⟩; ext i; fin_cases i <;> simp [pt])

@[simp] theorem flip_apply (w : E3) : normalFlip w=pt (w 0) (w 1) (-w 2) := rfl

theorem flip_graph (a : ℝ) : normalFlip '' G a=G (-a) := by
  simp only [G,Set.image_union,Set.image_iUnion]
  congr 1 <;> congr 1 <;> funext k <;>
    change normalFlip.toLinearEquiv.toAffineEquiv.toAffineMap '' segment ℝ _ _ = _ <;> -- [compile-fix]
    rw [image_segment] <;> -- [compile-fix]
    simp [B,A,pt,flip_apply]

def SmallHeight (a : ℝ) : Prop := a≠0 ∧ a^2<2*eta^2

theorem native_small (r : Role) : SmallHeight ((profileCoefficient r:ℝ)/10000) := by
  obtain ⟨hnz,hbound⟩ := coefficient_bounds profile_canonical r
  have ha : |(profileCoefficient r:ℝ)|≤12 := by
    calc -- [compile-fix]
      |(profileCoefficient r : ℝ)| = ((profileCoefficient r).natAbs : ℝ) := by -- [compile-fix]
        simpa using (Nat.cast_natAbs (α := ℝ) (profileCoefficient r)).symm -- [compile-fix]
      _ ≤ 12 := by exact_mod_cast hbound -- [compile-fix]
      -- API?: simplification Int.natAbs_ofNat/coercion to absolute value.
  constructor
  · exact div_ne_zero (by exact_mod_cast hnz) (by norm_num)
  · rcases abs_le.mp ha with ⟨hl,hu⟩
    norm_num [eta]
    nlinarith [sq_nonneg ((profileCoefficient r:ℝ)-12),
      sq_nonneg ((profileCoefficient r:ℝ)+12)]

/-- Congruent compact graphs: a proof of equality from containment that
avoids the one-dimensional length formula altogether. -/
theorem opposite_graph_containment_eq {a : ℝ} (m : RigidMotion)
    (hsub : m '' G a ⊆ G (-a)) : m '' G a=G (-a) := by
  let f : RigidMotion := normalFlip.toAffineIsometryEquiv * m
  have hself : f '' G a ⊆ G a := by
    rw [show f '' G a = normalFlip '' (m '' G a) by simp [f,Set.image_image]]
    calc
      normalFlip '' (m '' G a) ⊆ normalFlip '' G (-a) := Set.image_mono hsub
      _ = G a := by rw [flip_graph,neg_neg]
  have heq := DischargeCompact.compact_isometry_image_eq (graph_compact a)
    f f.isometry hself
  have himage := congrArg (fun E : Set E3 => normalFlip '' E) heq
  have hflip (w : E3) : normalFlip (normalFlip w) = w := by -- [compile-fix]
    ext i -- [compile-fix]
    fin_cases i <;> simp [flip_apply, pt] -- [compile-fix]
  have hleft : normalFlip '' (f '' G a) = m '' G a := by -- [compile-fix]
    rw [Set.image_image] -- [compile-fix]
    apply congrArg (fun q : E3 → E3 => q '' G a) -- [compile-fix]
    funext w -- [compile-fix]
    change normalFlip (normalFlip (m w)) = m w -- [compile-fix]
    exact hflip (m w) -- [compile-fix]
  rw [hleft, flip_graph] at himage -- [compile-fix]
  exact himage -- [compile-fix]

/-- Equality of graphs first recovers the center. This center need not be
on the graph: it is intrinsically the center of its minimum enclosing ball. -/
theorem graph_eq_center {a b : ℝ} (ha : SmallHeight a) (hb : SmallHeight b)
    (m : RigidMotion) (heq : m '' G a=G b) : m 0=0 := by
  have hdist (k : Fin 4) : ‖m 0-B k‖^2≤2*eta^2 := by
    have hk : B k∈m '' G a := heq.symm ▸ B_mem b k
    obtain ⟨x,hx,hxm⟩ := hk
    have hi := m.isometry.dist_eq 0 x
    rw [hxm,dist_eq_norm,dist_eq_norm,zero_sub,norm_neg] at hi
    rw [hi]
    exact (graph_radius ha.2 hx).1
  have h0 := hdist 0
  have h2 := hdist 2
  rw [norm_sq] at h0 h2
  simp [B,pt,eta] at h0 h2
  have hz : (m 0) 0^2+(m 0) 1^2+(m 0) 2^2=0 := by
    nlinarith [sq_nonneg ((m 0) 0),sq_nonneg ((m 0) 1),sq_nonneg ((m 0) 2)]
  have hz0 : (m 0) 0 ^ 2 = 0 := by -- [compile-fix]
    nlinarith [sq_nonneg ((m 0) 1), sq_nonneg ((m 0) 2)] -- [compile-fix]
  have hz1 : (m 0) 1 ^ 2 = 0 := by -- [compile-fix]
    nlinarith [sq_nonneg ((m 0) 0), sq_nonneg ((m 0) 2)] -- [compile-fix]
  have hz2 : (m 0) 2 ^ 2 = 0 := by -- [compile-fix]
    nlinarith [sq_nonneg ((m 0) 0), sq_nonneg ((m 0) 1)] -- [compile-fix]
  ext i
  fin_cases i <;> simp only [PiLp.zero_apply] -- [compile-fix]
  · exact sq_eq_zero_iff.mp hz0 -- [compile-fix]
  · exact sq_eq_zero_iff.mp hz1 -- [compile-fix]
  · exact sq_eq_zero_iff.mp hz2 -- [compile-fix]

/-- The four base corners are precisely the maximum-radius graph points. -/
theorem graph_eq_corners {a b : ℝ} (ha : SmallHeight a) (hb : SmallHeight b)
    (m : RigidMotion) (heq : m '' G a=G b) :
    ∃p : Fin 4 ≃ Fin 4,∀k,m (B k)=B (p k) := by
  have hc := graph_eq_center ha hb m heq
  have heach (k : Fin 4) : ∃j,m (B k)=B j := by
    have hmem : m (B k)∈G b := heq ▸ ⟨B k,B_mem a k,rfl⟩
    apply (graph_radius hb.2 hmem).2
    have hdist := m.isometry.dist_eq (B k) 0
    rw [hc,dist_zero_right,dist_zero_right] at hdist
    rw [hdist,norm_sq]
    fin_cases k <;> simp [B,pt] <;> ring
  choose p hp using heach
  have hBinj : Function.Injective B := by
    intro i j h
    fin_cases i <;> fin_cases j -- [compile-fix]
    all_goals norm_num [B,pt,eta] at h -- [compile-fix]
    all_goals rfl -- [compile-fix]
  have hpi : Function.Injective p := by
    intro i j hij
    apply hBinj; apply m.injective
    rw [hp,hp,hij]
  let e := Equiv.ofBijective p ⟨hpi,Finite.surjective_of_injective hpi⟩
    -- API?: finite-type injective endomap is surjective.
  exact ⟨e,hp⟩

/-- Equal distances to all four base corners pin a graph point to the apex. -/
theorem graph_eq_apex {a b : ℝ} (ha : SmallHeight a) (hb : SmallHeight b)
    (m : RigidMotion) (heq : m '' G a=G b) : m (A a)=A b := by
  obtain ⟨p,hp⟩ := graph_eq_corners ha hb m heq
  have hdist (k : Fin 4) : ‖m (A a)-B k‖^2=2*eta^2+a^2 := by
    obtain ⟨j,rfl⟩ := p.surjective k
    rw [← hp j]
    have hd := m.isometry.dist_eq (A a) (B j)
    rw [dist_eq_norm,dist_eq_norm] at hd
    rw [hd,norm_sq]
    fin_cases j <;> simp [A,B,pt] <;> ring
  have h0 := hdist 0
  have h1 := hdist 1
  have h3 := hdist 3
  rw [norm_sq] at h0 h1 h3
  simp [B,pt,eta] at h0 h1 h3
  have hx : m (A a) 0=0 := by nlinarith
  have hy : m (A a) 1=0 := by nlinarith
  exact graph_on_axis (heq ▸ ⟨A a,A_mem a,rfl⟩) hx hy

/-- An adjacent-corner pair is preserved. This is the only finite square
calculation, independent of all R44 certificates and coefficient values. -/
theorem corner_adjacency {a b : ℝ} (ha : SmallHeight a) (hb : SmallHeight b)
    (m : RigidMotion) (heq : m '' G a=G b)
    (p : Fin 4 ≃ Fin 4) (hp : ∀ k, m (B k) = B (p k)) (k : Fin 4) : -- [compile-fix]
    p (nextCorner k)=nextCorner (p k) ∨
      p k=nextCorner (p (nextCorner k)) := by
  have hd := m.isometry.dist_eq (B k) (B (nextCorner k))
  rw [hp,hp,dist_eq_norm,dist_eq_norm] at hd
  have hs := congrArg (fun z : ℝ => z^2) hd
  rw [norm_sq,norm_sq] at hs
  generalize hi : p k=i at *
  generalize hj : p (nextCorner k)=j at *
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [B,nextCorner,pt,eta] at hs ⊢ <;> simp at hs -- [compile-fix]

/-- The four lateral triangles are recovered from the graph, not from an
assumed match of filled facets. -/
theorem graph_eq_surface {a b : ℝ} (ha : SmallHeight a) (hb : SmallHeight b)
    (m : RigidMotion) (heq : m '' G a=G b) : m '' S a=S b := by
  have forward {a b : ℝ} (ha : SmallHeight a) (hb : SmallHeight b)
      (m : RigidMotion) (heq : m '' G a=G b) : m '' S a⊆S b := by
    obtain ⟨p,hp⟩ := graph_eq_corners ha hb m heq
    have hapex := graph_eq_apex ha hb m heq
    simp only [S,Set.image_iUnion]
    intro x hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    change x ∈ m.toAffineMap '' convexHull ℝ _ at hk -- [compile-fix]
    rw [AffineMap.image_convexHull] at hk -- [compile-fix]
      -- API?: affine maps commute with finite convex hull.
    simp only [Set.image_insert_eq,Set.image_singleton] at hk -- [compile-fix]
    rw [show m.toAffineMap (B k) = B (p k) by exact hp k, -- [compile-fix]
      show m.toAffineMap (B (nextCorner k)) = B (p (nextCorner k)) by -- [compile-fix]
        exact hp (nextCorner k), -- [compile-fix]
      show m.toAffineMap (A a) = A b by exact hapex] at hk -- [compile-fix]
    rcases corner_adjacency ha hb m heq p hp k with he | he
    · exact Set.mem_iUnion.mpr ⟨p k,by simpa [he] using hk⟩
    · refine Set.mem_iUnion.mpr ⟨p (nextCorner k),?_⟩
      simpa [he,Set.insert_comm] using hk
  apply Set.Subset.antisymm (forward ha hb m heq)
  have hinv : m.symm '' G b=G a := by
    rw [← heq,Set.image_image]
    simp
  have hs := forward hb ha m.symm hinv
  intro x hx
  refine ⟨m.symm x,hs ⟨x,hx,rfl⟩,by simp⟩

/-- In opposite-height coordinates, the normal reverses. -/
theorem graph_eq_normal {a : ℝ} (ha : SmallHeight a)
    (m : RigidMotion) (heq : m '' G a=G (-a)) :
    m.linearIsometryEquiv (pt 0 0 1) = -(pt 0 0 1) := by
  have hb : SmallHeight (-a) := ⟨neg_ne_zero.mpr ha.1,by simpa using ha.2⟩
  have hz := graph_eq_center ha hb m heq
  have ht := graph_eq_apex ha hb m heq
  have hm := m.map_vadd (0:E3) (A a)
  simp only [vadd_eq_add,add_zero,hz,zero_add] at hm
  have hai : A a=a • pt 0 0 1 := by ext i; fin_cases i <;> simp [A,pt]
  have hbi : A (-a)=a • -(pt 0 0 1) := by ext i; fin_cases i <;> simp [A,pt]
  rw [hm,hai,map_smul,hbi] at ht
  ext i
  have hi := congrArg (fun w : E3 => w i) ht
  simp only [PiLp.smul_apply,smul_eq_mul] at hi
  exact mul_left_cancel₀ ha.1 hi
  -- API?: expected mul_left_cancel₀ : a ≠ 0 → a*b = a*c → b=c.

end
end R44.DischargePyramid
