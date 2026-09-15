import R44.CollarPredicates
import R44.Proved.RetainedCoreOverlap
import R44.Proved.CarrierFeatureFrameReduction
import R44.Proved.CircularConeSolidAngle
import R44.Proved.PerTubeHomeomorphisms
import R44.Proved.FeatureTubeMapsGlue
import R44.Proved.FeatureTubeMapCarriesCarrier
import R44.Proved.FeatureCircularConeContainment
import R44.Proved.PlanarAreaCarrierRecovery
import R44.Proved.ConeSectorBudgets
import R44.Proved.ConnectedFeatureCompanion
import R44.Proved.FeatureContainmentRigidity
import R44.Proved.CompanionPoseDiscrete
import R44.Proved.OnlyRegisteredMates
import R44.Proved.ComponentSolidsCover
import R44.Proved.SmallCollarRealization
import R44.Proved.CompleteDihedralList -- [compile-fix: exchange-7 endpoint promoted]
import R44.Proved.GenericFeaturePartner -- [compile-fix: exchange-7 endpoint promoted]
import R44.Proved.BaselineComponentCoversGrid -- [compile-fix: exchange-7 endpoint promoted]
import R44.Proved.UnrestrictedAlignment -- [compile-fix: exchange-7 endpoint promoted]

/-!
# The logical spine of the R44 theorem (0 residual fields)

The geometric object, feature strata, and propositions used by the promoted
proofs are defined in `R44.LogicalSpineFoundation`. Continuous properties are
proved here; `Hypotheses` is retained as an empty historical interface.
-/

namespace R44

open scoped Pointwise
open Set
open Generated

noncomputable section

/-- The `i`th literal child pose; index 7 is the designated central child. -/
def literalChildPose (i : Fin 8) : Pose := getD children i.val rootPose

def centralChildIndex : Fin 8 := ⟨7, by omega⟩

/-- `g` is the canonically labelled `i`th child of geometric parent pose
    `π`.  The role is a proposition determined by the two poses, not stored
    as freely permutable data. -/
def ChildOfParent (π : RigidMotion) (i : Fin 8) (g : RigidMotion) : Prop :=
  RealizesPose (π⁻¹ * g) (literalChildPose i)

def CentralChildOfParent (π g : RigidMotion) : Prop :=
  ChildOfParent π centralChildIndex g

/-- A canonical child role of a fixed parent pose determines the child
    placement. -/
theorem childOfParent_unique {π g h : RigidMotion} {i : Fin 8}
    (hg : ChildOfParent π i g) (hh : ChildOfParent π i h) : g = h := by
  have hrel : π⁻¹ * g = π⁻¹ * h := realizesPose_unique hg hh
  calc
    g = π * (π⁻¹ * g) := by group
    _ = π * (π⁻¹ * h) := congrArg (fun k : RigidMotion => π * k) hrel
    _ = h := by group

/-- All eight literal children of `π` occur in the tiling. -/
def CompleteParent {S : Set E3} (T : Tiling S) (π : RigidMotion) : Prop :=
  ∀ i : Fin 8, ∃ g ∈ T.placements, ChildOfParent π i g

/-- The local shell/completion conclusion used in Theorem 7.1: every placed
    tile belongs, in its determined literal role, to a complete parent. -/
def EveryPlacementHasCompleteParent {S : Set E3} (T : Tiling S) : Prop :=
  ∀ g : RigidMotion, g ∈ T.placements →
    ∃ π : RigidMotion, CompleteParent T π ∧
      ∃ i : Fin 8, ChildOfParent π i g

/-- The geometric readout of the 28-pair conflict census: two complete
    literal parents cannot share a placed tile, even under different roles. -/
def CompleteParentsDisjoint {S : Set E3} (T : Tiling S) : Prop :=
  ∀ ⦃π ρ g : RigidMotion⦄ ⦃i j : Fin 8⦄,
    CompleteParent T π → CompleteParent T ρ →
      ChildOfParent π i g → ChildOfParent ρ j g → π = ρ ∧ i = j

/-- The component placement `h` owns the root-shell cell `c` in the normalized
    integer-cell coordinates intrinsic to `relativeMotion g h`. -/
def ComponentOwnsShellCell {S : Set E3} (T : Tiling S) (g : RigidMotion)
    (c : V3) (h : RigidMotion) : Prop :=
  h ∈ T.placements ∧ SameFeatureComponent T g h ∧
    ∃ p : Pose, p.frame ∈ allFrames ∧
      RealizesPose (relativeMotion g h) p ∧ c ∈ body p

/-- The component owner is represented by the `k`th literal registered
    neighbour pose, which covers that same root-shell cell. -/
def ShellCellOwner {S : Set E3} (T : Tiling S) (g : RigidMotion)
    (c : V3) (h : RigidMotion) (k : Nat) : Prop :=
  ComponentOwnsShellCell T g c h ∧
    k ∈ List.range legalContacts.length ∧
    RealizesPose (relativeMotion g h) (getD legalContacts k rootPose) ∧
    c ∈ coverAt k

/-- R§7's first-shell statement in its native lattice form.  Every one of the
    22 shell cells has a unique owner in the root's registered feature
    component; the indices of precisely those owners form one of the 33
    literal certified shells. -/
def CertifiedFirstShells {S : Set E3} (T : Tiling S) : Prop :=
  ∀ g : RigidMotion, g ∈ T.placements →
    ∃ shell ∈ shellSolutions,
      (∀ c ∈ shellCells, ∃! h : RigidMotion,
        ComponentOwnsShellCell T g c h) ∧
      (∀ c ∈ shellCells, ∀ h : RigidMotion,
        ComponentOwnsShellCell T g c h →
          ∃ k ∈ shell, ShellCellOwner T g c h k) ∧
      ∀ k ∈ shell, ∃ c ∈ shellCells, ∃ h : RigidMotion,
        ShellCellOwner T g c h k

/-- A geometric partition into literal eight-child clusters.  `covers`
    identifies the placements exactly with the union of all literal fibers;
    `each_child` rules out a deficient fiber; `disjoint` says that the union
    is disjoint, including its canonical child indices. -/
structure ParentPartition {S : Set E3} (T : Tiling S) where
  parents : Set RigidMotion
  covers : ∀ g : RigidMotion,
    g ∈ T.placements ↔ ∃ π ∈ parents, ∃ i : Fin 8, ChildOfParent π i g
  each_child : ∀ π ∈ parents, ∀ i : Fin 8,
    ∃ g ∈ T.placements, ChildOfParent π i g
  disjoint : ∀ ⦃π ρ g : RigidMotion⦄ ⦃i j : Fin 8⦄,
    π ∈ parents → ρ ∈ parents →
    ChildOfParent π i g → ChildOfParent ρ j g → π = ρ ∧ i = j

/-- Partition proof fields carry no choices: the geometric parent-pose set
    determines the entire structure. -/
@[ext] theorem ParentPartition.ext {S : Set E3} {T : Tiling S}
    {A B : ParentPartition T} (h : A.parents = B.parents) : A = B := by
  cases A
  cases B
  cases h
  rfl

def HasUniqueParent {S : Set E3} (T : Tiling S) : Prop :=
  Nonempty (ParentPartition T) ∧ Subsingleton (ParentPartition T)

/-- Once the two genuine geometric conclusions of the local census are
    available, the parent partition itself and its uniqueness are pure logic.
    In particular no freely permutable role labels are introduced. -/
theorem hasUniqueParent_of_completeParents {S : Set E3} (T : Tiling S)
    (hexists : EveryPlacementHasCompleteParent T)
    (hconflict : CompleteParentsDisjoint T) : HasUniqueParent T := by
  let A : ParentPartition T := {
    parents := {π | CompleteParent T π}
    covers := by
      intro g
      constructor
      · intro hg
        obtain ⟨π, hπ, i, hi⟩ := hexists g hg
        exact ⟨π, hπ, i, hi⟩
      · rintro ⟨π, hπ, i, hi⟩
        obtain ⟨h, hh, hhi⟩ := hπ i
        rwa [childOfParent_unique hi hhi]
    each_child := by
      intro π hπ i
      exact hπ i
    disjoint := by
      intro π ρ g i j hπ hρ hi hj
      exact hconflict hπ hρ hi hj
  }
  refine ⟨⟨A⟩, ⟨?_⟩⟩
  intro B C
  apply ParentPartition.ext
  apply Set.Subset.antisymm
  · intro π hπ
    have hcomplete : CompleteParent T π := B.each_child π hπ
    obtain ⟨g, hg, hgi⟩ := hcomplete centralChildIndex
    obtain ⟨ρ, hρ, j, hgj⟩ := (C.covers g).mp hg
    have hρcomplete : CompleteParent T ρ := C.each_child ρ hρ
    exact (hconflict hcomplete hρcomplete hgi hgj).1 ▸ hρ
  · intro ρ hρ
    have hcomplete : CompleteParent T ρ := C.each_child ρ hρ
    obtain ⟨g, hg, hgj⟩ := hcomplete centralChildIndex
    obtain ⟨π, hπ, i, hgi⟩ := (B.covers g).mp hg
    have hπcomplete : CompleteParent T π := B.each_child π hπ
    exact (hconflict hcomplete hπcomplete hgj hgi).1 ▸ hπ

private theorem childOfParent_translate_iff (v : E3) (π g : RigidMotion)
    (i : Fin 8) :
    ChildOfParent (translation v * π) i (translation v * g) ↔
      ChildOfParent π i g := by
  unfold ChildOfParent
  have hrel : (translation v * π)⁻¹ * (translation v * g) = π⁻¹ * g := by
    group
  rw [hrel]

/-- Translate a geometric parent partition by translating all macro-poses.
    The literal role of each child is unchanged. -/
def translateParentPartition {S : Set E3} {T : Tiling S} (v : E3)
    (A : ParentPartition T) : ParentPartition (translateTiling v T) where
  parents := translation v • A.parents
  covers := by
    intro g
    constructor
    · intro hg
      change g ∈ translation v • T.placements at hg
      rw [Set.mem_smul_set] at hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg
      obtain ⟨π, hπ, i, hi⟩ := (A.covers g₀).mp hg₀
      exact ⟨translation v * π, Set.mem_smul_set.mpr ⟨π, hπ, rfl⟩,
        i, (childOfParent_translate_iff v π g₀ i).mpr hi⟩
    · rintro ⟨π', hπ', i, hi⟩
      rw [Set.mem_smul_set] at hπ'
      obtain ⟨π, hπ, rfl⟩ := hπ'
      let g₀ : RigidMotion := (translation v)⁻¹ * g
      have hgform : translation v * g₀ = g := by
        dsimp [g₀]
        group
      have hi₀ : ChildOfParent π i g₀ := by
        rw [← childOfParent_translate_iff v π g₀ i, hgform]
        exact hi
      exact Set.mem_smul_set.mpr ⟨g₀,
        (A.covers g₀).mpr ⟨π, hπ, i, hi₀⟩, hgform⟩
  each_child := by
    intro π' hπ' i
    rw [Set.mem_smul_set] at hπ'
    obtain ⟨π, hπ, rfl⟩ := hπ'
    obtain ⟨g, hg, hi⟩ := A.each_child π hπ i
    exact ⟨translation v * g, Set.mem_smul_set.mpr ⟨g, hg, rfl⟩,
      (childOfParent_translate_iff v π g i).mpr hi⟩
  disjoint := by
    intro π' ρ' g i j hπ' hρ' hi hj
    rw [Set.mem_smul_set] at hπ' hρ'
    obtain ⟨π, hπ, rfl⟩ := hπ'
    obtain ⟨ρ, hρ, rfl⟩ := hρ'
    let g₀ : RigidMotion := (translation v)⁻¹ * g
    have hgform : translation v * g₀ = g := by
      dsimp [g₀]
      group
    have hi₀ : ChildOfParent π i g₀ := by
      rw [← childOfParent_translate_iff v π g₀ i, hgform]
      exact hi
    have hj₀ : ChildOfParent ρ j g₀ := by
      rw [← childOfParent_translate_iff v ρ g₀ j, hgform]
      exact hj
    obtain ⟨hπρ, hij⟩ := A.disjoint hπ hρ hi₀ hj₀
    exact ⟨by rw [hπρ], hij⟩

/-- Keep a macro-pose's orthogonal frame and divide its origin by two. -/
def halfPose (g : RigidMotion) : RigidMotion :=
  translation ((2 : ℝ)⁻¹ • g 0) *
    g.linearIsometryEquiv.toAffineIsometryEquiv

/-- Halving affine origins while retaining linear parts respects composition.
    This is the structural reason a registration ambient can be transported
    from parent macro-poses to their halved poses. -/
theorem halfPose_mul (g h : RigidMotion) :
    halfPose (g * h) = halfPose g * halfPose h := by
  apply AffineIsometryEquiv.ext
  intro x
  have hg := g.map_vadd (0 : E3) (h 0)
  simp only [vadd_eq_add, add_zero] at hg
  simp only [halfPose, AffineIsometryEquiv.coe_mul, Function.comp_apply]
  simp [translation, hg, smul_add, map_smul, add_assoc]
  change
    (2 : ℝ)⁻¹ • g.linearIsometryEquiv (h 0) +
        ((2 : ℝ)⁻¹ • g 0 +
          g.linearIsometryEquiv (h.linearIsometryEquiv x)) =
      (2 : ℝ)⁻¹ • g 0 +
        ((2 : ℝ)⁻¹ • g.linearIsometryEquiv (h 0) +
          g.linearIsometryEquiv (h.linearIsometryEquiv x))
  abel

theorem halfPose_translate (v : E3) (g : RigidMotion) :
    halfPose (translation v * g) =
      translation ((2 : ℝ)⁻¹ • v) * halfPose g := by
  apply AffineIsometryEquiv.ext
  intro x
  have hlinear :
      (translation v * g).linearIsometryEquiv = g.linearIsometryEquiv := by
    change (translation v).linearIsometryEquiv * g.linearIsometryEquiv = _
    congr 1
  simp only [halfPose, AffineIsometryEquiv.coe_mul, Function.comp_apply]
  rw [hlinear]
  simp [translation, add_assoc]

private theorem half_cast_of_even {a : Int} (h : a % 2 = 0) :
    ((a / 2 : Int) : ℝ) = (2 : ℝ)⁻¹ * (a : ℝ) := by
  have ha : 2 * (a / 2) = a := by omega
  have har : (2 : ℝ) * ((a / 2 : Int) : ℝ) = (a : ℝ) := by
    exact_mod_cast ha
  norm_num
  linarith

/-- An even integral pose remains integral after its affine origin is halved,
    and realizes the literal `halvePose` computed by the phase-1 model. -/
theorem halfPose_realizes_halvePose {g : RigidMotion} {p : Pose}
    (hg : RealizesPose g p) (heven : evenPose p = true) :
    RealizesPose (halfPose g) (halvePose p) := by
  simp only [evenPose, Bool.and_eq_true] at heven
  constructor
  · intro x i
    have hlin : (halfPose g).linearIsometryEquiv = g.linearIsometryEquiv := by
      apply LinearIsometryEquiv.ext
      intro y
      rfl
    rw [hlin]
    exact hg.1 x i
  · intro i
    have horigin : halfPose g 0 = (2 : ℝ)⁻¹ • g 0 := by
      simp [halfPose, translation]
    have hi := congrArg (fun y : E3 => y i) horigin
    rw [hi]
    fin_cases i
    · change _ = ((p.shift.x / 2 : Int) : ℝ)
      simp [smul_eq_mul, hg.2]
      apply Eq.symm
      apply half_cast_of_even
      simpa [V3.get] using heven.1.1
    · change _ = ((p.shift.y / 2 : Int) : ℝ)
      simp [smul_eq_mul, hg.2]
      apply Eq.symm
      apply half_cast_of_even
      simpa [V3.get] using heven.1.2
    · change _ = ((p.shift.z / 2 : Int) : ℝ)
      simp [smul_eq_mul, hg.2]
      apply Eq.symm
      apply half_cast_of_even
      simpa [V3.get] using heven.2

/-- The parent-atlas certificate's 44 admitted macro contacts all have even
    translations, exposed propositionally for the coarsening proof. -/
theorem computedMacroLegal_even (hatlas : parentAtlasCheck = true)
    {p : Pose} (hp : p ∈ computedMacroLegal) : evenPose p = true := by
  have hall : computedMacroLegal.all evenPose = true := by
    unfold parentAtlasCheck at hatlas
    simp only [Bool.and_eq_true] at hatlas
    aesop
  exact List.all_eq_true.mp hall p hp

/-- The parent origins divided by two, with their registered frames retained. -/
def halvedParentPoses {S : Set E3} {T : Tiling S}
    (A : ParentPartition T) : Set RigidMotion :=
  halfPose '' A.parents

theorem halvedParentPoses_translate {S : Set E3} {T : Tiling S}
    (v : E3) (A : ParentPartition T) :
    halvedParentPoses (translateParentPartition v A) =
      translation ((2 : ℝ)⁻¹ • v) • halvedParentPoses A := by
  ext m
  constructor
  · rintro ⟨π', hπ', rfl⟩
    change π' ∈ translation v • A.parents at hπ'
    rw [Set.mem_smul_set] at hπ'
    obtain ⟨π, hπ, rfl⟩ := hπ'
    exact Set.mem_smul_set.mpr
      ⟨halfPose π, ⟨π, hπ, rfl⟩, (halfPose_translate v π).symm⟩
  · intro hm
    rw [Set.mem_smul_set] at hm
    obtain ⟨m, ⟨π, hπ, rfl⟩, hm⟩ := hm
    refine ⟨translation v * π,
      Set.mem_smul_set.mpr ⟨π, hπ, rfl⟩, ?_⟩
    rw [halfPose_translate]
    exact hm

/-! ## Registered baseline languages

The two hierarchy constructions first produce tilings by the undeformed chair
`P`.  The following structures keep that combinatorial conclusion separate
from the one shared geometric small-collar realization step. -/

/-- Relative pose belongs to the closed 30-state substitution language. -/
def ClosedContactRelated (g h : RigidMotion) : Prop :=
  ∃ p ∈ closedContacts, RealizesPose (relativeMotion g h) p

def ClosedContactFaceLanguage (A : Set RigidMotion) : Prop :=
  ∀ ⦃g h : RigidMotion⦄, g ∈ A → h ∈ A → g ≠ h →
    LatticeFaceAdjacent g h → ClosedContactRelated g h

/-- A hierarchy baseline tiling before the finite inclusion of its 30 contact
    states in the 44-contact atlas is applied. -/
structure HierarchyBaselineTiling (A : Set RigidMotion)
    extends RegisteredBaselineTiling A where
  closed_faces : ClosedContactFaceLanguage A

/-- Structural soundness of the generated Boolean equality on integer vectors. -/
private theorem v3_eq_of_beq {a b : V3} (h : (a == b) = true) : a = b := by
  rcases a with ⟨ax, ay, az⟩
  rcases b with ⟨bx, byv, bz⟩
  unfold instBEqV3 instBEqV3.beq at h
  simp at h
  simp_all

private theorem pose_eq_of_beq {a b : Pose} (h : (a == b) = true) : a = b := by
  rcases a with ⟨af, ashift⟩
  rcases b with ⟨bf, bshift⟩
  unfold instBEqPose instBEqPose.beq at h
  simp only [Bool.and_eq_true] at h
  rw [frame_eq_of_beq h.1, v3_eq_of_beq h.2]

private local instance lawfulBEqPose : LawfulBEq Pose where
  rfl := by
    intro a
    rcases a with
      ⟨⟨⟨ap0, ap1, ap2⟩, ⟨as0, as1, as2⟩⟩, ⟨ax, ay, az⟩⟩
    unfold instBEqPose instBEqPose.beq instBEqFrame instBEqFrame.beq
      instBEqN3 instBEqN3.beq instBEqV3 instBEqV3.beq
    simp
  eq_of_beq := pose_eq_of_beq

private local instance equivBEqPose : EquivBEq Pose where
  symm := by
    intro a b hab
    have h : a = b := pose_eq_of_beq hab
    subst b
    exact lawfulBEqPose.rfl
  trans := by
    intro a b c hab hbc
    have hab' : a = b := pose_eq_of_beq hab
    have hbc' : b = c := pose_eq_of_beq hbc
    subst b
    subst c
    exact lawfulBEqPose.rfl

private local instance lawfulHashablePose : LawfulHashable Pose where
  hash_eq := by
    intro a b hab
    rw [pose_eq_of_beq hab]

private theorem mem_hashDedup_iff {p : Pose} {xs : List Pose} :
    p ∈ hashDedup xs ↔ p ∈ xs := by
  unfold hashDedup
  rw [Std.HashSet.mem_toList, Std.HashSet.mem_ofList,
    List.contains_iff_mem]

/-- Add an integer translation to the literal shift of a pose. -/
private def addPoseShift (a : V3) (p : Pose) : Pose :=
  po p.frame (p.shift.add a)

/-- Refinement commutes with translation, with the translation doubled. -/
private theorem addPoseShift_refine_mem {a : V3} {p q : Pose}
    (hq : q ∈ refine p) :
    addPoseShift (a.smul 2) q ∈ refine (addPoseShift a p) := by
  unfold refine at hq ⊢
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
  apply List.mem_map.mpr
  refine ⟨c, hc, ?_⟩
  rcases a with ⟨ax, ay, az⟩
  rcases p with ⟨pf, px, py, pz⟩
  rcases c with ⟨cf, cx, cy, cz⟩
  simp only [addPoseShift, po, V3.add, V3.smul]
  apply congrArg (po (pf.mul cf))
  rcases pf with ⟨⟨p0, p1, p2⟩, s0, s1, s2⟩
  simp [Frame.act, V3.get, v] <;> ring_nf
  simp

/-- Two refinement steps multiply an ambient literal translation by four.
    The source list need only embed into the target list. -/
private theorem addPoseShift_twoRefinements_mem {a : V3}
    {xs ys : List Pose} {q : Pose}
    (hq : q ∈ twoRefinements xs)
    (hxy : ∀ p ∈ xs, addPoseShift a p ∈ ys) :
    addPoseShift (a.smul 4) q ∈ twoRefinements ys := by
  unfold twoRefinements at hq ⊢
  rw [mem_hashDedup_iff] at hq ⊢
  obtain ⟨r, hr, hqr⟩ := List.mem_flatMap.mp hq
  obtain ⟨p, hp, hrp⟩ := List.mem_flatMap.mp hr
  have hr' : addPoseShift (a.smul 2) r ∈ refine (addPoseShift a p) :=
    addPoseShift_refine_mem hrp
  have hq' : addPoseShift ((a.smul 2).smul 2) q ∈
      refine (addPoseShift (a.smul 2) r) :=
    addPoseShift_refine_mem hqr
  have ha : (a.smul 2).smul 2 = a.smul 4 := by
    rcases a with ⟨ax, ay, az⟩
    simp [V3.smul, v] <;> ring_nf
    simp
  rw [ha] at hq'
  apply List.mem_flatMap.mpr
  refine ⟨addPoseShift (a.smul 2) r, ?_, hq'⟩
  apply List.mem_flatMap.mpr
  exact ⟨addPoseShift a p, hxy p hp, hr'⟩

private theorem mem_of_subset_true {xs ys : List Pose}
    (h : subset xs ys = true) {p : Pose} (hp : p ∈ xs) : p ∈ ys := by
  apply List.contains_iff_mem.mp
  exact List.all_eq_true.mp h p hp

/-- The closed hierarchy language is literally included in the admitted
    atlas, read propositionally from the phase-1 atlas check. -/
theorem closedContacts_subset_legal (hatlas : atlasCheck = true) :
    ∀ p : Pose, p ∈ closedContacts → p ∈ legalContacts := by
  simp only [atlasCheck, Bool.and_eq_true] at hatlas
  intro p hp
  have hpcomputed : p ∈ computedLegalContacts :=
    mem_of_subset_true hatlas.1.2 hp
  have heq := hatlas.1.1.1.2
  simp only [setEq, Bool.and_eq_true] at heq
  exact mem_of_subset_true heq.1 hpcomputed

/-- Convert a hierarchy baseline tiling to the common atlas-admissible
    interface using the phase-1 literal inclusion. -/
def HierarchyBaselineTiling.toAtlas {A : Set RigidMotion}
    (B : HierarchyBaselineTiling A) (hatlas : atlasCheck = true) :
    AtlasBaselineTiling A where
  toRegisteredBaselineTiling := B.toRegisteredBaselineTiling
  atlas_faces := by
    intro g h hg hh hne hface
    obtain ⟨p, hp, hpose⟩ := B.closed_faces hg hh hne hface
    exact ⟨p, closedContacts_subset_legal hatlas p hp, hpose⟩

/-- Two-refinement levels before the centering translation of R§9. -/
def hierarchyPoseLevel : Nat → List Pose
  | 0 => [rootPose]
  | n + 1 => twoRefinements (hierarchyPoseLevel n)

/-- The integer centering shift, in the recurrence form
    `c_0 = 0`, `c_(n+1) = 4 c_n + 2` of R§9. -/
def hierarchyCenterShift : Nat → Int
  | 0 => 0
  | n + 1 => 4 * hierarchyCenterShift n + 2

/-- The recurrence gives the closed-form identity needed to compare two
    consecutive centerings, without appealing to truncated natural-number
    division. -/
private theorem hierarchyCenterShift_identity (n : Nat) :
    3 * hierarchyCenterShift n + 2 = 2 * (4 : Int) ^ n := by
  induction n with
  | zero => norm_num [hierarchyCenterShift]
  | succ n ih =>
      rw [hierarchyCenterShift, pow_succ]
      calc
        3 * (4 * hierarchyCenterShift n + 2) + 2 =
            4 * (3 * hierarchyCenterShift n + 2) := by ring
        _ = 4 * (2 * (4 : Int) ^ n) := by rw [ih]
        _ = 2 * ((4 : Int) ^ n * 4) := by ring

private theorem hierarchyCenterShift_add_step (n : Nat) :
    hierarchyCenterShift (n + 1) =
      hierarchyCenterShift n + 2 * (4 : Int) ^ n := by
  calc
    hierarchyCenterShift (n + 1) = 4 * hierarchyCenterShift n + 2 := by
      rfl
    _ = hierarchyCenterShift n + (3 * hierarchyCenterShift n + 2) := by
      ring
    _ = hierarchyCenterShift n + 2 * (4 : Int) ^ n := by
      rw [hierarchyCenterShift_identity]

/-- Read the same-frame grandchild directly from the phase-1 control. -/
private theorem sameFrameGrandchild_mem
    (hnested : nestedPatchControlsCheck = true) :
    po identityFrame (v 2 2 2) ∈ hierarchyPoseLevel 1 := by
  change po identityFrame (v 2 2 2) ∈ twoRefinements [rootPose]
  apply List.contains_iff_mem.mp
  simp only [nestedPatchControlsCheck, Bool.and_eq_true] at hnested
  exact hnested.1.1.1.1.1.1.1.1

/-- Applying `2n` more refinement steps to the same-frame grandchild
    embeds the whole level `n` in level `n+1`, translated by
    `2·4^n (1,1,1)`. -/
private theorem hierarchyPoseLevel_shift_embeds
    (hnested : nestedPatchControlsCheck = true) :
    ∀ n : Nat, ∀ p ∈ hierarchyPoseLevel n,
      addPoseShift
          (v (2 * (4 : Int) ^ n) (2 * (4 : Int) ^ n)
            (2 * (4 : Int) ^ n)) p ∈
        hierarchyPoseLevel (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro p hp
      simp only [hierarchyPoseLevel, List.mem_singleton] at hp
      subst p
      simpa [addPoseShift, rootPose, V3.add, v, po] using
        sameFrameGrandchild_mem hnested
  | succ n ih =>
      intro p hp
      change p ∈ twoRefinements (hierarchyPoseLevel n) at hp
      have hshift := addPoseShift_twoRefinements_mem
        (a := v (2 * (4 : Int) ^ n) (2 * (4 : Int) ^ n)
          (2 * (4 : Int) ^ n))
        (ys := hierarchyPoseLevel (n + 1)) hp ih
      have ha :
          (v (2 * (4 : Int) ^ n) (2 * (4 : Int) ^ n)
              (2 * (4 : Int) ^ n)).smul 4 =
            v (2 * (4 : Int) ^ (n + 1)) (2 * (4 : Int) ^ (n + 1))
              (2 * (4 : Int) ^ (n + 1)) := by
        simp [V3.smul, v, pow_succ] <;> ring_nf
      rw [ha] at hshift
      exact hshift

/-- The exact finite patch `A_n` of R§9. -/
def hierarchyPatch (n : Nat) : List Pose :=
  translatedPatch (hierarchyCenterShift n) (hierarchyPoseLevel n)

/-- The infinite definition is anchored exactly to both finite phase-1
    patches, rather than merely reproducing their cardinalities. -/
theorem hierarchyPatch_one : hierarchyPatch 1 = nestedPatchOne := by rfl

theorem hierarchyPatch_two : hierarchyPatch 2 = nestedPatchTwo := by rfl

def hierarchyCells (n : Nat) : List V3 :=
  (hierarchyPatch n).flatMap body

def hierarchyCellSupport (n : Nat) : Set E3 :=
  {x | ∃ a ∈ hierarchyCells n, x ∈ unitCube a}

def hierarchyBoundingBox (n : Nat) : Set E3 :=
  {x | ∀ i : Fin 3,
    (-(hierarchyCenterShift n : Int) : ℝ) ≤ x i ∧
      x i ≤ (((4 ^ n + 2) / 3 : Nat) : ℝ)}

/-- The same-frame `(I,(2,2,2))` grandchild makes every centered patch a
    literal subpatch of the next. -/
def HierarchyPatchesNested : Prop :=
  ∀ n : Nat, ∀ p ∈ hierarchyPatch n, p ∈ hierarchyPatch (n + 1)

/-- R§9 same-frame-grandchild induction: every centered literal hierarchy
    patch is a subpatch of its successor. -/
theorem hierarchy_patch_nesting
    (hnested : nestedPatchControlsCheck = true) :
    HierarchyPatchesNested := by
  intro n p hp
  unfold hierarchyPatch translatedPatch at hp ⊢
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  let a : Int := 2 * (4 : Int) ^ n
  have hq' : addPoseShift (v a a a) q ∈ hierarchyPoseLevel (n + 1) := by
    exact hierarchyPoseLevel_shift_embeds hnested n q hq
  apply List.mem_map.mpr
  refine ⟨addPoseShift (v a a a) q, hq', ?_⟩
  have hc : hierarchyCenterShift (n + 1) = hierarchyCenterShift n + a := by
    exact hierarchyCenterShift_add_step n
  rcases q with ⟨qf, qx, qy, qz⟩
  simp only [addPoseShift, po, V3.add, V3.sub, v]
  rw [hc]
  simp [a]

/-- Every finite hierarchy level is a packing by distinct unit cells. -/
def HierarchyCellsDisjoint : Prop :=
  ∀ n : Nat, (hierarchyCells n).Nodup

/-- The documented centered cube lies in the baseline support at every
    hierarchy level. -/
def HierarchyBoxContainment : Prop :=
  ∀ n : Nat, hierarchyBoundingBox n ⊆ hierarchyCellSupport n


private theorem childrenFrames_data {c : Pose} (hc : c ∈ children) :
    FrameData c.frame := by
  simp [children, fr, n3, v] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

private theorem v3_eq (a b : V3) (hx : a.x = b.x) (hy : a.y = b.y)
    (hz : a.z = b.z) : a = b := by
  rcases a with ⟨ax, ay, az⟩
  rcases b with ⟨bx, byv, bz⟩
  simp_all

private local instance lawfulBEqV3Hierarchy : LawfulBEq V3 where
  rfl := by
    intro a
    rcases a with ⟨ax, ay, az⟩
    unfold instBEqV3 instBEqV3.beq
    simp
  eq_of_beq := v3_eq_of_beq

private local instance lawfulBEqFrameHierarchy : LawfulBEq Frame where
  rfl := by
    intro g
    rcases g with ⟨⟨px, py, pz⟩, sx, sy, sz⟩
    unfold instBEqFrame instBEqFrame.beq instBEqN3 instBEqN3.beq
      instBEqV3 instBEqV3.beq
    simp
  eq_of_beq := frame_eq_of_beq

/-! Structural equivariance of the literal signed-permutation action.  The
only finite computations below are the 48-element inverse-closure and inverse
identity checks; multiplication itself is proved coordinatewise. -/

private theorem frame_mul_sign_get (f f' : Frame) (i : Fin 3) :
    (f.mul f').sign.get i = f.sign.get i * f'.sign.get (f.perm.get i) := by
  fin_cases i <;> rfl

private theorem frame_mul_perm_get (f f' : Frame) (i : Fin 3) :
    (f.mul f').perm.get i = f'.perm.get (f.perm.get i) := by
  fin_cases i <;> rfl

/-- The real linear action represented by a literal frame. -/
def frameActRealVector (f : Frame) (x : E3) : E3 :=
  WithLp.toLp 2 fun i : Fin 3 => frameActReal f x i

@[simp] private theorem frameActRealVector_apply (f : Frame) (x : E3)
    (i : Fin 3) : frameActRealVector f x i = frameActReal f x i := rfl

/-- Literal frame multiplication represents composition of the corresponding
real coordinate actions. -/
theorem frameActReal_mul (f f' : Frame)
    (hf : ∀ i : Fin 3, f.perm.get i < 3)
    (hf' : ∀ i : Fin 3, f'.perm.get i < 3)
    (x : E3) (i : Fin 3) :
    frameActReal (f.mul f') x i =
      frameActReal f (frameActRealVector f' x) i := by
  let j : Fin 3 := ⟨f.perm.get i, hf i⟩
  have hj' : f'.perm.get j < 3 := hf' j
  rw [frameActReal, frame_mul_sign_get, frame_mul_perm_get,
    frameCoordinate_of_lt x hj']
  rw [frameActReal, frameCoordinate_of_lt (frameActRealVector f' x) (hf i)]
  simp only [frameActRealVector_apply]
  rw [frameActReal, frameCoordinate_of_lt x hj']
  change ((f.sign.get i * f'.sign.get (f.perm.get i) : Int) : Real) *
      x ⟨f'.perm.get j, hj'⟩ =
    (f.sign.get i : Real) * ((f'.sign.get (f.perm.get i) : Real) *
      x ⟨f'.perm.get j, hj'⟩)
  push_cast
  ring

private theorem allFrames_transpose_mem (f : Frame) (hf : f ∈ allFrames) :
    f.transpose ∈ allFrames := by
  have hcheck :
      allFrames.all (fun f => allFrames.contains f.transpose) = true := by decide
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hcheck f hf)

private theorem allFrames_mul_transpose (f : Frame) (hf : f ∈ allFrames) :
    f.mul f.transpose = identityFrame := by
  have hcheck :
      allFrames.all (fun f => f.mul f.transpose == identityFrame) = true := by decide
  exact frame_eq_of_beq (List.all_eq_true.mp hcheck f hf)

private theorem allFrames_transpose_mul (f : Frame) (hf : f ∈ allFrames) :
    f.transpose.mul f = identityFrame := by
  have hcheck :
      allFrames.all (fun f => f.transpose.mul f == identityFrame) = true := by decide
  exact frame_eq_of_beq (List.all_eq_true.mp hcheck f hf)

private theorem frameActReal_identity (x : E3) (i : Fin 3) :
    frameActReal identityFrame x i = x i := by
  fin_cases i <;> simp [frameActReal, frameCoordinate, identityFrame, fr, n3, v,
    N3.get, V3.get]

/-- Transpose is the inverse of the real signed-permutation action. -/
theorem frameActReal_transpose (f : Frame) (hf : f ∈ allFrames) (x : E3) :
    frameActRealVector f.transpose (frameActRealVector f x) = x := by
  apply PiLp.ext
  intro i
  have hm := frameActReal_mul f.transpose f
    (fun j => perm_lt_three (allFrames_transpose_mem f hf) j)
    (fun j => perm_lt_three hf j) x i
  rw [allFrames_transpose_mul f hf, frameActReal_identity] at hm
  exact hm.symm

private theorem frameActReal_transpose_right (f : Frame)
    (hf : f ∈ allFrames) (x : E3) :
    frameActRealVector f (frameActRealVector f.transpose x) = x := by
  apply PiLp.ext
  intro i
  have hm := frameActReal_mul f f.transpose
    (fun j => perm_lt_three hf j)
    (fun j => perm_lt_three (allFrames_transpose_mem f hf) j) x i
  rw [allFrames_mul_transpose f hf, frameActReal_identity] at hm
  exact hm.symm

private theorem frameActReal_scaledV3_one (f : Frame)
    (hf : ∀ i : Fin 3, f.perm.get i < 3) (a : V3) :
    frameActRealVector f (scaledV3 1 a) = scaledV3 1 (f.act a) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · have hp := hf (0 : Fin 3)
    change f.perm.x < 3 at hp
    simp only [frameActRealVector_apply]
    unfold frameActReal Frame.act scaledV3
    simp only [V3.get, N3.get]
    interval_cases f.perm.x <;> simp [frameCoordinate, v]
  · have hp := hf (1 : Fin 3)
    change f.perm.y < 3 at hp
    simp only [frameActRealVector_apply]
    unfold frameActReal Frame.act scaledV3
    simp only [V3.get, N3.get]
    interval_cases f.perm.y <;> simp [frameCoordinate, v]
  · have hp := hf (2 : Fin 3)
    change f.perm.z < 3 at hp
    simp only [frameActRealVector_apply]
    unfold frameActReal Frame.act scaledV3
    simp only [V3.get, N3.get]
    interval_cases f.perm.z <;> simp [frameCoordinate, v]

private theorem v3_get_sub (a b : V3) (j : Nat) :
    (a.sub b).get j = a.get j - b.get j := by
  rcases j with (_ | j)
  · rfl
  rcases j with (_ | j)
  · rfl
  rfl

private theorem frame_act_sub (f : Frame) (a b : V3) :
    f.act (a.sub b) = (f.act a).sub (f.act b) := by
  apply v3_eq
  · change f.sign.x * (a.sub b).get f.perm.x =
      f.sign.x * a.get f.perm.x - f.sign.x * b.get f.perm.x
    rw [v3_get_sub]
    ring
  · change f.sign.y * (a.sub b).get f.perm.y =
      f.sign.y * a.get f.perm.y - f.sign.y * b.get f.perm.y
    rw [v3_get_sub]
    ring
  · change f.sign.z * (a.sub b).get f.perm.z =
      f.sign.z * a.get f.perm.z - f.sign.z * b.get f.perm.z
    rw [v3_get_sub]
    ring

private theorem pose_relative_shift (p q : Pose) :
    (p.relative q).shift = p.frame.transpose.act (q.shift.sub p.shift) := by
  unfold Pose.relative Pose.inverse Pose.transform
  change (p.frame.transpose.act p.shift).neg.add
      (p.frame.transpose.act q.shift) = _
  rw [frame_act_sub]
  apply v3_eq <;>
    simp [V3.add, V3.sub, V3.neg, V3.smul, v] <;> ring

private theorem realizesPose_linear_vector {g : RigidMotion} {p : Pose}
    (hg : RealizesPose g p) (x : E3) :
    g.linearIsometryEquiv x = frameActRealVector p.frame x := by
  apply PiLp.ext
  intro i
  exact hg.1 x i

private theorem realizesPose_origin_vector {g : RigidMotion} {p : Pose}
    (hg : RealizesPose g p) : g 0 = scaledV3 1 p.shift := by
  apply PiLp.ext
  intro i
  simpa [scaledV3] using hg.2 i

/-- Realized signed-permutation poses are equivariant under passage to the
relative affine motion. -/
theorem realizesPose_relative {g h : RigidMotion} {p q : Pose}
    (hg : RealizesPose g p) (hh : RealizesPose h q)
    (hpf : p.frame ∈ allFrames) (hqf : q.frame ∈ allFrames) :
    RealizesPose (relativeMotion g h) (p.relative q) := by
  constructor
  · intro x i
    have hlin :
        (relativeMotion g h).linearIsometryEquiv x =
          frameActRealVector (p.relative q).frame x := by
      apply g.linearIsometryEquiv.injective
      have hcomp :
          g.linearIsometryEquiv ((relativeMotion g h).linearIsometryEquiv x) =
            h.linearIsometryEquiv x := by
        change g.linearIsometryEquiv
            (g.linearIsometryEquiv.symm (h.linearIsometryEquiv x)) = _
        exact g.linearIsometryEquiv.apply_symm_apply _
      rw [hcomp, realizesPose_linear_vector hh]
      rw [realizesPose_linear_vector hg]
      unfold Pose.relative Pose.inverse Pose.transform
      change frameActRealVector q.frame x =
        frameActRealVector p.frame
          (frameActRealVector (p.frame.transpose.mul q.frame) x)
      have hmul := frameActReal_mul p.frame.transpose q.frame
        (fun j => perm_lt_three (allFrames_transpose_mem p.frame hpf) j)
        (fun j => perm_lt_three hqf j) x
      have hvecmul :
          frameActRealVector (p.frame.transpose.mul q.frame) x =
            frameActRealVector p.frame.transpose
              (frameActRealVector q.frame x) := by
        apply PiLp.ext
        intro j
        exact hmul j
      rw [hvecmul, frameActReal_transpose_right p.frame hpf]
    exact congrArg (fun y : E3 => y i) hlin
  · intro i
    have horigin :
        relativeMotion g h 0 = scaledV3 1 (p.relative q).shift := by
      apply g.injective
      have hcomp : g (relativeMotion g h 0) = h 0 := by
        change g (g⁻¹ (h 0)) = h 0
        exact g.apply_symm_apply _
      rw [hcomp, realizesPose_origin_vector hh]
      have hmap := g.map_vadd (0 : E3) (scaledV3 1 (p.relative q).shift)
      simp only [vadd_eq_add, add_zero] at hmap
      rw [hmap, realizesPose_linear_vector hg,
        realizesPose_origin_vector hg]
      rw [pose_relative_shift]
      change scaledV3 1 q.shift =
        frameActRealVector p.frame
          (scaledV3 1 (p.frame.transpose.act (q.shift.sub p.shift))) +
            scaledV3 1 p.shift
      rw [← frameActReal_scaledV3_one p.frame.transpose
        (fun j => perm_lt_three (allFrames_transpose_mem p.frame hpf) j)]
      rw [frameActReal_transpose_right p.frame hpf]
      symm
      apply PiLp.ext
      intro j
      fin_cases j <;> norm_num [scaledV3, V3.sub, V3.get, v]
    simpa [scaledV3] using congrArg (fun y : E3 => y i) horigin

/- [compile-fix begin: moved verbatim in functional form to
R44.Proved.ConcreteCompanions to break the final promoted import cycle]
private theorem nativeFeatureData_mem (r : Role) :
    nativeFeatureData r ∈ nativeFeatures := by
  have hr : r.val < nativeFeatures.length := by
    rw [native_features_length]
    exact r.isLt
  rw [show nativeFeatureData r = nativeFeatures[r.val] by
    simp [nativeFeatureData, getD, hr]]
  exact List.get_mem nativeFeatures ⟨r.val, hr⟩

private theorem frame_mem_of_registeredShellCellControls
    (hcontrols : registeredShellCellControlsCheck = true)
    {p : Pose} (hp : p ∈ legalContacts) : p.frame ∈ allFrames := by
  simp only [registeredShellCellControlsCheck, Bool.and_eq_true] at hcontrols
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hcontrols.1.1.2 p hp)

set_option maxHeartbeats 2000000 in
private theorem featureMateFormula_center8 {m : RigidMotion} {p : Pose}
    {r s : Role} (hpframe : p.frame ∈ allFrames) (hm : RealizesPose m p)
    (hf : FeatureMateFormula m r s) :
    (p.frame.act (nativeFeatureData s).center8).add (p.shift.smul 8) =
      (nativeFeatureData r).center8 := by
  rcases hm with ⟨hlin, horigin⟩
  rcases hf with ⟨_, _, _, hcenter⟩
  have hc (i : Fin 3) :
      (m 0) i = featureCenter r i -
        (m.linearIsometryEquiv (featureCenter s)) i := by
    rw [hcenter]
    rfl
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  rw [hlin (featureCenter s) 0] at hc0
  rw [hlin (featureCenter s) 1] at hc1
  rw [hlin (featureCenter s) 2] at hc2
  unfold allFrames at hpframe
  obtain ⟨perm, hperm, hpframe⟩ := List.mem_flatMap.mp hpframe
  obtain ⟨sign, hsign, hpframe⟩ := List.mem_map.mp hpframe
  rcases p with ⟨pf, ⟨tx, ty, tz⟩⟩
  simp only at hpframe
  subst pf
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    apply v3_eq <;>
    simp [featureCenter, scaledV3, frameActReal, frameCoordinate,
      Frame.act, N3.get, V3.add, V3.smul, V3.get, fr, n3, v,
      horigin] at hc0 hc1 hc2 ⊢ <;>
    apply Int.cast_injective (α := ℝ) <;>
    push_cast <;>
    linarith

set_option maxHeartbeats 2000000 in
private theorem featureMateFormula_normal {m : RigidMotion} {p : Pose}
    {r s : Role} (hpframe : p.frame ∈ allFrames) (hm : RealizesPose m p)
    (hf : FeatureMateFormula m r s) :
    p.frame.act (nativeFeatureData s).normal =
      (nativeFeatureData r).normal.neg := by
  rcases hm with ⟨hlin, _⟩
  rcases hf with ⟨_, _, hnormal, _⟩
  have hn (i : Fin 3) :
      featureNormal r i =
        -(m.linearIsometryEquiv (featureNormal s)) i := by
    rw [hnormal]
    rfl
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  rw [hlin (featureNormal s) 0] at hn0
  rw [hlin (featureNormal s) 1] at hn1
  rw [hlin (featureNormal s) 2] at hn2
  unfold allFrames at hpframe
  obtain ⟨perm, hperm, hpframe⟩ := List.mem_flatMap.mp hpframe
  obtain ⟨sign, hsign, hpframe⟩ := List.mem_map.mp hpframe
  rcases p with ⟨pf, pt⟩
  simp only at hpframe
  subst pf
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    apply v3_eq <;>
    simp [featureNormal, scaledV3, frameActReal, frameCoordinate,
      Frame.act, N3.get, V3.neg, V3.smul, V3.get, fr, n3, v]
      at hn0 hn1 hn2 ⊢ <;>
    norm_cast at hn0 hn1 hn2 <;>
    omega

private theorem featureMateFormula_coefficient {m : RigidMotion} {r s : Role}
    (hf : FeatureMateFormula m r s) :
    (nativeFeatureData s).coefficient =
      -(nativeFeatureData r).coefficient := by
  rcases hf with ⟨_, hcoeff, _, _⟩
  unfold profileCoefficient at hcoeff
  omega

/-- The literal panel table turns the centre, normal, and polarity equations
    of a legal complete-feature mate into ownership of that feature's unique
    far-side shell cell by the companion's baseline chair. -/
theorem formula_mate_owns_far_cell
    (hcontrols : registeredShellCellControlsCheck = true)
    {m : RigidMotion} {p : Pose} {r s : Role}
    (hp : p ∈ legalContacts) (hm : RealizesPose m p)
    (hf : FeatureMateFormula m r s) :
    featureFarCell (nativeFeatureData r) ∈ body p := by
  have hpframe := frame_mem_of_registeredShellCellControls hcontrols hp
  have hcenter := featureMateFormula_center8 hpframe hm hf
  have hnormal := featureMateFormula_normal hpframe hm hf
  have hcoeff := featureMateFormula_coefficient hf
  have hr := nativeFeatureData_mem r
  have hs := nativeFeatureData_mem s
  simp only [registeredShellCellControlsCheck, Bool.and_eq_true] at hcontrols
  have hpcheck := List.all_eq_true.mp hcontrols.1.2 p hp
  have hrcheck := List.all_eq_true.mp hpcheck (nativeFeatureData r) hr
  have hscheck := List.all_eq_true.mp hrcheck (nativeFeatureData s) hs
  simp [hcenter, hnormal, hcoeff] at hscheck
  exact hscheck
-/ -- [compile-fix end]

set_option maxHeartbeats 2000000 in
private theorem realized_cellCenter {m : RigidMotion} {p : Pose} {d : V3}
    (hpframe : p.frame ∈ allFrames) (hm : RealizesPose m p) :
    m (cellCenter d) = cellCenter (cellLower p.frame p.shift d) := by
  rcases hm with ⟨hlin, horigin⟩
  have hc (i : Fin 3) :
      (m (cellCenter d)) i =
        frameActReal p.frame (cellCenter d) i + (p.shift.get i : ℝ) := by
    have hmap := congrArg (fun y : E3 => y i)
      (m.map_vadd (0 : E3) (cellCenter d))
    simp only [vadd_eq_add, add_zero] at hmap
    rw [hmap]
    change (m.linearIsometryEquiv (cellCenter d)) i + (m 0) i = _
    rw [hlin, horigin]
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  unfold allFrames at hpframe
  obtain ⟨perm, hperm, hpframe⟩ := List.mem_flatMap.mp hpframe
  obtain ⟨sign, hsign, hpframe⟩ := List.mem_map.mp hpframe
  rcases p with ⟨pf, ⟨tx, ty, tz⟩⟩
  simp only at hpframe
  subst pf
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    apply PiLp.ext <;> intro i <;> fin_cases i <;>
    simp [cellCenter, cellLower, frameActReal, frameCoordinate,
      N3.get, V3.get, fr, n3, v] at hc0 hc1 hc2 ⊢ <;>
    linarith

/-- Realization of a literal pose transports every listed baseline body cell
    to the corresponding open unit-cell core of the moved carrier. -/
theorem body_cellCenter_mem_interior {m : RigidMotion} {p : Pose} {a : V3}
    (hpframe : p.frame ∈ allFrames) (hm : RealizesPose m p)
    (ha : a ∈ body p) : cellCenter a ∈ interior (m '' P) := by
  unfold body at ha
  rw [List.mem_eraseDups] at ha
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
  change cellCenter (cellLower p.frame p.shift d) ∈
    interior (m.toHomeomorph '' P)
  rw [← m.toHomeomorph.image_interior]
  refine ⟨cellCenter d, ?_, realized_cellCenter hpframe hm⟩
  exact interior_mono (by intro x hx; exact ⟨d, hd, hx⟩)
    (cellCenter_mem_interior_unitCube d)

/-- In a registered feature component, two placements whose realized
    baseline bodies own the same integral unit cell are the same placement.
    This is the disjoint-retained-core step used by the first-shell bridge. -/
theorem component_cell_owner_unique {T : Tiling Q} {g h k A : RigidMotion}
    (hAg : A * g = 1)
    (hh : h ∈ T.placements) (hk : k ∈ T.placements)
    (hhcomp : SameFeatureComponent T g h)
    (hkcomp : SameFeatureComponent T g k)
    (hdisjoint : ∀ ⦃u w : RigidMotion⦄,
      u ∈ T.placements → w ∈ T.placements →
      SameFeatureComponent T g u → SameFeatureComponent T g w → u ≠ w →
      Disjoint (interior ((A * u) '' P)) (interior ((A * w) '' P)))
    {ph pk : Pose} {c : V3}
    (hfh : ph.frame ∈ allFrames) (hfk : pk.frame ∈ allFrames)
    (hrh : RealizesPose (relativeMotion g h) ph)
    (hrk : RealizesPose (relativeMotion g k) pk)
    (hch : c ∈ body ph) (hck : c ∈ body pk) : h = k := by
  have hnormalize (u : RigidMotion) : A * u = relativeMotion g u := by
    calc
      A * u = (A * g) * (g⁻¹ * u) := by group
      _ = relativeMotion g u := by rw [hAg]; simp [relativeMotion]
  by_contra hne
  have hd := hdisjoint hh hk hhcomp hkcomp hne
  have hcenterH : cellCenter c ∈ interior ((A * h) '' P) := by
    rw [hnormalize]
    exact body_cellCenter_mem_interior hfh hrh hch
  have hcenterK : cellCenter c ∈ interior ((A * k) '' P) := by
    rw [hnormalize]
    exact body_cellCenter_mem_interior hfk hrk hck
  exact Set.disjoint_left.1 hd hcenterH hcenterK

private def cc (s a t : Int) : Int :=
  (if s == 1 then a else -a - 1) + t

private theorem cc_comp {gs hs a u t : Int}
    (hgs : gs = 1 ∨ gs = -1) (hhs : hs = 1 ∨ hs = -1) :
    cc (gs * hs) a (t + gs * u) = cc gs (cc hs a u) t := by
  rcases hgs with rfl | rfl <;> rcases hhs with rfl | rfl <;>
    simp [cc] <;> ring

private theorem cellLower_comp (g h : Frame) (t u d : V3)
    (hg : FrameData g) (hh : FrameData h) :
    cellLower (g.mul h) (t.add (g.act u)) d =
      cellLower g t (cellLower h u d) := by
  rcases g with ⟨⟨g0, g1, g2⟩, ⟨s0, s1, s2⟩⟩
  rcases h with ⟨⟨h0, h1, h2⟩, ⟨r0, r1, r2⟩⟩
  rcases t with ⟨tx, ty, tz⟩
  rcases u with ⟨ux, uy, uz⟩
  rcases d with ⟨dx, dy, dz⟩
  have hg0 : g0 < 3 := hg.px
  have hg1 : g1 < 3 := hg.py
  have hg2 : g2 < 3 := hg.pz
  apply v3_eq
  · interval_cases g0 <;>
      simp [cellLower, Frame.mul, Frame.act, N3.get, V3.get, V3.add,
        fr, n3, v] at ⊢ <;>
      first | simpa [cc] using (cc_comp hg.sx hh.sx) |
        simpa [cc] using (cc_comp hg.sx hh.sy) |
        simpa [cc] using (cc_comp hg.sx hh.sz)
  · interval_cases g1 <;>
      simp [cellLower, Frame.mul, Frame.act, N3.get, V3.get, V3.add,
        fr, n3, v] at ⊢ <;>
      first | simpa [cc] using (cc_comp hg.sy hh.sx) |
        simpa [cc] using (cc_comp hg.sy hh.sy) |
        simpa [cc] using (cc_comp hg.sy hh.sz)
  · interval_cases g2 <;>
      simp [cellLower, Frame.mul, Frame.act, N3.get, V3.get, V3.add,
        fr, n3, v] at ⊢ <;>
      first | simpa [cc] using (cc_comp hg.sz hh.sx) |
        simpa [cc] using (cc_comp hg.sz hh.sy) |
        simpa [cc] using (cc_comp hg.sz hh.sz)

private theorem allFrames_mul_child_mem {g : Frame} (hg : g ∈ allFrames)
    {c : Pose} (hc : c ∈ children) : g.mul c.frame ∈ allFrames := by
  have hcheck :
      allFrames.all (fun g => children.all fun c =>
        allFrames.contains (g.mul c.frame)) = true := by decide
  have hgcheck := List.all_eq_true.mp hcheck g hg
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hgcheck c hc)

private theorem root_cells_iff (hchildren : childrenPartitionCheck = true)
    {a : V3} :
    a ∈ children.flatMap body ↔ a ∈ doubledChairCells := by
  simp only [childrenPartitionCheck, Bool.and_eq_true] at hchildren
  have hset := hchildren.2
  simp only [setEq, Bool.and_eq_true, subset] at hset
  constructor
  · intro ha
    apply List.contains_iff_mem.mp
    exact List.all_eq_true.mp hset.1 a ha
  · intro ha
    apply List.contains_iff_mem.mp
    exact List.all_eq_true.mp hset.2 a ha

private theorem body_mem_iff {p : Pose} {a : V3} :
    a ∈ body p ↔ ∃ d ∈ chairCells, a = cellLower p.frame p.shift d := by
  unfold body
  simp [eq_comm]

private theorem cellLower_injective_hierarchy {f : Frame}
    (hf : f ∈ allFrames) (t : V3) :
    Function.Injective (cellLower f t) := by
  intro a b hab
  unfold allFrames at hf
  obtain ⟨perm, hperm, hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨sign, hsign, rfl⟩ := List.mem_map.mp hf
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases a with ⟨ax, ay, az⟩ <;> rcases b with ⟨bx, byv, bz⟩ <;>
    rcases t with ⟨tx, ty, tz⟩ <;>
    simp [cellLower, N3.get, V3.get, fr, n3, v] at hab ⊢ <;> omega

private theorem eraseDups_nodup_hierarchy {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ xs : List α, xs.eraseDups.Nodup
  | [] => by simp
  | a :: xs => by
      rw [List.eraseDups_cons]
      constructor
      · intro b hb hab
        rw [List.mem_eraseDups] at hb
        subst b
        simp at hb
      · exact eraseDups_nodup_hierarchy (xs.filter fun b => !b == a)
termination_by xs => xs.length
decreasing_by
  have h := List.length_filter_le (fun b => !b == a) xs
  simp only [List.length_cons]
  omega

private theorem body_nodup_hierarchy (p : Pose) : (body p).Nodup := by
  unfold body
  exact eraseDups_nodup_hierarchy _

private theorem body_nonempty_hierarchy (p : Pose) : ∃ a, a ∈ body p := by
  refine ⟨cellLower p.frame p.shift (v 0 0 0), ?_⟩
  apply body_mem_iff.mpr
  exact ⟨v 0 0 0, by decide, rfl⟩

private theorem body_length_seven_hierarchy {p : Pose}
    (hf : p.frame ∈ allFrames) : (body p).length = 7 := by
  let source := chairCells.map (cellLower p.frame p.shift)
  have hsource : source.Nodup := by
    exact (by decide : chairCells.Nodup).map
      (cellLower_injective_hierarchy hf p.shift)
  have hperm : (body p).Perm source := by
    apply (List.perm_ext_iff_of_nodup (body_nodup_hierarchy p) hsource).mpr
    intro a
    simp [source, body]
  calc
    (body p).length = source.length := hperm.length_eq
    _ = chairCells.length := by simp [source]
    _ = 7 := by decide

private theorem flatMap_body_length_seven {xs : List Pose}
    (hframes : ∀ p ∈ xs, p.frame ∈ allFrames) :
    (xs.flatMap body).length = 7 * xs.length := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      · rw [body_length_seven_hierarchy (hframes p (by simp))]
        simp [Nat.mul_add, Nat.add_comm]
      · intro q hq
        exact hframes q (by simp [hq])

private theorem nodup_of_mem_iff_length {α : Type*} [DecidableEq α]
    {xs ys : List α} (hy : ys.Nodup)
    (hmem : ∀ a, a ∈ xs ↔ a ∈ ys) (hlen : xs.length = ys.length) :
    xs.Nodup := by
  have heq : xs.toFinset = ys.toFinset := by
    ext a
    simp only [List.mem_toFinset]
    exact hmem a
  have hcard : xs.toFinset.card = xs.length := calc
    xs.toFinset.card = ys.toFinset.card := congrArg Finset.card heq
    _ = ys.length := List.toFinset_card_of_nodup hy
    _ = xs.length := hlen.symm
  rw [List.card_toFinset] at hcard
  apply List.dedup_eq_self.mp
  exact (List.dedup_sublist xs).eq_of_length hcard

private theorem refine_frame_mem_allFrames {p q : Pose}
    (hp : p.frame ∈ allFrames) (hq : q ∈ refine p) :
    q.frame ∈ allFrames := by
  unfold refine at hq
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
  exact allFrames_mul_child_mem hp hc

/-- Equivariance of the literal root dissection at an arbitrary signed frame.
    Since `body` records lower cube corners, a reversed coordinate uses the
    `-a-1` branch of `cellLower`. -/
theorem cells_refine (hchildren : childrenPartitionCheck = true)
    (p : Pose) (hpFrame : p.frame ∈ allFrames) (a : V3) :
    a ∈ (refine p).flatMap body ↔
      ∃ c ∈ doubledChairCells,
        a = cellLower p.frame (p.shift.smul 2) c := by
  constructor
  · intro ha
    obtain ⟨q, hq, haq⟩ := List.mem_flatMap.mp ha
    unfold refine at hq
    obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hq
    obtain ⟨d, hd, had⟩ := body_mem_iff.mp haq
    let c := cellLower child.frame child.shift d
    have hcroot : c ∈ children.flatMap body := by
      apply List.mem_flatMap.mpr
      refine ⟨child, hchild, ?_⟩
      apply body_mem_iff.mpr
      exact ⟨d, hd, rfl⟩
    refine ⟨c, root_cells_iff hchildren |>.mp hcroot, ?_⟩
    rw [had]
    dsimp only [c]
    exact cellLower_comp p.frame child.frame (p.shift.smul 2) child.shift d
      (allFrames_data hpFrame) (childrenFrames_data hchild)
  · rintro ⟨c, hc, rfl⟩
    have hcroot : c ∈ children.flatMap body :=
      root_cells_iff hchildren |>.mpr hc
    obtain ⟨child, hchild, hcchild⟩ := List.mem_flatMap.mp hcroot
    obtain ⟨d, hd, hcd⟩ := body_mem_iff.mp hcchild
    apply List.mem_flatMap.mpr
    refine ⟨po (p.frame.mul child.frame)
        ((p.shift.smul 2).add (p.frame.act child.shift)), ?_, ?_⟩
    · unfold refine
      apply List.mem_map.mpr
      exact ⟨child, hchild, rfl⟩
    · apply body_mem_iff.mpr
      refine ⟨d, hd, ?_⟩
      rw [hcd]
      exact (cellLower_comp p.frame child.frame (p.shift.smul 2) child.shift d
        (allFrames_data hpFrame) (childrenFrames_data hchild)).symm

private theorem refine_cells_nodup
    (hchildren : childrenPartitionCheck = true)
    (p : Pose) (hp : p.frame ∈ allFrames) :
    ((refine p).flatMap body).Nodup := by
  let transported := doubledChairCells.map
    (cellLower p.frame (p.shift.smul 2))
  have htransported : transported.Nodup := by
    exact (by decide : doubledChairCells.Nodup).map
      (cellLower_injective_hierarchy hp (p.shift.smul 2))
  apply nodup_of_mem_iff_length htransported
  · intro a
    rw [cells_refine hchildren p hp a]
    simp [transported, eq_comm]
  · rw [flatMap_body_length_seven]
    · rw [List.length_map]
      change 7 * (refine p).length = doubledChairCells.length
      simp only [refine, List.length_map]
      decide
    · intro q hq
      exact refine_frame_mem_allFrames hp hq

private theorem childFrame_mem_allFrames {c : Pose} (hc : c ∈ children) :
    c.frame ∈ allFrames := by
  have hcheck : children.all (fun c => allFrames.contains c.frame) = true := by
    decide
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hcheck c hc)

private theorem refine_root : refine rootPose = children := by decide

private theorem v3_get_smul (a : V3) (k : Int) (i : Nat) :
    (a.smul k).get i = k * a.get i := by
  rcases a with ⟨ax, ay, az⟩
  rcases i with _ | i
  · rfl
  · rcases i with _ | i <;> rfl

private theorem frameAct_smul (g : Frame) (a : V3) (k : Int) :
    g.act (a.smul k) = (g.act a).smul k := by
  apply v3_eq <;>
    simp only [Frame.act, v] <;>
    rw [v3_get_smul] <;>
    simp [V3.smul, v] <;> ring

private theorem doubled_refine_shift (g : Frame) (t u : V3) :
    ((t.smul 2).add (g.act u)).smul 2 =
      (t.smul 4).add (g.act (u.smul 2)) := by
  rw [frameAct_smul]
  rcases t with ⟨tx, ty, tz⟩
  rcases g.act u with ⟨ux, uy, uz⟩
  apply v3_eq <;> simp [V3.smul, V3.add, v] <;> ring

/-- Two applications of `cells_refine`: all lower corners in a double
    refinement are the signed-frame transport of the root double refinement,
    with the parent shift multiplied by four. -/
theorem cells_two_refine (hchildren : childrenPartitionCheck = true)
    (p : Pose) (hpFrame : p.frame ∈ allFrames) (a : V3) :
    a ∈ twoRefinementCells p ↔
      ∃ c ∈ twoRefinementCells rootPose,
        a = cellLower p.frame (p.shift.smul 4) c := by
  constructor
  · intro ha
    obtain ⟨q, hq, haq⟩ := List.mem_flatMap.mp ha
    unfold refine at hq
    obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hq
    have hqFrame : (p.frame.mul child.frame) ∈ allFrames :=
      allFrames_mul_child_mem hpFrame hchild
    obtain ⟨c, hc, hac⟩ :=
      (cells_refine hchildren
        (po (p.frame.mul child.frame)
          ((p.shift.smul 2).add (p.frame.act child.shift))) hqFrame a).mp haq
    let rootCell := cellLower child.frame (child.shift.smul 2) c
    have hrootCell : rootCell ∈ twoRefinementCells rootPose := by
      unfold twoRefinementCells
      rw [refine_root]
      apply List.mem_flatMap.mpr
      refine ⟨child, hchild, ?_⟩
      apply (cells_refine hchildren child (childFrame_mem_allFrames hchild)
        rootCell).mpr
      exact ⟨c, hc, rfl⟩
    refine ⟨rootCell, hrootCell, ?_⟩
    rw [hac]
    dsimp only [rootCell]
    change cellLower (p.frame.mul child.frame)
      (((p.shift.smul 2).add (p.frame.act child.shift)).smul 2) c = _
    rw [doubled_refine_shift]
    exact cellLower_comp p.frame child.frame (p.shift.smul 4)
      (child.shift.smul 2) c (allFrames_data hpFrame)
      (childrenFrames_data hchild)
  · rintro ⟨rootCell, hrootCell, rfl⟩
    unfold twoRefinementCells at hrootCell ⊢
    rw [refine_root] at hrootCell
    obtain ⟨child, hchild, hc⟩ := List.mem_flatMap.mp hrootCell
    obtain ⟨c, hc, hrootEq⟩ :=
      (cells_refine hchildren child (childFrame_mem_allFrames hchild)
        rootCell).mp hc
    apply List.mem_flatMap.mpr
    refine ⟨po (p.frame.mul child.frame)
        ((p.shift.smul 2).add (p.frame.act child.shift)), ?_, ?_⟩
    · unfold refine
      apply List.mem_map.mpr
      exact ⟨child, hchild, rfl⟩
    · apply (cells_refine hchildren
        (po (p.frame.mul child.frame)
          ((p.shift.smul 2).add (p.frame.act child.shift)))
        (allFrames_mul_child_mem hpFrame hchild)
        (cellLower p.frame (p.shift.smul 4) rootCell)).mpr
      refine ⟨c, hc, ?_⟩
      rw [hrootEq]
      change _ = cellLower (p.frame.mul child.frame)
        (((p.shift.smul 2).add (p.frame.act child.shift)).smul 2) c
      rw [doubled_refine_shift]
      exact (cellLower_comp p.frame child.frame (p.shift.smul 4)
        (child.shift.smul 2) c (allFrames_data hpFrame)
        (childrenFrames_data hchild)).symm

private theorem blockOffset_preimage
    (haction : blockOffsetActionCheck = true)
    {g : Frame} (hg : g ∈ allFrames)
    {b : V3} (hb : b ∈ fourBlockOffsets) :
    ∃ c ∈ fourBlockOffsets,
      cellLower g (v 0 0 0) c =
        ((cellLower g (v 0 0 0) (v 0 0 0)).smul 4 |>.add b) := by
  have hgcheck := List.all_eq_true.mp haction g hg
  have hbcheck := List.all_eq_true.mp hgcheck b hb
  obtain ⟨c, hc, heq⟩ := List.any_eq_true.mp hbcheck
  exact ⟨c, hc, v3_eq_of_beq heq⟩

private theorem v3_get_add (a b : V3) (i : Nat) :
    (a.add b).get i = a.get i + b.get i := by
  rcases a with ⟨ax, ay, az⟩
  rcases b with ⟨bx, byv, bz⟩
  rcases i with _ | i
  · rfl
  · rcases i with _ | i <;> rfl

private theorem cellLower_get (g : Frame) (t a : V3) (i : Nat) (hi : i < 3) :
    (cellLower g t a).get i =
      (if g.sign.get i == 1 then a.get (g.perm.get i)
       else -a.get (g.perm.get i) - 1) + t.get i := by
  interval_cases i <;> rfl

private theorem cellLower_four_block_get {g : Frame} {a b c t : V3}
    (hzero : cellLower g (v 0 0 0) c =
      ((cellLower g (v 0 0 0) (v 0 0 0)).smul 4 |>.add b))
    (i : Nat) (hi : i < 3) :
    (cellLower g (t.smul 4) ((a.smul 4).add c)).get i =
      (((cellLower g t a).smul 4).add b).get i := by
  have h := congrArg (fun z : V3 => z.get i) hzero
  rw [cellLower_get g (v 0 0 0) c i hi,
    v3_get_add, v3_get_smul,
    cellLower_get g (v 0 0 0) (v 0 0 0) i hi] at h
  rw [cellLower_get g (t.smul 4) ((a.smul 4).add c) i hi]
  rw [v3_get_add, v3_get_smul]
  rw [v3_get_add]
  rw [v3_get_smul (cellLower g t a) 4 i]
  rw [cellLower_get g t a i hi]
  have hzeroPerm : (v 0 0 0).get (g.perm.get i) = 0 := by
    generalize g.perm.get i = j
    rcases j with _ | j
    · rfl
    · rcases j with _ | j <;> rfl
  have hzeroI : (v 0 0 0).get i = 0 := by
    rcases i with _ | i
    · rfl
    · rcases i with _ | i <;> rfl
  rw [hzeroPerm, hzeroI] at h
  rw [v3_get_smul t 4 i]
  by_cases hs : g.sign.get i == 1
  · simp only [hs, if_true] at h ⊢
    simp at h ⊢
    omega
  · simp only [hs, if_false] at h ⊢
    simp at h ⊢
    omega

private theorem cellLower_four_block {g : Frame} {a b c t : V3}
    (hzero : cellLower g (v 0 0 0) c =
      ((cellLower g (v 0 0 0) (v 0 0 0)).smul 4 |>.add b)) :
    cellLower g (t.smul 4) ((a.smul 4).add c) =
      ((cellLower g t a).smul 4 |>.add b) := by
  apply v3_eq
  · exact cellLower_four_block_get hzero 0 (by omega)
  · exact cellLower_four_block_get hzero 1 (by omega)
  · exact cellLower_four_block_get hzero 2 (by omega)

private theorem bit_action_image {g : Frame} (hg : g ∈ allFrames)
    {c : V3} (hc : c ∈ bits) :
    ∃ b ∈ bits,
      cellLower g (v 0 0 0) c =
        ((cellLower g (v 0 0 0) (v 0 0 0)).smul 2 |>.add b) := by
  have hcheck : allFrames.all (fun f => bits.all fun c =>
      bits.any fun b =>
        cellLower f (v 0 0 0) c ==
          ((cellLower f (v 0 0 0) (v 0 0 0)).smul 2 |>.add b)) = true := by
    decide
  have hgcheck := List.all_eq_true.mp hcheck g hg
  have hccheck := List.all_eq_true.mp hgcheck c hc
  obtain ⟨b, hb, heq⟩ := List.any_eq_true.mp hccheck
  exact ⟨b, hb, v3_eq_of_beq heq⟩

private theorem cellLower_two_block_get {g : Frame} {a b c t : V3}
    (hzero : cellLower g (v 0 0 0) c =
      ((cellLower g (v 0 0 0) (v 0 0 0)).smul 2 |>.add b))
    (i : Nat) (hi : i < 3) :
    (cellLower g (t.smul 2) ((a.smul 2).add c)).get i =
      (((cellLower g t a).smul 2).add b).get i := by
  have h := congrArg (fun z : V3 => z.get i) hzero
  rw [cellLower_get g (v 0 0 0) c i hi,
    v3_get_add, v3_get_smul,
    cellLower_get g (v 0 0 0) (v 0 0 0) i hi] at h
  rw [cellLower_get g (t.smul 2) ((a.smul 2).add c) i hi]
  rw [v3_get_add, v3_get_smul]
  rw [v3_get_add]
  rw [v3_get_smul (cellLower g t a) 2 i]
  rw [cellLower_get g t a i hi]
  have hzeroPerm : (v 0 0 0).get (g.perm.get i) = 0 := by
    generalize g.perm.get i = j
    rcases j with _ | j
    · rfl
    · rcases j with _ | j <;> rfl
  have hzeroI : (v 0 0 0).get i = 0 := by
    rcases i with _ | i
    · rfl
    · rcases i with _ | i <;> rfl
  rw [hzeroPerm, hzeroI] at h
  rw [v3_get_smul t 2 i]
  by_cases hs : g.sign.get i == 1
  · simp only [hs, if_true] at h ⊢
    simp at h ⊢
    omega
  · simp only [hs, if_false] at h ⊢
    simp at h ⊢
    omega

private theorem cellLower_two_block {g : Frame} {a b c t : V3}
    (hzero : cellLower g (v 0 0 0) c =
      ((cellLower g (v 0 0 0) (v 0 0 0)).smul 2 |>.add b)) :
    cellLower g (t.smul 2) ((a.smul 2).add c) =
      ((cellLower g t a).smul 2 |>.add b) := by
  apply v3_eq
  · exact cellLower_two_block_get hzero 0 (by omega)
  · exact cellLower_two_block_get hzero 1 (by omega)
  · exact cellLower_two_block_get hzero 2 (by omega)

private theorem refined_cell_in_parent_block
    (hchildren : childrenPartitionCheck = true)
    {p : Pose} (hp : p.frame ∈ allFrames) {x : V3}
    (hx : x ∈ (refine p).flatMap body) :
    ∃ a ∈ body p, ∃ b ∈ bits, x = (a.smul 2).add b := by
  obtain ⟨c, hc, rfl⟩ := (cells_refine hchildren p hp x).mp hx
  unfold doubledChairCells at hc
  obtain ⟨d, hd, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  obtain ⟨b, hb, hzero⟩ := bit_action_image hp he
  refine ⟨cellLower p.frame p.shift d, body_mem_iff.mpr ⟨d, hd, rfl⟩,
    b, hb, ?_⟩
  exact cellLower_two_block hzero

private theorem bit_coordinate_bounds {b : V3} (hb : b ∈ bits) :
    0 ≤ b.x ∧ b.x < 2 ∧ 0 ≤ b.y ∧ b.y < 2 ∧ 0 ≤ b.z ∧ b.z < 2 := by
  simp [bits, v] at hb
  rcases hb with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    norm_num

private theorem two_block_base_unique {a d b c : V3}
    (hb : b ∈ bits) (hc : c ∈ bits)
    (heq : (a.smul 2).add b = (d.smul 2).add c) : a = d := by
  obtain ⟨hbx0, hbx2, hby0, hby2, hbz0, hbz2⟩ := bit_coordinate_bounds hb
  obtain ⟨hcx0, hcx2, hcy0, hcy2, hcz0, hcz2⟩ := bit_coordinate_bounds hc
  have hx := congrArg V3.x heq
  have hy := congrArg V3.y heq
  have hz := congrArg V3.z heq
  apply v3_eq <;>
    simp only [V3.smul, V3.add, v] at hx hy hz ⊢ <;> omega

private theorem refine_cells_disjoint_of_body_disjoint
    (hchildren : childrenPartitionCheck = true)
    {p q : Pose} (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames)
    (hpq : (body p).Disjoint (body q)) :
    ((refine p).flatMap body).Disjoint ((refine q).flatMap body) := by
  rw [List.disjoint_left] at hpq ⊢
  intro x hxp hxq
  obtain ⟨a, ha, b, hb, hab⟩ :=
    refined_cell_in_parent_block hchildren hp hxp
  obtain ⟨d, hd, c, hc, hdc⟩ :=
    refined_cell_in_parent_block hchildren hq hxq
  have had : a = d := two_block_base_unique hb hc (hab.symm.trans hdc)
  exact hpq ha (had ▸ hd)

private theorem pairwise_rel_of_mem_ne {α : Type*} {R : α → α → Prop}
    (hsym : ∀ {a b}, R a b → R b a) {xs : List α}
    (hpair : xs.Pairwise R) {a b : α}
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) : R a b := by
  induction xs generalizing a b with
  | nil => simp at ha
  | cons x xs ih =>
      rw [List.pairwise_cons] at hpair
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact False.elim (hne rfl)
        · exact hpair.1 b hb
      · rcases hb with rfl | hb
        · exact hsym (hpair.1 a ha)
        · exact ih hpair.2 ha hb hne

private theorem refine_flat_cells_nodup
    (hchildren : childrenPartitionCheck = true)
    {xs : List Pose} (hframes : ∀ p ∈ xs, p.frame ∈ allFrames)
    (hcells : (xs.flatMap body).Nodup) :
    ((xs.flatMap refine).flatMap body).Nodup := by
  rw [List.flatMap_assoc]
  apply List.nodup_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro p hp
    exact refine_cells_nodup hchildren p (hframes p hp)
  · have hpair := (List.nodup_flatMap.mp hcells).2
    exact hpair.imp_of_mem fun hp hq hpq =>
      refine_cells_disjoint_of_body_disjoint hchildren
        (hframes _ hp) (hframes _ hq) hpq

private theorem hashDedup_nodup_pose (xs : List Pose) :
    (hashDedup xs).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  unfold hashDedup
  exact Std.HashSet.distinct_toList.imp fun hab heq => by
    subst heq
    simpa using hab

private theorem hashDedup_flat_cells_nodup {xs : List Pose}
    (hcells : (xs.flatMap body).Nodup) :
    ((hashDedup xs).flatMap body).Nodup := by
  have hsource := List.nodup_flatMap.mp hcells
  apply List.nodup_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro p hp
    exact hsource.1 p (mem_hashDedup_iff.mp hp)
  · have hne := List.nodup_iff_pairwise_ne.mp (hashDedup_nodup_pose xs)
    exact hne.imp_of_mem fun hp hq hpq =>
      pairwise_rel_of_mem_ne (fun h => h.symm) hsource.2
        (mem_hashDedup_iff.mp hp) (mem_hashDedup_iff.mp hq) hpq

private theorem twoRefinements_flat_cells_nodup
    (hchildren : childrenPartitionCheck = true)
    {xs : List Pose} (hframes : ∀ p ∈ xs, p.frame ∈ allFrames)
    (hcells : (xs.flatMap body).Nodup) :
    ((twoRefinements xs).flatMap body).Nodup := by
  have hfirst : ((xs.flatMap refine).flatMap body).Nodup :=
    refine_flat_cells_nodup hchildren hframes hcells
  have hfirstFrames : ∀ q ∈ xs.flatMap refine, q.frame ∈ allFrames := by
    intro q hq
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.mp hq
    exact refine_frame_mem_allFrames (hframes p hp) hq
  have hsecond :
      (((xs.flatMap refine).flatMap refine).flatMap body).Nodup :=
    refine_flat_cells_nodup hchildren hfirstFrames hfirst
  unfold twoRefinements
  exact hashDedup_flat_cells_nodup hsecond

private theorem two_refinement_covers_cell
    (hchildren : childrenPartitionCheck = true)
    (hblock : hierarchyBlockCoverCheck = true)
    (haction : blockOffsetActionCheck = true)
    (p : Pose) (hpFrame : p.frame ∈ allFrames)
    (a : V3) (ha : a ∈ body p)
    (b : V3) (hb : b ∈ fourBlockOffsets) :
    (a.smul 4).add b ∈ twoRefinementCells p := by
  obtain ⟨d, hd, had⟩ := body_mem_iff.mp ha
  obtain ⟨c, hc, hzero⟩ := blockOffset_preimage haction hpFrame hb
  let rootCell := (d.smul 4).add c
  have hrootFour : rootCell ∈ fourBlockCells := by
    unfold fourBlockCells
    apply List.mem_flatMap.mpr
    refine ⟨d, hd, ?_⟩
    apply List.mem_map.mpr
    exact ⟨c, hc, rfl⟩
  have hroot : rootCell ∈ twoRefinementCells rootPose := by
    unfold hierarchyBlockCoverCheck subset at hblock
    apply List.contains_iff_mem.mp
    exact List.all_eq_true.mp hblock rootCell hrootFour
  apply (cells_two_refine hchildren p hpFrame ((a.smul 4).add b)).mpr
  refine ⟨rootCell, hroot, ?_⟩
  rw [had]
  exact (cellLower_four_block hzero).symm

private theorem fourBlock_of_lt_four {x y z : Nat}
    (hx : x < 4) (hy : y < 4) (hz : z < 4) :
    v (Int.ofNat x) (Int.ofNat y) (Int.ofNat z) ∈ fourBlockOffsets := by
  have hcheck :
      (List.range 4).all (fun x => (List.range 4).all fun y =>
        (List.range 4).all fun z =>
          fourBlockOffsets.contains
            (v (Int.ofNat x) (Int.ofNat y) (Int.ofNat z))) = true := by decide
  have hxcheck := List.all_eq_true.mp hcheck x (List.mem_range.mpr hx)
  have hycheck := List.all_eq_true.mp hxcheck y (List.mem_range.mpr hy)
  have hzcheck := List.all_eq_true.mp hycheck z (List.mem_range.mpr hz)
  exact List.contains_iff_mem.mp hzcheck

def hierarchyCubeCells (n : Nat) : List V3 :=
  (List.range (4 ^ n)).flatMap fun x =>
    (List.range (4 ^ n)).flatMap fun y =>
      (List.range (4 ^ n)).map fun z =>
        v (Int.ofNat x) (Int.ofNat y) (Int.ofNat z)

private theorem hierarchyCubeCell_mem {n x y z : Nat}
    (hx : x < 4 ^ n) (hy : y < 4 ^ n) (hz : z < 4 ^ n) :
    v (Int.ofNat x) (Int.ofNat y) (Int.ofNat z) ∈ hierarchyCubeCells n := by
  unfold hierarchyCubeCells
  apply List.mem_flatMap.mpr
  refine ⟨x, List.mem_range.mpr hx, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨y, List.mem_range.mpr hy, ?_⟩
  apply List.mem_map.mpr
  exact ⟨z, List.mem_range.mpr hz, rfl⟩

private theorem hierarchyPoseLevel_frames :
    ∀ n : Nat, ∀ p ∈ hierarchyPoseLevel n, p.frame ∈ allFrames := by
  intro n
  induction n with
  | zero =>
      intro p hp
      simp only [hierarchyPoseLevel, List.mem_singleton] at hp
      subst p
      decide
  | succ n ih =>
      intro p hp
      change p ∈ twoRefinements (hierarchyPoseLevel n) at hp
      unfold twoRefinements at hp
      unfold hashDedup at hp
      rw [Std.HashSet.mem_toList, Std.HashSet.mem_ofList,
        List.contains_iff_mem] at hp
      obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.mp hp
      obtain ⟨r, hr, hqr⟩ := List.mem_flatMap.mp hq
      unfold refine at hqr hpq
      obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.mp hqr
      obtain ⟨c₂, hc₂, rfl⟩ := List.mem_map.mp hpq
      exact allFrames_mul_child_mem
        (allFrames_mul_child_mem (ih r hr) hc₁) hc₂

private theorem hierarchyCubeCells_covered
    (hchildren : childrenPartitionCheck = true)
    (hblock : hierarchyBlockCoverCheck = true)
    (haction : blockOffsetActionCheck = true) :
    ∀ n : Nat, ∀ a ∈ hierarchyCubeCells n,
      a ∈ (hierarchyPoseLevel n).flatMap body := by
  intro n
  induction n with
  | zero =>
      intro a ha
      simp [hierarchyCubeCells] at ha
      subst a
      decide
  | succ n ih =>
      intro a ha
      unfold hierarchyCubeCells at ha
      obtain ⟨x, hx, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨y, hy, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
      have hxlt : x < 4 ^ (n + 1) := List.mem_range.mp hx
      have hylt : y < 4 ^ (n + 1) := List.mem_range.mp hy
      have hzlt : z < 4 ^ (n + 1) := List.mem_range.mp hz
      have hxp : x / 4 < 4 ^ n := by
        apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)).2
        simpa [pow_succ] using hxlt
      have hyp : y / 4 < 4 ^ n := by
        apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)).2
        simpa [pow_succ] using hylt
      have hzp : z / 4 < 4 ^ n := by
        apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)).2
        simpa [pow_succ] using hzlt
      let parentCell := v (Int.ofNat (x / 4)) (Int.ofNat (y / 4))
        (Int.ofNat (z / 4))
      let offset := v (Int.ofNat (x % 4)) (Int.ofNat (y % 4))
        (Int.ofNat (z % 4))
      have hparentCube : parentCell ∈ hierarchyCubeCells n := by
        exact hierarchyCubeCell_mem hxp hyp hzp
      have hparent := ih parentCell hparentCube
      obtain ⟨p, hp, hcell⟩ := List.mem_flatMap.mp hparent
      have hoffset : offset ∈ fourBlockOffsets := by
        exact fourBlock_of_lt_four (Nat.mod_lt x (by norm_num))
          (Nat.mod_lt y (by norm_num)) (Nat.mod_lt z (by norm_num))
      have hdecomp :
          v (Int.ofNat x) (Int.ofNat y) (Int.ofNat z) =
            (parentCell.smul 4).add offset := by
        dsimp only [parentCell, offset]
        apply v3_eq <;> simp [V3.smul, V3.add, v] <;>
          omega
      have hsub := two_refinement_covers_cell hchildren hblock haction p
        (hierarchyPoseLevel_frames n p hp) parentCell hcell offset hoffset
      rw [← hdecomp] at hsub
      unfold twoRefinementCells at hsub
      obtain ⟨q, hq, hrest⟩ := List.mem_flatMap.mp hsub
      obtain ⟨r, hr, hrcell⟩ := List.mem_flatMap.mp hrest
      change v (Int.ofNat x) (Int.ofNat y) (Int.ofNat z) ∈
        (twoRefinements (hierarchyPoseLevel n)).flatMap body
      apply List.mem_flatMap.mpr
      refine ⟨r, ?_, hrcell⟩
      unfold twoRefinements
      unfold hashDedup
      rw [Std.HashSet.mem_toList, Std.HashSet.mem_ofList,
        List.contains_iff_mem]
      apply List.mem_flatMap.mpr
      refine ⟨q, ?_, hr⟩
      apply List.mem_flatMap.mpr
      exact ⟨p, hp, hq⟩

private theorem center_id (n : Nat) :
    3 * hierarchyCenterShift n + 2 = 2 * (4 : Int) ^ n := by
  induction n with
  | zero => norm_num [hierarchyCenterShift]
  | succ n ih =>
      rw [show hierarchyCenterShift (n + 1) =
        4 * hierarchyCenterShift n + 2 by rfl]
      calc
        3 * (4 * hierarchyCenterShift n + 2) + 2 =
            4 * (3 * hierarchyCenterShift n + 2) := by ring
        _ = 4 * (2 * (4 : Int) ^ n) := by rw [ih]
        _ = 2 * (4 : Int) ^ (n + 1) := by rw [pow_succ]; ring

private theorem pow_four_mod_three (n : Nat) : 4 ^ n % 3 = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ, Nat.mul_mod, ih]

private theorem hierarchy_upper_add_center (n : Nat) :
    (((4 ^ n + 2) / 3 : Nat) : Int) + hierarchyCenterShift n =
      (4 : Int) ^ n := by
  have hm : (4 ^ n + 2) % 3 = 0 := by
    rw [Nat.add_mod, pow_four_mod_three]
  have hdiv := Nat.mod_add_div (4 ^ n + 2) 3
  rw [hm] at hdiv
  have hnat : 3 * ((4 ^ n + 2) / 3) = 4 ^ n + 2 := by omega
  have hint : 3 * (((4 ^ n + 2) / 3 : Nat) : Int) =
      (4 : Int) ^ n + 2 := by exact_mod_cast hnat
  have hc := center_id n
  omega

private theorem body_shift_mem {p : Pose} {a s : V3} (ha : a ∈ body p) :
    a.sub s ∈ body (po p.frame (p.shift.sub s)) := by
  unfold body at ha ⊢
  rw [List.mem_eraseDups] at ha ⊢
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
  apply List.mem_map.mpr
  refine ⟨c, hc, ?_⟩
  rcases p with ⟨pf, px, py, pz⟩
  rcases s with ⟨sx, sy, sz⟩
  apply v3_eq <;> simp [cellLower, po, V3.sub, V3.get, v] <;> ring

private theorem centered_cell_mem {n : Nat} {a : V3}
    (ha : a ∈ (hierarchyPoseLevel n).flatMap body) :
    a.sub (v (hierarchyCenterShift n) (hierarchyCenterShift n)
      (hierarchyCenterShift n)) ∈ hierarchyCells n := by
  obtain ⟨p, hp, hpa⟩ := List.mem_flatMap.mp ha
  unfold hierarchyCells hierarchyPatch translatedPatch
  apply List.mem_flatMap.mpr
  refine ⟨po p.frame (p.shift.sub
    (v (hierarchyCenterShift n) (hierarchyCenterShift n)
      (hierarchyCenterShift n))), ?_, ?_⟩
  · exact List.mem_map.mpr ⟨p, hp, rfl⟩
  · exact body_shift_mem hpa

private theorem hierarchyPoseLevel_cells_nodup
    (hchildren : childrenPartitionCheck = true) :
    ∀ n : Nat, ((hierarchyPoseLevel n).flatMap body).Nodup := by
  intro n
  induction n with
  | zero =>
      simpa [hierarchyPoseLevel] using body_nodup_hierarchy rootPose
  | succ n ih =>
      exact twoRefinements_flat_cells_nodup hchildren
        (hierarchyPoseLevel_frames n) ih

private theorem cellLower_shift (f : Frame) (t s d : V3) :
    cellLower f (t.sub s) d = (cellLower f t d).sub s := by
  rcases f with ⟨⟨p0, p1, p2⟩, sg⟩
  rcases t with ⟨tx, ty, tz⟩
  rcases s with ⟨sx, sy, sz⟩
  apply v3_eq <;>
    simp [cellLower, V3.sub, V3.get, N3.get, v] <;> ring

private theorem v3_sub_add_cancel (a s : V3) : (a.sub s).add s = a := by
  rcases a with ⟨ax, ay, az⟩
  rcases s with ⟨sx, sy, sz⟩
  simp [V3.sub, V3.add, v]

private theorem v3_add_sub_cancel (a s : V3) : (a.add s).sub s = a := by
  rcases a with ⟨ax, ay, az⟩
  rcases s with ⟨sx, sy, sz⟩
  simp [V3.sub, V3.add, v]

private theorem body_shift_iff {p : Pose} {s a : V3} :
    a ∈ body (po p.frame (p.shift.sub s)) ↔ a.add s ∈ body p := by
  constructor
  · intro ha
    obtain ⟨d, hd, had⟩ := body_mem_iff.mp ha
    change a = cellLower p.frame (p.shift.sub s) d at had
    apply body_mem_iff.mpr
    refine ⟨d, hd, ?_⟩
    calc
      a.add s = (cellLower p.frame (p.shift.sub s) d).add s := by rw [had]
      _ = ((cellLower p.frame p.shift d).sub s).add s := by
        rw [cellLower_shift]
      _ = cellLower p.frame p.shift d := v3_sub_add_cancel _ _
  · intro ha
    obtain ⟨d, hd, had⟩ := body_mem_iff.mp ha
    apply body_mem_iff.mpr
    refine ⟨d, hd, ?_⟩
    change a = cellLower p.frame (p.shift.sub s) d
    rw [cellLower_shift]
    calc
      a = (a.add s).sub s := (v3_add_sub_cancel a s).symm
      _ = (cellLower p.frame p.shift d).sub s := by rw [had]

private theorem shifted_bodies_disjoint {p q : Pose} {s : V3}
    (hpq : (body p).Disjoint (body q)) :
    (body (po p.frame (p.shift.sub s))).Disjoint
      (body (po q.frame (q.shift.sub s))) := by
  rw [List.disjoint_left] at hpq ⊢
  intro a hap haq
  exact hpq (body_shift_iff.mp hap) (body_shift_iff.mp haq)

private theorem translatedPatch_cells_nodup (amount : Int) {xs : List Pose}
    (hcells : (xs.flatMap body).Nodup) :
    ((translatedPatch amount xs).flatMap body).Nodup := by
  let s := v amount amount amount
  have hsource := List.nodup_flatMap.mp hcells
  unfold translatedPatch
  apply List.nodup_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact body_nodup_hierarchy _
  · rw [List.pairwise_map]
    exact hsource.2.imp fun hpq =>
      shifted_bodies_disjoint (s := s) hpq

/-- R§9 disjointness induction: distinct poses at every centered hierarchy
    level own pairwise-disjoint literal baseline cells. -/
theorem hierarchy_cells_disjoint
    (hchildren : childrenPartitionCheck = true) :
    HierarchyCellsDisjoint := by
  intro n
  unfold hierarchyCells hierarchyPatch
  exact translatedPatch_cells_nodup (hierarchyCenterShift n)
    (hierarchyPoseLevel_cells_nodup hchildren n)

private theorem exists_unit_nat {N : Nat} (hN : 0 < N) {x : ℝ}
    (hx0 : 0 ≤ x) (hxN : x ≤ N) :
    ∃ k : Nat, k < N ∧ (k : ℝ) ≤ x ∧ x ≤ (k : ℝ) + 1 := by
  induction N generalizing x with
  | zero => omega
  | succ N ih =>
      cases N with
      | zero =>
          exact ⟨0, by omega, by simpa using hx0, by simpa using hxN⟩
      | succ N =>
          by_cases h : x ≤ (N + 1 : Nat)
          · obtain ⟨k, hk, hkx, hxk⟩ := ih (by omega) hx0 h
            exact ⟨k, by omega, hkx, hxk⟩
          · refine ⟨N + 1, by omega, ?_, ?_⟩
            · push_cast at h
              simpa using (le_of_not_ge h)
            · simpa using hxN

/-- R§9 support induction: every concrete level contains the documented
    centered cube `[-c_n,(4^n+2)/3]^3`. -/
theorem hierarchy_box_containment
    (hchildren : childrenPartitionCheck = true)
    (hcontrols : hierarchyCellControlsCheck = true) :
    HierarchyBoxContainment := by
  simp only [hierarchyCellControlsCheck, Bool.and_eq_true] at hcontrols
  obtain ⟨hblock, haction⟩ := hcontrols
  intro n x hx
  let c := hierarchyCenterShift n
  let N := 4 ^ n
  have hN : 0 < N := by simp [N]
  have hu : (((4 ^ n + 2) / 3 : Nat) : Int) + c = (N : Int) := by
    simpa [c, N] using hierarchy_upper_add_center n
  have hcoord (i : Fin 3) :
      0 ≤ x i + (c : ℝ) ∧ x i + (c : ℝ) ≤ (N : ℝ) := by
    have hi := hx i
    have hur : ((((4 ^ n + 2) / 3 : Nat) : Int) : ℝ) + (c : ℝ) =
        (N : ℝ) := by exact_mod_cast hu
    dsimp [c, N] at hur ⊢
    constructor
    · linarith
    · calc
        x i + (hierarchyCenterShift n : ℝ) ≤
            (((4 ^ n + 2) / 3 : Nat) : ℝ) +
              (hierarchyCenterShift n : ℝ) := by
                have h := add_le_add_right hi.2
                  (hierarchyCenterShift n : ℝ)
                simpa [add_comm] using h
        _ = ((4 ^ n : Nat) : ℝ) := hur
  obtain ⟨kx, hkxN, hkx0, hkx1⟩ :=
    exists_unit_nat hN (hcoord (0 : Fin 3)).1 (hcoord (0 : Fin 3)).2
  obtain ⟨ky, hkyN, hky0, hky1⟩ :=
    exists_unit_nat hN (hcoord (1 : Fin 3)).1 (hcoord (1 : Fin 3)).2
  obtain ⟨kz, hkzN, hkz0, hkz1⟩ :=
    exists_unit_nat hN (hcoord (2 : Fin 3)).1 (hcoord (2 : Fin 3)).2
  let a := v (Int.ofNat kx) (Int.ofNat ky) (Int.ofNat kz)
  have hacube : a ∈ hierarchyCubeCells n := by
    exact hierarchyCubeCell_mem hkxN hkyN hkzN
  have haraw := hierarchyCubeCells_covered hchildren hblock haction n a hacube
  let center := v c c c
  have hacentered : a.sub center ∈ hierarchyCells n := by
    exact centered_cell_mem haraw
  refine ⟨a.sub center, hacentered, ?_⟩
  intro i
  fin_cases i <;>
    simp [a, center, V3.sub, V3.get, v] <;> constructor <;> linarith

/-- The explicit centered boxes exhaust Euclidean three-space. -/
def HierarchyBoxesExhaust : Prop :=
  ∀ x : E3, ∃ n : Nat, x ∈ hierarchyBoundingBox n

/-- The explicit R§9 boxes exhaust Euclidean space.  This is the
    Archimedean part of hierarchy exhaustion, separated from the finite-cell
    support induction. -/
theorem hierarchy_boxes_exhaust : HierarchyBoxesExhaust := by
  intro x
  let m : ℝ := max |x 0| (max |x 1| |x 2|)
  obtain ⟨k, hk⟩ := exists_nat_ge m
  have hcoord : ∀ i : Fin 3, |x i| ≤ (k : ℝ) := by
    intro i
    fin_cases i
    · exact (le_max_left |x 0| (max |x 1| |x 2|)).trans hk
    · exact (le_max_left |x 1| |x 2|).trans
        ((le_max_right |x 0| (max |x 1| |x 2|)).trans hk)
    · exact (le_max_right |x 1| |x 2|).trans
        ((le_max_right |x 0| (max |x 1| |x 2|)).trans hk)
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt
    (show (1 : ℝ) < 4 by norm_num)).eventually_gt_atTop (3 * (k : ℝ))
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hpow
  have hnreal : 3 * (k : ℝ) < (4 : ℝ) ^ n := hn n le_rfl
  have hknat : 3 * k ≤ 4 ^ n := by
    have : 3 * k < 4 ^ n := by exact_mod_cast hnreal
    omega
  have hkcenter : (k : Int) ≤ hierarchyCenterShift n := by
    have hkpow : 3 * (k : Int) ≤ (4 : Int) ^ n := by
      exact_mod_cast hknat
    have hpowpos : (1 : Int) ≤ (4 : Int) ^ n := by
      have : (0 : Int) < (4 : Int) ^ n := pow_pos (by norm_num) n
      omega
    have hid := hierarchyCenterShift_identity n
    omega
  have hkupperNat : k ≤ (4 ^ n + 2) / 3 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
    omega
  refine ⟨n, ?_⟩
  intro i
  have habs := hcoord i
  have hleft : (-(k : ℝ)) ≤ x i := neg_le_of_abs_le habs
  have hright : x i ≤ (k : ℝ) := le_trans (le_abs_self (x i)) habs
  constructor
  · have hcast : ((-hierarchyCenterShift n : Int) : ℝ) ≤
        ((-(k : Int) : Int) : ℝ) :=
        Int.cast_le.mpr (neg_le_neg hkcenter)
    have hcast' : -(hierarchyCenterShift n : ℝ) ≤ -(k : ℝ) := by
      simpa only [Int.cast_neg, Int.cast_natCast] using hcast
    exact hcast'.trans hleft
  · exact hright.trans (Nat.cast_le.mpr hkupperNat)

/-- The concrete nested-union placement family, expressed extensionally by
    realization of a literal pose in one of the finite patches. -/
def hierarchyPlacements : Set RigidMotion :=
  {g | ∃ n : Nat, ∃ p ∈ hierarchyPatch n, RealizesPose g p}

/-- Historical proof interface. All 19 fields have been discharged across
    exchanges 1–7; the empty record remains so review receipts and the
    conditional compatibility theorem continue to elaborate. -/
structure Hypotheses : Prop where

/-- The full Object property used by the spine.  Compactness, regular closure,
    and nonempty interior are now derived rather than hypothesis fields. -/
theorem tube_homeomorphism (H : Hypotheses) : HasTubeHomeomorphism :=
  hasTubeHomeomorphism_of_tube_construction per_tube_homeomorphisms_holds
    feature_tube_maps_glue_holds feature_tube_map_carries_carrier_holds

theorem tube_ball (H : Hypotheses) : CompactRegularClosedBall Q :=
  compactRegularClosedBall_of_tube_homeomorphism (tube_homeomorphism H)

/-- R§6's geometric endpoint, reconstructed from its carrier-recovery and
    native-frame readout sub-lemmas. -/
theorem native_asymmetry_planar_reduction
    (H : Hypotheses) : PlanarAreaNativeReduction :=
  planar_area_native_reduction planar_area_carrier_recovery_holds
    carrier_feature_frame_reduction_holds

/-- The phase-1 rational bound `8(3/25)²<1`, interpreted through the exact
    analytic threshold theorem. -/
theorem r44_cone_angle_bound (h : lipschitzBoundsCheck = true) :
    coneAngle (3 / 25) > 4 * Real.pi / 3 := by
  unfold lipschitzBoundsCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h8 : (8 : ℝ) * (3 / 25) ^ 2 < 1 := by
    have h8' : (8 : ℝ) * 3 ^ 2 < 25 ^ 2 := by exact_mod_cast h.1
    calc
      (8 : ℝ) * (3 / 25) ^ 2 = (8 * 3 ^ 2) / 25 ^ 2 := by ring
      _ < 1 := (div_lt_one (by positivity)).2 h8'
  rw [coneAngle_gt_four_pi_div_three_iff (by norm_num : (0 : ℝ) ≤ 3 / 25)]
  exact h8

/-- A-L4.1 reconstructed from the two exact proved sub-lemmas and the
    proved Lipschitz arithmetic. -/
theorem uniform_solid_angle (H : Hypotheses) : UniformFeatureSolidAngle Q := by
  intro T g hg r x hx
  obtain ⟨A, hA⟩ := feature_circular_cone_containment_holds T g hg r x hx
  have hmono := solidAngle_mono (hA.trans interior_subset)
  rw [solidAngle_linearIsometry_image, circular_cone_solid_angle_holds] at hmono
  have hbound := r44_cone_angle_bound deviations_distinct.2
  exact lt_of_lt_of_le
    ((ENNReal.ofReal_lt_ofReal_iff (hbound.trans' (by positivity))).2 hbound) hmono

private theorem complete_dihedral (_H : Hypotheses) : CompleteDihedralList Q :=
  complete_dihedral_list_holds solid_mesh_exact mesh_angle_audit profile_canonical
    deviations_distinct.1

private theorem generic_partners (H : Hypotheses) : GenericFeaturePartners Q :=
  generic_feature_partner_holds
    (cone_sector_budgets_holds (local_finiteness (tube_ball H))) (complete_dihedral H)

private theorem whole_companions (H : Hypotheses) : WholeFeatureCompanions Q :=
  connected_feature_companion_holds
    (local_finiteness (tube_ball H))
    (cone_sector_budgets_holds (local_finiteness (tube_ball H)))
    (generic_partners H)
    (uniform_solid_angle H)

private theorem feature_rigidity (H : Hypotheses) : FeatureContainmentRigidity Q :=
  feature_containment_rigidity_holds (generic_partners H) (whole_companions H)

private theorem registered_mates (H : Hypotheses) : OnlyRegisteredMates Q :=
  only_registered_mates_holds (whole_companions H) (feature_rigidity H)
    (companion_pose_discrete_holds profile_canonical mates_census (feature_rigidity H))
    (retained_core_overlap_holds (tube_ball H) mates_census) mates_census

/-- Every native role has an actual companion tile whose legal relative pose
    owns the role's far-side shell cell.  This is the feature-to-baseline
    direction of the A-L6.1/R§7 bridge. -/
theorem role_companion_owns_far_cell (H : Hypotheses) (T : Tiling Q)
    {g : RigidMotion} (hg : g ∈ T.placements) (r : Role) :
    ∃ h ∈ T.placements, h ≠ g ∧
      ∃ s : Role, CompleteFeatureMate g r h s ∧
        ∃ p ∈ legalContacts,
          RealizesPose (relativeMotion g h) p ∧
            featureFarCell (nativeFeatureData r) ∈ body p := by
  obtain ⟨h, hh, hne, _, ⟨s, hcontained⟩, _⟩ :=
    whole_companions H T g hg r
  have hmate : CompleteFeatureMate g r h s :=
    feature_rigidity H T g h hg hh (Ne.symm hne) r s hcontained
  obtain ⟨p, hp, hreal⟩ := registered_mates H T g h hg hh (Ne.symm hne)
    ⟨r, s, hmate⟩
  have hformula :=
    (companion_pose_discrete_holds profile_canonical mates_census
      (feature_rigidity H)).2 T g h hg hh (Ne.symm hne) r s hmate
  exact ⟨h, hh, hne, s, hmate, p, hp, hreal,
    formula_mate_owns_far_cell registered_shell_cell_controls hp hreal hformula⟩

private theorem legalContact_frame_mem {p : Pose} (hp : p ∈ legalContacts) :
    p.frame ∈ allFrames := by
  -- [compile-fix begin: inline the helper moved with the companion proof]
  have hcontrols := registered_shell_cell_controls
  simp only [registeredShellCellControlsCheck, Bool.and_eq_true] at hcontrols
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hcontrols.1.1.2 p hp)
  -- [compile-fix end]

/-- Every literal shell cell has one component owner, and that owner has a
legal-contact index.  Existence comes from a feature companion; uniqueness is
the disjoint-retained-core argument. -/
theorem shellCell_unique_owner_with_index
    (H : Hypotheses) (T : Tiling Q) {g : RigidMotion}
    (hg : g ∈ T.placements)
    (hgrid : BaselineComponentCoversGrid Q)
    (c : V3) (hc : c ∈ shellCells) :
    (∃! h : RigidMotion, ComponentOwnsShellCell T g c h) ∧
      ∀ h : RigidMotion, ComponentOwnsShellCell T g c h →
        ∃ k ∈ List.range legalContacts.length, ShellCellOwner T g c h k := by
  have hcontrols := registered_shell_cell_controls
  simp only [registeredShellCellControlsCheck, Bool.and_eq_true] at hcontrols
  have hset : setEq roleFarCells shellCells = true := hcontrols.1.1.1.1.2
  simp only [setEq, Bool.and_eq_true, subset] at hset
  have hcmem : c ∈ roleFarCells := by
    apply List.contains_iff_mem.mp
    exact List.all_eq_true.mp hset.2 c hc
  obtain ⟨rn, hrn, hfar⟩ := List.mem_map.mp hcmem
  have hrnlt : rn < 192 := List.mem_range.mp hrn
  let r : Role := ⟨rn, hrnlt⟩
  have hfar' : featureFarCell (nativeFeatureData r) = c := by
    simpa [roleFarCells, nativeFeatureData, r] using hfar
  obtain ⟨h, hh, hne, s, hmate, p, hp, hreal, hcell⟩ :=
    role_companion_owns_far_cell H T hg r
  rw [hfar'] at hcell
  have hcomp : SameFeatureComponent T g h := by
    exact Relation.ReflTransGen.single
      ⟨hg, hh, Ne.symm hne, Or.inl ⟨r, s, hmate⟩⟩
  have hown : ComponentOwnsShellCell T g c h :=
    ⟨hh, hcomp, p, legalContact_frame_mem hp, hreal, hcell⟩
  obtain ⟨ip, hip⟩ := List.get_of_mem hp
  have hget : getD legalContacts ip.val rootPose = p := by
    rw [← hip]
    simp [getD, ip.isLt, List.get_eq_getElem]
  have hiprange : ip.val ∈ List.range legalContacts.length :=
    List.mem_range.mpr ip.isLt
  have hcCover : c ∈ coverAt ip.val := by
    simp [coverAt, inter, poseAt, hget, hcell, hc]
  have hshellOwner : ShellCellOwner T g c h ip.val :=
    ⟨hown, hiprange, by simpa [hget] using hreal, hcCover⟩
  constructor
  · refine ⟨h, hown, ?_⟩
    intro k hkown
    obtain ⟨hk, hkcomp, q, hqf, hqreal, hqcell⟩ := hkown
    obtain ⟨A, hAg, _, _, hdisjoint⟩ := hgrid T g hg
    exact component_cell_owner_unique hAg hh hk hcomp hkcomp hdisjoint
      (legalContact_frame_mem hp) hqf hreal hqreal hcell hqcell |>.symm
  · intro k hkown
    have hkh : k = h := by
      obtain ⟨hk, hkcomp, q, hqf, hqreal, hqcell⟩ := hkown
      obtain ⟨A, hAg, _, _, hdisjoint⟩ := hgrid T g hg
      exact component_cell_owner_unique hAg hk hh hkcomp hcomp hdisjoint
        hqf (legalContact_frame_mem hp) hqreal hreal hqcell hcell
    subst k
    exact ⟨ip.val, hiprange, hshellOwner⟩

/-- The recursion invariant: every remaining cell belongs to exactly one
remaining index, and every remaining index still covers a remaining cell. -/
def ExactShellCover (todo : List V3) (cover : List Nat) : Prop :=
  (∀ c ∈ todo, ∃! k : Nat, k ∈ cover ∧ c ∈ coverAt k) ∧
  ∀ k ∈ cover, ∃ c ∈ todo, c ∈ coverAt k

/-- Ordered pairwise compatibility of the indices retained by shell search. -/
def PairwiseShellCompatible (cover : List Nat) : Prop :=
  ∀ i ∈ cover, ∀ j ∈ cover, i ≠ j →
    compatible legalContacts (poseAt i) (poseAt j) = true

private theorem betterCell_mem (available : List Nat) {a b : V3} :
    betterCell available a b = a ∨ betterCell available a b = b := by
  unfold betterCell
  split <;> simp_all

private theorem chooseConstrainedCell_mem (available : List Nat)
    {x : V3} {xs : List V3} :
    chooseConstrainedCell available (x :: xs) ∈ x :: xs := by
  unfold chooseConstrainedCell
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih =>
      simp only [List.foldl_cons]
      have hchoice := betterCell_mem available (a := x) (b := y)
      have hmem := ih (x := betterCell available x y)
      rcases List.mem_cons.mp hmem with heq | htail
      · change List.foldl (betterCell available) (betterCell available x y) ys =
          betterCell available x y at heq
        rw [heq]
        rcases hchoice with h | h <;> simp [h]
      · simp [htail]

private theorem diff_length_lt_of_common {todo remove : List V3} {x : V3}
    (hxtodo : x ∈ todo) (hxremove : x ∈ remove) :
    (diff todo remove).length < todo.length := by
  induction todo with
  | nil => simp at hxtodo
  | cons a as ih =>
      by_cases ha : a ∈ remove
      · have hcontains : remove.contains a = true := List.contains_iff_mem.mpr ha
        simp only [diff, List.filter_cons, hcontains, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, List.length_cons]
        exact Nat.lt_succ_of_le
          (List.length_filter_le (fun x => !remove.contains x) as)
      · have hcontains : remove.contains a = false := by simp [ha]
        have hxas : x ∈ as := by
          rcases List.mem_cons.mp hxtodo with hxa | hxa
          · subst a
            contradiction
          · exact hxa
        simp only [diff, List.filter_cons, hcontains, Bool.not_false,
          ↓reduceIte, List.length_cons]
        exact Nat.succ_lt_succ (ih hxas)

/-- Completeness of the literal backtracking search.  Any duplicate-free,
pairwise-compatible exact cover surviving in `available` occurs in the search,
up to permutation with the reversed accumulator. -/
theorem enumerateShells_complete :
    ∀ (fuel : Nat) (todo : List V3) (available acc cover : List Nat),
      cover.Nodup →
      (∀ k ∈ cover, k ∈ available) →
      ExactShellCover todo cover →
      PairwiseShellCompatible cover →
      todo.length < fuel →
      ∃ out ∈ enumerateShells fuel todo available acc,
        out.Perm (acc.reverse ++ cover) := by
  intro fuel
  induction fuel with
  | zero =>
      intro todo available acc cover _ _ _ _ hlen
      omega
  | succ fuel ih =>
      intro todo available acc cover hnodup hsub hexact hcompatible hlen
      cases todo with
      | nil =>
          have hcover : cover = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro k hk
            obtain ⟨c, hc, _⟩ := hexact.2 k hk
            simp at hc
          subst cover
          refine ⟨acc.reverse, ?_, ?_⟩
          · simp [enumerateShells]
          · simp
      | cons c cs =>
          let x := chooseConstrainedCell available (c :: cs)
          have hx : x ∈ c :: cs := chooseConstrainedCell_mem available
          obtain ⟨k, hkdata, hkunique⟩ := hexact.1 x hx
          have hkcover : k ∈ cover := hkdata.1
          have hkx : x ∈ coverAt k := hkdata.2
          have hkavailable : k ∈ available := hsub k hkcover
          have hkcandidate : k ∈ candidatesForCell available x := by
            simp [candidatesForCell, hkavailable, hkx]
          let rest := cover.erase k
          have hrestNodup : rest.Nodup := hnodup.erase k
          have hknotrest : k ∉ rest := hnodup.not_mem_erase
          have hrestSub : ∀ j ∈ rest,
              j ∈ diff available (badIndices k) := by
            intro j hj
            have hjcover : j ∈ cover := List.mem_of_mem_erase hj
            have hjne : j ≠ k := by
              intro h
              subst j
              exact hknotrest hj
            have hjavailable := hsub j hjcover
            have hcomp := hcompatible k hkcover j hjcover hjne.symm
            have hjbad : j ∉ badIndices k := by
              intro hjbad
              simp [badIndices, hjne, hcomp] at hjbad
            simp [diff, hjavailable, hjbad]
          have hrestExact : ExactShellCover
              (diff (c :: cs) (coverAt k)) rest := by
            constructor
            · intro d hd
              have hdtodo : d ∈ c :: cs := (List.mem_filter.mp hd).1
              have hdnotk : d ∉ coverAt k := by
                intro hdk
                have htrue : (coverAt k).contains d = true :=
                  List.contains_iff_mem.mpr hdk
                have hfalse : (coverAt k).contains d = false := by
                  simpa using (List.mem_filter.mp hd).2
                rw [hfalse] at htrue
                contradiction
              obtain ⟨j, hjdata, hjunique⟩ := hexact.1 d hdtodo
              have hjne : j ≠ k := by
                intro heq
                subst j
                exact hdnotk hjdata.2
              have hjrest : j ∈ rest :=
                hnodup.mem_erase_iff.mpr ⟨hjne, hjdata.1⟩
              refine ⟨j, ⟨hjrest, hjdata.2⟩, ?_⟩
              intro l hldata
              exact hjunique l ⟨List.mem_of_mem_erase hldata.1, hldata.2⟩
            · intro j hjrest
              have hjcover : j ∈ cover := List.mem_of_mem_erase hjrest
              obtain ⟨d, hdtodo, hjd⟩ := hexact.2 j hjcover
              have hjne : j ≠ k := by
                intro heq
                subst j
                exact hknotrest hjrest
              have hdnotk : d ∉ coverAt k := by
                intro hdk
                obtain ⟨o, _, hounique⟩ := hexact.1 d hdtodo
                have hjo : j = o := hounique j ⟨hjcover, hjd⟩
                have hko : k = o := hounique k ⟨hkcover, hdk⟩
                exact hjne (hjo.trans hko.symm)
              refine ⟨d, ?_, hjd⟩
              simp [diff, hdtodo, hdnotk]
          have hrestCompatible : PairwiseShellCompatible rest := by
            intro i hi j hj hij
            exact hcompatible i (List.mem_of_mem_erase hi)
              j (List.mem_of_mem_erase hj) hij
          have hrestLen : (diff (c :: cs) (coverAt k)).length < fuel := by
            have hshrink := diff_length_lt_of_common hx hkx
            omega
          obtain ⟨out, hout, hperm⟩ := ih
            (diff (c :: cs) (coverAt k))
            (diff available (badIndices k)) (k :: acc) rest
            hrestNodup hrestSub hrestExact hrestCompatible hrestLen
          refine ⟨out, ?_, ?_⟩
          · simp only [enumerateShells]
            apply List.mem_flatMap.mpr
            exact ⟨k, hkcandidate, hout⟩
          · apply hperm.trans
            have hp := List.Perm.append_left acc.reverse
              (List.perm_cons_erase hkcover).symm
            simpa [List.reverse_cons, List.append_assoc] using hp

private theorem frame_sign_pm {f : Frame} (hf : f ∈ allFrames) (i : Fin 3) :
    f.sign.get i = 1 ∨ f.sign.get i = -1 := by
  fin_cases i
  · exact (allFrames_data hf).sx
  · exact (allFrames_data hf).sy
  · exact (allFrames_data hf).sz

private theorem frame_row_eq_of_action_eq {f f' : Frame}
    (hf : f ∈ allFrames) (hf' : f' ∈ allFrames)
    (haction : ∀ x : E3, ∀ i : Fin 3,
      frameActReal f x i = frameActReal f' x i)
    (i : Fin 3) :
    f.perm.get i = f'.perm.get i ∧ f.sign.get i = f'.sign.get i := by
  let j : Nat := f.perm.get i
  have hj : j < 3 := perm_lt_three hf i
  have hj' : f'.perm.get i < 3 := perm_lt_three hf' i
  have heq := haction (coordinateVector j) i
  rw [frameActReal, frameCoordinate_of_lt (coordinateVector j) hj] at heq
  rw [frameActReal, frameCoordinate_of_lt (coordinateVector j) hj'] at heq
  have hsi : f.sign.get i = 1 ∨ f.sign.get i = -1 := frame_sign_pm hf i
  have hperm : f'.perm.get i = j := by
    by_contra hne
    have hcoord0 : coordinateVector j ⟨f'.perm.get i, hj'⟩ = 0 := by
      simp [coordinateVector, hne]
    have hcoord1 : coordinateVector j ⟨j, hj⟩ = 1 := by
      simp [coordinateVector]
    rw [hcoord0, hcoord1] at heq
    rcases hsi with hs | hs <;> rw [hs] at heq <;> norm_num at heq
  have hcoord : coordinateVector j ⟨f'.perm.get i, hj'⟩ = 1 := by
    simp [coordinateVector, hperm]
  have hcoord' : coordinateVector j ⟨j, hj⟩ = 1 := by
    simp [coordinateVector]
  rw [hcoord, hcoord'] at heq
  norm_num at heq
  exact ⟨hperm.symm, Int.cast_injective heq⟩

private theorem frame_eq_of_rows (f f' : Frame)
    (h : ∀ i : Fin 3,
      f.perm.get i = f'.perm.get i ∧ f.sign.get i = f'.sign.get i) :
    f = f' := by
  rcases f with ⟨⟨p0, p1, p2⟩, s0, s1, s2⟩
  rcases f' with ⟨⟨q0, q1, q2⟩, t0, t1, t2⟩
  have h0 := h (0 : Fin 3)
  have h1 := h (1 : Fin 3)
  have h2 := h (2 : Fin 3)
  simp [N3.get, V3.get] at h0 h1 h2
  simp_all

/-- Within the signed-frame domain, one affine motion cannot realize two
different literal poses. -/
theorem realizesPose_pose_unique {m : RigidMotion} {p q : Pose}
    (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames)
    (hrealp : RealizesPose m p) (hrealq : RealizesPose m q) : p = q := by
  have haction : ∀ x : E3, ∀ i : Fin 3,
      frameActReal p.frame x i = frameActReal q.frame x i := by
    intro x i
    rw [← hrealp.1 x i, ← hrealq.1 x i]
  have h0 := frame_row_eq_of_action_eq hp hq haction (0 : Fin 3)
  have h1 := frame_row_eq_of_action_eq hp hq haction (1 : Fin 3)
  have h2 := frame_row_eq_of_action_eq hp hq haction (2 : Fin 3)
  have hframe : p.frame = q.frame := by
    apply frame_eq_of_rows
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hshift : p.shift = q.shift := by
    apply v3_eq
    · exact Int.cast_injective ((hrealp.2 0).symm.trans (hrealq.2 0))
    · exact Int.cast_injective ((hrealp.2 1).symm.trans (hrealq.2 1))
    · exact Int.cast_injective ((hrealp.2 2).symm.trans (hrealq.2 2))
  cases p
  cases q
  simp_all

theorem featureAdjacent_comm {T : Tiling Q} {g h : RigidMotion} :
    FeatureAdjacent T g h ↔ FeatureAdjacent T h g := by
  constructor <;> rintro ⟨hg, hh, hne, hm⟩
  · exact ⟨hh, hg, Ne.symm hne, hm.elim Or.inr Or.inl⟩
  · exact ⟨hh, hg, Ne.symm hne, hm.elim Or.inr Or.inl⟩

theorem sameFeatureComponent_symm {T : Tiling Q} {g h : RigidMotion}
    (hgh : SameFeatureComponent T g h) : SameFeatureComponent T h g := by
  have hs := hgh.swap
  exact Relation.ReflTransGen.mono
    (r := Function.swap (FeatureAdjacent T)) (p := FeatureAdjacent T)
    (fun a b hab => featureAdjacent_comm.mp hab) hs

theorem sameFeatureComponent_trans {T : Tiling Q} {g h k : RigidMotion}
    (hgh : SameFeatureComponent T g h) (hhk : SameFeatureComponent T h k) :
    SameFeatureComponent T g k := hgh.trans hhk

private theorem nativeFeature_mem_role {a : Feature} (ha : a ∈ nativeFeatures) :
    ∃ r : Role, nativeFeatureData r = a := by
  obtain ⟨i, hi⟩ := List.get_of_mem ha
  have hlen : nativeFeatures.length = 192 := native_features_length
  let r : Role := ⟨i.val, by simpa [hlen] using i.isLt⟩
  refine ⟨r, ?_⟩
  change getD nativeFeatures i.val fallbackFeature = a
  rw [show getD nativeFeatures i.val fallbackFeature = nativeFeatures.get i by
    simp [getD, i.isLt, List.get_eq_getElem]]
  exact hi

private theorem allFrames_relative_mem {p q : Pose}
    (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames) :
    (p.relative q).frame ∈ allFrames := by
  have hcheck : allFrames.all (fun f => allFrames.all fun f' =>
      allFrames.contains (f.transpose.mul f')) = true := by decide
  unfold Pose.relative Pose.inverse Pose.transform
  exact List.contains_iff_mem.mp
    (List.all_eq_true.mp (List.all_eq_true.mp hcheck p.frame hp) q.frame hq)

private theorem legal_index_injective {i j : Nat}
    (hi : i ∈ List.range legalContacts.length)
    (hj : j ∈ List.range legalContacts.length)
    (hpose : poseAt i = poseAt j) : i = j := by
  have hnodup : legalContacts.Nodup := by decide
  let ii : Fin legalContacts.length := ⟨i, List.mem_range.mp hi⟩
  let jj : Fin legalContacts.length := ⟨j, List.mem_range.mp hj⟩
  have hgeti : poseAt i = legalContacts.get ii := by
    simp [poseAt, getD, ii, List.mem_range.mp hi]
  have hgetj : poseAt j = legalContacts.get jj := by
    simp [poseAt, getD, jj, List.mem_range.mp hj]
  have hgeteq : legalContacts.get ii = legalContacts.get jj := by
    rw [← hgeti, ← hgetj]
    exact hpose
  have hfin : ii = jj := hnodup.get_inj_iff.mp hgeteq
  exact congrArg Fin.val hfin

/-- Distinct actually realized shell-owner indices satisfy the exact finite
compatibility predicate used by `enumerateShells`. -/
theorem shellOwner_indices_compatible
    (H : Hypotheses) (T : Tiling Q) {g : RigidMotion}
    (hg : g ∈ T.placements) (hgrid : BaselineComponentCoversGrid Q)
    {c d : V3} {h k : RigidMotion} {i j : Nat}
    (hi : ShellCellOwner T g c h i)
    (hj : ShellCellOwner T g d k j)
    (hij : i ≠ j) :
    compatible legalContacts (poseAt i) (poseAt j) = true := by
  rcases hi with ⟨⟨hh, hhcomp, pi, hpif, hpireal, hci⟩,
    hirange, hireal, _⟩
  rcases hj with ⟨⟨hk, hkcomp, pj, hpjf, hpjreal, hdj⟩,
    hjrange, hjreal, _⟩
  have hpi : pi = poseAt i := realizesPose_pose_unique hpif
    (legalContact_frame_mem (by
      have hi' : i < legalContacts.length := List.mem_range.mp hirange
      simp [poseAt, getD, hi'])) hpireal hireal
  subst pi
  have hpj : pj = poseAt j := realizesPose_pose_unique hpjf
    (legalContact_frame_mem (by
      have hj' : j < legalContacts.length := List.mem_range.mp hjrange
      simp [poseAt, getD, hj'])) hpjreal hjreal
  subst pj
  have hpimem : poseAt i ∈ legalContacts := by
    have hi' : i < legalContacts.length := List.mem_range.mp hirange
    simp [poseAt, getD, hi']
  have hpjmem : poseAt j ∈ legalContacts := by
    have hj' : j < legalContacts.length := List.mem_range.mp hjrange
    simp [poseAt, getD, hj']
  have hhk : h ≠ k := by
    intro heq
    subst k
    have hpq := realizesPose_pose_unique
      (legalContact_frame_mem hpimem) (legalContact_frame_mem hpjmem)
      hireal hjreal
    exact hij (legal_index_injective hirange hjrange hpq)
  have hoverlap : bodiesOverlap (poseAt i) (poseAt j) = false := by
    apply Bool.eq_false_iff.mpr
    intro hoverlap
    unfold bodiesOverlap at hoverlap
    obtain ⟨a, hai, haj⟩ := List.any_eq_true.mp hoverlap
    have haj' : a ∈ body (poseAt j) := List.contains_iff_mem.mp haj
    obtain ⟨A, hAg, _, _, hdisjoint⟩ := hgrid T g hg
    exact hhk (component_cell_owner_unique hAg hh hk hhcomp hkcomp hdisjoint
      (legalContact_frame_mem hpimem) (legalContact_frame_mem hpjmem)
      hireal hjreal hai haj')
  by_cases htouch : touch (poseAt i) (poseAt j) = true
  · have hcontrols := registered_shell_cell_controls
    simp only [registeredShellCellControlsCheck, Bool.and_eq_true] at hcontrols
    have hicheck := List.all_eq_true.mp hcontrols.2 (poseAt i) hpimem
    have hijcheck := List.all_eq_true.mp hicheck (poseAt j) hpjmem
    simp [htouch] at hijcheck
    obtain ⟨a, ha, hfar⟩ := hijcheck
    obtain ⟨r, hra⟩ := nativeFeature_mem_role ha
    rw [← hra] at hfar
    obtain ⟨ell, hell, hellne, s, hmate, pe, hpe, hpereal, hpecell⟩ :=
      role_companion_owns_far_cell H T hh r
    have hhellcomp : SameFeatureComponent T h ell :=
      Relation.ReflTransGen.single
        ⟨hh, hell, Ne.symm hellne, Or.inl ⟨r, s, hmate⟩⟩
    have hhkcomp : SameFeatureComponent T h k :=
      (sameFeatureComponent_symm hhcomp).trans hkcomp
    have hrelative : RealizesPose (relativeMotion h k)
        ((poseAt i).relative (poseAt j)) := by
      have hr := realizesPose_relative hireal hjreal
        (legalContact_frame_mem hpimem) (legalContact_frame_mem hpjmem)
      have heq : relativeMotion (relativeMotion g h) (relativeMotion g k) =
          relativeMotion h k := by
        unfold relativeMotion
        group
      rwa [heq] at hr
    obtain ⟨B, hBh, _, _, hdisjointH⟩ := hgrid T h hh
    have hkell : k = ell := component_cell_owner_unique hBh hk hell
      hhkcomp hhellcomp hdisjointH
      (allFrames_relative_mem (legalContact_frame_mem hpimem)
        (legalContact_frame_mem hpjmem))
      (legalContact_frame_mem hpe) hrelative hpereal hfar hpecell
    subst ell
    have hposeEq := realizesPose_pose_unique
      (allFrames_relative_mem (legalContact_frame_mem hpimem)
        (legalContact_frame_mem hpjmem))
      (legalContact_frame_mem hpe) hrelative hpereal
    unfold compatible
    simp [hoverlap, htouch, hposeEq, hpe]
  · unfold compatible
    have hpneq : poseAt i ≠ poseAt j := by
      intro heq
      exact hij (legal_index_injective hirange hjrange heq)
    simp [hpneq, hoverlap, htouch]

/-- An atlas index occurs in the actual shell exactly when one of the literal
shell cells has a component owner realizing that index. -/
def RealizedShellIndex (T : Tiling Q) (g : RigidMotion) (i : Nat) : Prop :=
  ∃ c ∈ shellCells, ∃ h : RigidMotion, ShellCellOwner T g c h i

noncomputable def realizedShellCover (T : Tiling Q) (g : RigidMotion) : List Nat := by
  classical
  exact (List.range legalContacts.length).filter fun i =>
    decide (RealizedShellIndex T g i)

theorem mem_realizedShellCover {T : Tiling Q} {g : RigidMotion} {i : Nat} :
    i ∈ realizedShellCover T g ↔
      i ∈ List.range legalContacts.length ∧ RealizedShellIndex T g i := by
  classical
  simp [realizedShellCover]

private theorem shellCellOwner_index_unique
    (H : Hypotheses) (T : Tiling Q) {g : RigidMotion}
    (hg : g ∈ T.placements) (hgrid : BaselineComponentCoversGrid Q)
    {c : V3} (hc : c ∈ shellCells) {h k : RigidMotion} {i j : Nat}
    (hi : ShellCellOwner T g c h i) (hj : ShellCellOwner T g c k j) :
    i = j := by
  have hownerUnique := (shellCell_unique_owner_with_index H T hg hgrid c hc).1
  have hhk : h = k := hownerUnique.unique hi.1 hj.1
  subst k
  have hpimem : poseAt i ∈ legalContacts := by
    have hi' : i < legalContacts.length := List.mem_range.mp hi.2.1
    simp [poseAt, getD, hi']
  have hpjmem : poseAt j ∈ legalContacts := by
    have hj' : j < legalContacts.length := List.mem_range.mp hj.2.1
    simp [poseAt, getD, hj']
  have hpq := realizesPose_pose_unique
    (legalContact_frame_mem hpimem) (legalContact_frame_mem hpjmem)
    hi.2.2.1 hj.2.2.1
  exact legal_index_injective hi.2.1 hj.2.1 hpq

/-- The actual component-owner indices cover each shell cell exactly once. -/
theorem realizedShellCover_exact
    (H : Hypotheses) (T : Tiling Q) {g : RigidMotion}
    (hg : g ∈ T.placements) (hgrid : BaselineComponentCoversGrid Q) :
    ExactShellCover shellCells (realizedShellCover T g) := by
  constructor
  · intro c hc
    have hdata := shellCell_unique_owner_with_index H T hg hgrid c hc
    obtain ⟨h, hown, _⟩ := hdata.1
    obtain ⟨i, hirange, hiowner⟩ := hdata.2 h hown
    have himem : i ∈ realizedShellCover T g :=
      mem_realizedShellCover.mpr ⟨hirange, c, hc, h, hiowner⟩
    refine ⟨i, ⟨himem, hiowner.2.2.2⟩, ?_⟩
    intro j hjdata
    obtain ⟨_, ⟨_, _, k, hjowner⟩⟩ := mem_realizedShellCover.mp hjdata.1
    have hcbody : c ∈ body (poseAt j) := (List.mem_filter.mp hjdata.2).1
    have hjownc : ShellCellOwner T g c k j := by
      rcases hjowner with ⟨⟨hk, hkcomp, _, _, _, _⟩,
        hjrange, hjreal, _⟩
      exact ⟨⟨hk, hkcomp, poseAt j, legalContact_frame_mem (by
          have hj' : j < legalContacts.length := List.mem_range.mp hjrange
          simp [poseAt, getD, hj']), hjreal, hcbody⟩,
        hjrange, hjreal, hjdata.2⟩
    exact shellCellOwner_index_unique H T hg hgrid hc hjownc hiowner
  · intro i hi
    obtain ⟨_, ⟨c, hc, _, hiowner⟩⟩ := mem_realizedShellCover.mp hi
    exact ⟨c, hc, hiowner.2.2.2⟩

/-- The actual component-owner cover obeys the compatibility relation used by
the finite first-shell census. -/
theorem realizedShellCover_compatible
    (H : Hypotheses) (T : Tiling Q) {g : RigidMotion}
    (hg : g ∈ T.placements) (hgrid : BaselineComponentCoversGrid Q) :
    PairwiseShellCompatible (realizedShellCover T g) := by
  intro i hi j hj hij
  obtain ⟨_, ⟨_, _, _, hiowner⟩⟩ := mem_realizedShellCover.mp hi
  obtain ⟨_, ⟨_, _, _, hjowner⟩⟩ := mem_realizedShellCover.mp hj
  exact shellOwner_indices_compatible H T hg hgrid hiowner hjowner hij

/-- R§7 first-shell bridge: the unique component owners form an exact,
pairwise-compatible cover, completeness of `enumerateShells` produces it, and
the phase-1 set-family equality identifies it with one of the 33 literals. -/
theorem registered_first_shells
    (H : Hypotheses) (T : Tiling Q) (_hregistered : Registered T)
    (hshells : firstShellsCheck = true) : CertifiedFirstShells T := by
  unfold CertifiedFirstShells
  intro g hg
  have hgrid : BaselineComponentCoversGrid Q :=
    baseline_component_covers_grid_holds (registered_mates H) atlas_44
  let cover := realizedShellCover T g
  have hnodup : cover.Nodup := List.nodup_range.filter _
  have hsub : ∀ k ∈ cover, k ∈ List.range legalContacts.length := by
    intro k hk
    exact (mem_realizedShellCover.mp hk).1
  have hexact : ExactShellCover shellCells cover :=
    realizedShellCover_exact H T hg hgrid
  have hcompatible : PairwiseShellCompatible cover :=
    realizedShellCover_compatible H T hg hgrid
  have hlen : shellCells.length < 23 := by decide
  obtain ⟨out, hout, hperm⟩ := enumerateShells_complete 23 shellCells
    (List.range legalContacts.length) [] cover hnodup hsub hexact
    hcompatible hlen
  have houtComputed : out ∈ computedShells := List.mem_eraseDups.mpr hout
  have hfamily : setFamilyEq computedShells shellSolutions = true := by
    unfold firstShellsCheck at hshells
    simp only [Bool.and_eq_true] at hshells
    aesop
  unfold setFamilyEq at hfamily
  simp only [Bool.and_eq_true] at hfamily
  have houtMatch := List.all_eq_true.mp hfamily.1 out houtComputed
  obtain ⟨shell, hshellmem, houtSet⟩ := List.any_eq_true.mp houtMatch
  have hperm' : out.Perm cover := by simpa using hperm
  have hset : setEq out shell = true := houtSet
  simp only [setEq, Bool.and_eq_true, subset] at hset
  have hcoverShell (k : Nat) : k ∈ cover ↔ k ∈ shell := by
    constructor
    · intro hk
      have hkout : k ∈ out := hperm'.mem_iff.mpr hk
      apply List.contains_iff_mem.mp
      exact List.all_eq_true.mp hset.1 k hkout
    · intro hk
      have hkout : k ∈ out := by
        apply List.contains_iff_mem.mp
        exact List.all_eq_true.mp hset.2 k hk
      exact hperm'.mem_iff.mp hkout
  refine ⟨shell, hshellmem, ?_, ?_, ?_⟩
  · intro c hc
    exact (shellCell_unique_owner_with_index H T hg hgrid c hc).1
  · intro c hc h hown
    obtain ⟨k, _, hkowner⟩ :=
      (shellCell_unique_owner_with_index H T hg hgrid c hc).2 h hown
    exact ⟨k, (hcoverShell k).mp
      (mem_realizedShellCover.mpr ⟨hkowner.2.1, c, hc, h, hkowner⟩), hkowner⟩
  · intro k hk
    obtain ⟨_, ⟨c, hc, h, hkowner⟩⟩ :=
      mem_realizedShellCover.mp ((hcoverShell k).mpr hk)
    exact ⟨c, hc, h, hkowner⟩

/-! The central-completion census is stated in the coordinates of a shell
root.  The following structural lemmas transport its literal poses to actual
placements of the registered component. -/

private def centralFaceDirections : List (Nat × Int) :=
  [(0, -1), (0, 1), (1, -1), (1, 1), (2, -1), (2, 1)]

private def centralCellFace (x : V3) (axis : Nat) (sgn : Int) : Face :=
  { axis := axis
    center2 := (x.smul 2).add (v 1 1 1) |>.add (unitAxis axis sgn)
    outward := sgn }

private theorem mem_faces_iff {p : Pose} {F : Face} :
    F ∈ faces p ↔ ∃ x ∈ body p, ∃ axis sgn,
      (axis, sgn) ∈ centralFaceDirections ∧
      x.add (unitAxis axis sgn) ∉ body p ∧
      F = centralCellFace x axis sgn := by
  unfold faces centralFaceDirections
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, hF⟩
    refine ⟨x, hx, ?_⟩
    simp only [List.mem_filterMap] at hF
    obtain ⟨d, hd, hsome⟩ := hF
    rcases d with ⟨axis, sgn⟩
    simp only at hsome
    by_cases hin : (body p).contains (x.add (unitAxis axis sgn)) = true
    · rw [hin] at hsome
      contradiction
    · have hfalse :
          (body p).contains (x.add (unitAxis axis sgn)) = false :=
        Bool.eq_false_of_not_eq_true hin
      rw [hfalse] at hsome
      refine ⟨axis, sgn, hd, ?_, ?_⟩
      · intro hmem
        have htrue := List.contains_iff_mem.mpr hmem
        rw [hfalse] at htrue
        contradiction
      · simpa [centralCellFace] using hsome.symm
  · rintro ⟨x, hx, axis, sgn, hd, hout, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp only [List.mem_filterMap]
    refine ⟨(axis, sgn), hd, ?_⟩
    have hfalse : (body p).contains (x.add (unitAxis axis sgn)) = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      exact hout (List.contains_iff_mem.mp htrue)
    simp [hfalse, centralCellFace]
    exact hout

private theorem opposite_cell {x y : V3} {a b : Nat} {s t : Int}
    (ha : (a, s) ∈ centralFaceDirections)
    (hb : (b, t) ∈ centralFaceDirections)
    (hop : oppositeFaces (centralCellFace x a s)
      (centralCellFace y b t) = true) :
    b = a ∧ t = -s ∧ y = x.add (unitAxis a s) := by
  simp [centralFaceDirections] at ha hb
  rcases ha with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases hb with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases x with ⟨xx, xy, xz⟩ <;> rcases y with ⟨yx, yy, yz⟩ <;>
    simp [oppositeFaces, centralCellFace, unitAxis, V3.smul, V3.add, v]
      at hop ⊢ <;> omega

private def CellFaceAdjacent (p q : Pose) : Prop :=
  ∃ x ∈ body p, ∃ axis sgn,
    (axis, sgn) ∈ centralFaceDirections ∧
      x.add (unitAxis axis sgn) ∈ body q ∧
      x.add (unitAxis axis sgn) ∉ body p ∧ x ∉ body q

private theorem neighbor_back {x : V3} {axis : Nat} {sgn : Int}
    (hdir : (axis, sgn) ∈ centralFaceDirections) :
    (x.add (unitAxis axis sgn)).add (unitAxis axis (-sgn)) = x := by
  simp [centralFaceDirections] at hdir
  rcases hdir with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases x with ⟨xx, xy, xz⟩ <;>
    simp [unitAxis, V3.add, v]

private theorem opposite_neighbor {x : V3} {axis : Nat} {sgn : Int}
    (hdir : (axis, sgn) ∈ centralFaceDirections) :
    oppositeFaces (centralCellFace x axis sgn)
      (centralCellFace (x.add (unitAxis axis sgn)) axis (-sgn)) = true := by
  simp [centralFaceDirections] at hdir
  rcases hdir with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases x with ⟨xx, xy, xz⟩ <;>
    simp [oppositeFaces, centralCellFace, unitAxis, V3.smul, V3.add, v] <;>
    omega

private theorem touch_iff_cellFaceAdjacent {p q : Pose} :
    touch p q = true ↔ CellFaceAdjacent p q := by
  constructor
  · intro htouch
    unfold touch at htouch
    obtain ⟨F, hF, hFG⟩ := List.any_eq_true.mp htouch
    obtain ⟨G, hG, hop⟩ := List.any_eq_true.mp hFG
    obtain ⟨x, hx, axis, sgn, hdir, hout, rfl⟩ := mem_faces_iff.mp hF
    obtain ⟨y, hy, axis', sgn', hdir', hout', hGeq⟩ := mem_faces_iff.mp hG
    subst G
    obtain ⟨haxis, hsgn, hyx⟩ := opposite_cell hdir hdir' hop
    subst axis'
    subst sgn'
    refine ⟨x, hx, axis, sgn, hdir, ?_, hout, ?_⟩
    · rwa [← hyx]
    · intro hxq
      rw [hyx, neighbor_back hdir] at hout'
      exact hout' hxq
  · rintro ⟨x, hx, axis, sgn, hdir, hneighbor, houtp, houtq⟩
    unfold touch
    apply List.any_eq_true.mpr
    refine ⟨centralCellFace x axis sgn, mem_faces_iff.mpr
      ⟨x, hx, axis, sgn, hdir, houtp, rfl⟩, ?_⟩
    apply List.any_eq_true.mpr
    refine ⟨centralCellFace (x.add (unitAxis axis sgn)) axis (-sgn),
      mem_faces_iff.mpr ?_, opposite_neighbor hdir⟩
    refine ⟨x.add (unitAxis axis sgn), hneighbor, axis, -sgn, ?_, ?_, rfl⟩
    · simp [centralFaceDirections] at hdir ⊢
      rcases hdir with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
    · rw [neighbor_back hdir]
      exact houtq

private theorem cellLower_injective {f : Frame} (hf : f ∈ allFrames) (t : V3) :
    Function.Injective (cellLower f t) := by
  intro a b hab
  unfold allFrames at hf
  obtain ⟨perm, hperm, hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨sign, hsign, rfl⟩ := List.mem_map.mp hf
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases a with ⟨ax, ay, az⟩ <;> rcases b with ⟨bx, byv, bz⟩ <;>
    rcases t with ⟨tx, ty, tz⟩ <;>
    simp [cellLower, N3.get, V3.get, fr, n3, v] at hab ⊢ <;> omega

private theorem frame_cancel (f q : Frame)
    (hf : f ∈ allFrames) (hq : q ∈ allFrames) :
    f.mul (f.transpose.mul q) = q := by
  have hcheck : allFrames.all (fun f => allFrames.all fun q =>
      f.mul (f.transpose.mul q) == q) = true := by decide
  simpa using (List.all_eq_true.mp (List.all_eq_true.mp hcheck f hf) q hq)

private theorem shift_cancel (f : Frame) (hf : f ∈ allFrames) (t u : V3) :
    t.add (f.act ((f.transpose.act t).neg.add (f.transpose.act u))) = u := by
  unfold allFrames at hf
  obtain ⟨perm, hperm, hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨sign, hsign, rfl⟩ := List.mem_map.mp hf
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases t with ⟨tx, ty, tz⟩ <;> rcases u with ⟨ux, uy, uz⟩ <;>
    simp [Frame.transpose, Frame.act, V3.neg, V3.smul, V3.add,
      N3.get, V3.get, fr, n3, v] <;> ring

private theorem allFrames_mul_mem {f g : Frame}
    (hf : f ∈ allFrames) (hg : g ∈ allFrames) : f.mul g ∈ allFrames := by
  have hcheck : allFrames.all (fun f => allFrames.all fun g =>
      allFrames.contains (f.mul g)) = true := by decide
  exact List.contains_iff_mem.mp
    (List.all_eq_true.mp (List.all_eq_true.mp hcheck f hf) g hg)

private theorem frame_act_get (f : Frame) (a : V3) (i : Nat) (hi : i < 3) :
    (f.act a).get i = f.sign.get i * a.get (f.perm.get i) := by
  interval_cases i <;> rfl

private theorem frame_mul_sign_get_nat (f g : Frame) (i : Nat) (hi : i < 3) :
    (f.mul g).sign.get i = f.sign.get i * g.sign.get (f.perm.get i) := by
  interval_cases i <;> rfl

private theorem frame_mul_perm_get_nat (f g : Frame) (i : Nat) (hi : i < 3) :
    (f.mul g).perm.get i = g.perm.get (f.perm.get i) := by
  interval_cases i <;> rfl

private theorem frame_act_mul_int (f g : Frame) (hf : f ∈ allFrames)
    (a : V3) : (f.mul g).act a = f.act (g.act a) := by
  apply v3_eq
  · change ((f.mul g).act a).get 0 = (f.act (g.act a)).get 0
    rw [frame_act_get (f.mul g) a 0 (by omega),
      frame_act_get f (g.act a) 0 (by omega),
      frame_mul_sign_get_nat f g 0 (by omega),
      frame_mul_perm_get_nat f g 0 (by omega),
      frame_act_get g a (f.perm.get 0) (perm_lt_three hf 0)]
    ring
  · change ((f.mul g).act a).get 1 = (f.act (g.act a)).get 1
    rw [frame_act_get (f.mul g) a 1 (by omega),
      frame_act_get f (g.act a) 1 (by omega),
      frame_mul_sign_get_nat f g 1 (by omega),
      frame_mul_perm_get_nat f g 1 (by omega),
      frame_act_get g a (f.perm.get 1) (perm_lt_three hf 1)]
    ring
  · change ((f.mul g).act a).get 2 = (f.act (g.act a)).get 2
    rw [frame_act_get (f.mul g) a 2 (by omega),
      frame_act_get f (g.act a) 2 (by omega),
      frame_mul_sign_get_nat f g 2 (by omega),
      frame_mul_perm_get_nat f g 2 (by omega),
      frame_act_get g a (f.perm.get 2) (perm_lt_three hf 2)]
    ring

private theorem frame_mul_assoc {f g h : Frame}
    (hf : f ∈ allFrames) (hg : g ∈ allFrames) (hh : h ∈ allFrames) :
    (f.mul g).mul h = f.mul (g.mul h) := by
  apply frame_eq_of_rows
  intro i
  let j : Fin 3 := ⟨f.perm.get i, perm_lt_three hf i⟩
  constructor
  · calc
      ((f.mul g).mul h).perm.get i =
          h.perm.get ((f.mul g).perm.get i) := frame_mul_perm_get _ _ _
      _ = h.perm.get (g.perm.get (f.perm.get i)) := by
        rw [frame_mul_perm_get f g i]
      _ = (g.mul h).perm.get (f.perm.get i) := by
        simpa [j] using (frame_mul_perm_get g h j).symm
      _ = (f.mul (g.mul h)).perm.get i :=
        (frame_mul_perm_get f (g.mul h) i).symm
  · calc
      ((f.mul g).mul h).sign.get i =
          (f.mul g).sign.get i * h.sign.get ((f.mul g).perm.get i) :=
        frame_mul_sign_get _ _ _
      _ = (f.sign.get i * g.sign.get (f.perm.get i)) *
          h.sign.get (g.perm.get (f.perm.get i)) := by
        rw [frame_mul_sign_get f g i, frame_mul_perm_get f g i]
      _ = f.sign.get i *
          (g.sign.get (f.perm.get i) * h.sign.get (g.perm.get (f.perm.get i))) := by
        ring
      _ = f.sign.get i * (g.mul h).sign.get (f.perm.get i) := by
        rw [show (g.mul h).sign.get (f.perm.get i) =
          g.sign.get (f.perm.get i) * h.sign.get (g.perm.get (f.perm.get i)) by
            simpa [j] using frame_mul_sign_get g h j]
      _ = (f.mul (g.mul h)).sign.get i :=
        (frame_mul_sign_get f (g.mul h) i).symm

private theorem frame_act_add_int (f : Frame) (a b : V3) :
    f.act (a.add b) = (f.act a).add (f.act b) := by
  apply v3_eq
  · change (f.act (a.add b)).get 0 = ((f.act a).add (f.act b)).get 0
    rw [frame_act_get f _ 0 (by omega), v3_get_add]
    change f.sign.get 0 * (a.get (f.perm.get 0) + b.get (f.perm.get 0)) =
      f.sign.get 0 * a.get (f.perm.get 0) +
        f.sign.get 0 * b.get (f.perm.get 0)
    ring
  · change (f.act (a.add b)).get 1 = ((f.act a).add (f.act b)).get 1
    rw [frame_act_get f _ 1 (by omega), v3_get_add]
    change f.sign.get 1 * (a.get (f.perm.get 1) + b.get (f.perm.get 1)) =
      f.sign.get 1 * a.get (f.perm.get 1) +
        f.sign.get 1 * b.get (f.perm.get 1)
    ring
  · change (f.act (a.add b)).get 2 = ((f.act a).add (f.act b)).get 2
    rw [frame_act_get f _ 2 (by omega), v3_get_add]
    change f.sign.get 2 * (a.get (f.perm.get 2) + b.get (f.perm.get 2)) =
      f.sign.get 2 * a.get (f.perm.get 2) +
        f.sign.get 2 * b.get (f.perm.get 2)
    ring

private theorem pose_transform_assoc {a b c : Pose}
    (ha : a.frame ∈ allFrames) (hb : b.frame ∈ allFrames)
    (hc : c.frame ∈ allFrames) :
    (a.transform b).transform c = a.transform (b.transform c) := by
  rcases a with ⟨af, ashift⟩
  rcases b with ⟨bf, bt⟩
  rcases c with ⟨cf, ct⟩
  unfold Pose.transform
  simp only [po] at ha hb hc ⊢
  congr 1
  · exact frame_mul_assoc ha hb hc
  · rw [frame_act_mul_int af bf ha, frame_act_add_int]
    rcases ashift with ⟨ax, ay, az⟩
    rcases af.act bt with ⟨bx, byv, bz⟩
    rcases af.act (bf.act ct) with ⟨cx, cy, cz⟩
    apply v3_eq <;> simp [V3.add, v] <;> ring

private theorem pose_inverse_transform_self (p : Pose)
    (hp : p.frame ∈ allFrames) : p.inverse.transform p = rootPose := by
  rcases p with ⟨pf, pt⟩
  unfold Pose.inverse Pose.transform rootPose
  simp only [po] at hp ⊢
  congr 1
  · exact allFrames_transpose_mul pf hp
  · rcases pf.transpose.act pt with ⟨x, y, z⟩
    apply v3_eq <;> simp [V3.neg, V3.smul, V3.add, v]

private theorem rootPose_transform (p : Pose) : rootPose.transform p = p := by
  rcases p with ⟨⟨⟨p0, p1, p2⟩, ⟨s0, s1, s2⟩⟩, ⟨x, y, z⟩⟩
  simp [rootPose, Pose.transform, identityFrame, Frame.mul, Frame.act, po,
    N3.get, V3.get, V3.add, fr, n3, v]

private theorem pose_transform_root (p : Pose) (hp : p.frame ∈ allFrames) :
    p.transform rootPose = p := by
  have hframe : p.frame.mul identityFrame = p.frame := by
    have hcheck : allFrames.all (fun f => f.mul identityFrame == f) = true := by
      decide
    exact frame_eq_of_beq (List.all_eq_true.mp hcheck p.frame hp)
  rcases p with ⟨pf, pt⟩
  unfold Pose.transform rootPose
  simp only [po] at hp ⊢
  rw [hframe]
  have zero_get (i : Nat) : (v 0 0 0).get i = 0 := by
    rcases i with _ | i
    · rfl
    rcases i with _ | i <;> rfl
  have hzero : pf.act (v 0 0 0) = v 0 0 0 := by
    apply v3_eq
    · change pf.sign.x * (v 0 0 0).get pf.perm.x = 0
      rw [zero_get]
      ring
    · change pf.sign.y * (v 0 0 0).get pf.perm.y = 0
      rw [zero_get]
      ring
    · change pf.sign.z * (v 0 0 0).get pf.perm.z = 0
      rw [zero_get]
      ring
  rw [hzero]
  rcases pt with ⟨x, y, z⟩
  simp [V3.add, v]

private theorem pose_transform_left_cancel {a b c : Pose}
    (ha : a.frame ∈ allFrames) (hb : b.frame ∈ allFrames)
    (hc : c.frame ∈ allFrames) (h : a.transform b = a.transform c) : b = c := by
  have hi : a.inverse.frame ∈ allFrames := allFrames_transpose_mem _ ha
  have h' := congrArg (fun p => a.inverse.transform p) h
  rw [← pose_transform_assoc hi ha hb, ← pose_transform_assoc hi ha hc,
    pose_inverse_transform_self a ha, rootPose_transform,
    rootPose_transform] at h'
  exact h'

private theorem pose_transform_relative (p q : Pose)
    (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames) :
    p.transform (p.relative q) = q := by
  rcases p with ⟨pf, pt⟩
  rcases q with ⟨qf, qt⟩
  have hframe := frame_cancel pf qf hp hq
  have hshift := shift_cancel pf hp pt qt
  unfold Pose.relative Pose.inverse Pose.transform
  change po (pf.mul (pf.transpose.mul qf))
      (pt.add (pf.act ((pf.transpose.act pt).neg.add
        (pf.transpose.act qt)))) = po qf qt
  rw [hframe, hshift]

private theorem pose_relative_transform_transform {a b c d : Pose}
    (ha : a.frame ∈ allFrames) (hb : b.frame ∈ allFrames)
    (hc : c.frame ∈ allFrames) (hd : d.frame ∈ allFrames) :
    (a.transform b).relative (c.transform d) =
      b.relative ((a.relative c).transform d) := by
  let lhs := a.transform b
  let rhs := c.transform d
  let candidate := b.relative ((a.relative c).transform d)
  have hab : lhs.frame ∈ allFrames := allFrames_mul_mem ha hb
  have hcd : rhs.frame ∈ allFrames := allFrames_mul_mem hc hd
  have hac : (a.relative c).frame ∈ allFrames := allFrames_relative_mem ha hc
  have hacd : ((a.relative c).transform d).frame ∈ allFrames :=
    allFrames_mul_mem hac hd
  have hcandidate : candidate.frame ∈ allFrames :=
    allFrames_relative_mem hb hacd
  apply pose_transform_left_cancel hab
    (allFrames_relative_mem hab hcd) hcandidate
  rw [pose_transform_relative lhs rhs hab hcd]
  dsimp only [lhs, rhs, candidate]
  rw [pose_transform_assoc ha hb hcandidate]
  rw [pose_transform_relative b ((a.relative c).transform d) hb hacd]
  rw [← pose_transform_assoc ha hac hd]
  rw [pose_transform_relative a c ha hc]

/-- A signed permutation carries an even integral vector to an even integral
    vector.  This is structural in the three coordinate selectors; it does
    not enumerate the 48 frames. -/
private theorem frameAct_preserves_even {f : Frame} (hf : f ∈ allFrames)
    {a : V3}
    (ha : (a.x % 2 = 0 ∧ a.y % 2 = 0) ∧ a.z % 2 = 0) :
    ((f.act a).x % 2 = 0 ∧ (f.act a).y % 2 = 0) ∧
      (f.act a).z % 2 = 0 := by
  have hget (j : Nat) (hj : j < 3) : a.get j % 2 = 0 := by
    interval_cases j <;> simp_all [V3.get]
  constructor
  · constructor
    · change (f.sign.x * a.get f.perm.x) % 2 = 0
      rw [Int.mul_emod]
      simp [hget f.perm.x (allFrames_data hf).px]
    · change (f.sign.y * a.get f.perm.y) % 2 = 0
      rw [Int.mul_emod]
      simp [hget f.perm.y (allFrames_data hf).py]
  · change (f.sign.z * a.get f.perm.z) % 2 = 0
    rw [Int.mul_emod]
    simp [hget f.perm.z (allFrames_data hf).pz]

private theorem v3_add_preserves_even {a b : V3}
    (ha : (a.x % 2 = 0 ∧ a.y % 2 = 0) ∧ a.z % 2 = 0)
    (hb : (b.x % 2 = 0 ∧ b.y % 2 = 0) ∧ b.z % 2 = 0) :
    ((a.add b).x % 2 = 0 ∧ (a.add b).y % 2 = 0) ∧
      (a.add b).z % 2 = 0 := by
  rcases a with ⟨ax, ay, az⟩
  rcases b with ⟨bx, byv, bz⟩
  simp only [V3.add, v] at ha hb ⊢
  omega

/-- Even translations form a subgroup of the literal signed-pose group. -/
theorem evenPose_transform {p q : Pose} (hpf : p.frame ∈ allFrames)
    (hp : evenPose p = true) (hq : evenPose q = true) :
    evenPose (p.transform q) = true := by
  simp only [evenPose, Bool.and_eq_true, beq_iff_eq] at hp hq ⊢
  exact v3_add_preserves_even hp
    (frameAct_preserves_even hpf hq)

/-- If the relative phases from `p` to `q` and from `q` to `r` are even,
    then the relative phase from `p` to `r` is even. -/
theorem evenPose_relative_trans {p q r : Pose}
    (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames)
    (hr : r.frame ∈ allFrames)
    (hpq : evenPose (p.relative q) = true)
    (hqr : evenPose (q.relative r) = true) :
    evenPose (p.relative r) = true := by
  have hrel :
      (p.relative q).transform (q.relative r) = p.relative r := by
    apply pose_transform_left_cancel hp
      (allFrames_mul_mem (allFrames_relative_mem hp hq)
        (allFrames_relative_mem hq hr))
      (allFrames_relative_mem hp hr)
    rw [← pose_transform_assoc hp (allFrames_relative_mem hp hq)
      (allFrames_relative_mem hq hr)]
    rw [pose_transform_relative p q hp hq,
      pose_transform_relative q r hq hr,
      pose_transform_relative p r hp hr]
  rw [← hrel]
  exact evenPose_transform (allFrames_relative_mem hp hq) hpq hqr

def doubledPose (p : Pose) : Pose := po p.frame (p.shift.smul 2)

/-- Conversely to `halfPose_realizes_halvePose`, realization of a halved
    affine motion determines the literal pose obtained by doubling its
    integral shift.  No parity premise is needed in this direction. -/
theorem halfPose_realizes_doubledPose {g : RigidMotion} {p : Pose}
    (h : RealizesPose (halfPose g) p) :
    RealizesPose g (doubledPose p) := by
  constructor
  · intro x i
    have hlin : (halfPose g).linearIsometryEquiv = g.linearIsometryEquiv := by
      apply LinearIsometryEquiv.ext
      intro y
      rfl
    rw [← hlin]
    exact h.1 x i
  · intro i
    have horigin : halfPose g 0 = (2 : ℝ)⁻¹ • g 0 := by
      simp [halfPose, translation]
    have hi := congrArg (fun y : E3 => y i) horigin
    rw [h.2 i] at hi
    fin_cases i <;>
      change (g 0) _ = ((p.shift.smul 2).get _ : ℝ) <;>
      simp [smul_eq_mul, V3.smul, V3.get, v] at hi ⊢ <;>
      linarith

private theorem refine_as_transform {p u : Pose} (hu : u ∈ refine p) :
    ∃ c ∈ children, u = (doubledPose p).transform c := by
  unfold refine at hu
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hu
  refine ⟨c, hc, ?_⟩
  rfl

private theorem smul_sub_two (a b : V3) :
    (a.smul 2).sub (b.smul 2) = (a.sub b).smul 2 := by
  rcases a with ⟨ax, ay, az⟩
  rcases b with ⟨bx, byv, bz⟩
  apply v3_eq <;> simp [V3.smul, V3.sub, v] <;> ring

private theorem doubledPose_relative {p q : Pose} :
    (doubledPose p).relative (doubledPose q) = doubledPose (p.relative q) := by
  rcases p with ⟨pf, pt⟩
  rcases q with ⟨qf, qt⟩
  unfold doubledPose Pose.relative Pose.inverse Pose.transform
  simp only [po]
  congr 1
  rw [frameAct_smul pf.transpose pt 2,
    frameAct_smul pf.transpose qt 2]
  rcases pf.transpose.act pt with ⟨px, py, pz⟩
  rcases pf.transpose.act qt with ⟨qx, qy, qz⟩
  apply v3_eq <;>
    simp [V3.neg, V3.smul, V3.add, v] <;> ring

private theorem relative_refine_normalize {p q u w : Pose}
    (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames)
    (hu : u ∈ refine p) (hw : w ∈ refine q) :
    ∃ c ∈ children, ∃ z ∈ refine (p.relative q),
      u.relative w = c.relative z := by
  obtain ⟨c, hc, rfl⟩ := refine_as_transform hu
  obtain ⟨d, hd, rfl⟩ := refine_as_transform hw
  let z := (doubledPose (p.relative q)).transform d
  have hz : z ∈ refine (p.relative q) := by
    unfold refine
    apply List.mem_map.mpr
    exact ⟨d, hd, rfl⟩
  refine ⟨c, hc, z, hz, ?_⟩
  have hcp : c.frame ∈ allFrames := childFrame_mem_allFrames hc
  have hdp : d.frame ∈ allFrames := childFrame_mem_allFrames hd
  rw [pose_relative_transform_transform
    (show (doubledPose p).frame ∈ allFrames from hp)
    hcp (show (doubledPose q).frame ∈ allFrames from hq) hdp]
  rw [doubledPose_relative]

private theorem pose_relative_self (p : Pose) (hp : p.frame ∈ allFrames) :
    p.relative p = rootPose := pose_inverse_transform_self p hp

private theorem relative_refine_same_parent {p u w : Pose}
    (hp : p.frame ∈ allFrames) (hu : u ∈ refine p) (hw : w ∈ refine p) :
    ∃ c ∈ children, ∃ d ∈ children, u.relative w = c.relative d := by
  obtain ⟨c, hc, rfl⟩ := refine_as_transform hu
  obtain ⟨d, hd, rfl⟩ := refine_as_transform hw
  refine ⟨c, hc, d, hd, ?_⟩
  rw [pose_relative_transform_transform
    (show (doubledPose p).frame ∈ allFrames from hp)
    (childFrame_mem_allFrames hc)
    (show (doubledPose p).frame ∈ allFrames from hp)
    (childFrame_mem_allFrames hd)]
  rw [doubledPose_relative, pose_relative_self p hp]
  change c.relative ((doubledPose rootPose).transform d) = c.relative d
  rw [show doubledPose rootPose = rootPose by rfl, rootPose_transform]

private theorem body_transform_mem {p q : Pose}
    (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames) {a : V3} :
    a ∈ body (p.transform q) ↔
      ∃ b ∈ body q, a = cellLower p.frame p.shift b := by
  constructor
  · intro ha
    obtain ⟨d, hd, had⟩ := body_mem_iff.mp ha
    let b := cellLower q.frame q.shift d
    refine ⟨b, body_mem_iff.mpr ⟨d, hd, rfl⟩, ?_⟩
    rw [had]
    exact cellLower_comp p.frame q.frame p.shift q.shift d
      (allFrames_data hp) (allFrames_data hq)
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨d, hd, rfl⟩ := body_mem_iff.mp hb
    apply body_mem_iff.mpr
    refine ⟨d, hd, ?_⟩
    exact (cellLower_comp p.frame q.frame p.shift q.shift d
      (allFrames_data hp) (allFrames_data hq)).symm

private theorem body_relative_mem {p q : Pose}
    (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames) {a : V3} :
    a ∈ body q ↔
      ∃ b ∈ body (p.relative q), a = cellLower p.frame p.shift b := by
  have hpose := pose_transform_relative p q hp hq
  have hmul : p.frame.transpose.mul q.frame ∈ allFrames :=
    allFrames_relative_mem hp hq
  calc
    a ∈ body q ↔ a ∈ body (p.transform (p.relative q)) := by rw [hpose]
    _ ↔ ∃ b ∈ body (p.relative q),
        a = cellLower p.frame p.shift b := body_transform_mem hp hmul

private def centralGridDirections : List V3 :=
  centralFaceDirections.map fun d => unitAxis d.1 d.2

set_option maxHeartbeats 2000000 in
private theorem inverse_grid_direction {f : Frame} (hf : f ∈ allFrames)
    {n : V3} (hn : n ∈ centralGridDirections) :
    f.transpose.act n ∈ centralGridDirections ∧
      f.act (f.transpose.act n) = n := by
  unfold allFrames at hf
  obtain ⟨perm, hperm, hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨sign, hsign, rfl⟩ := List.mem_map.mp hf
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  simp [centralGridDirections, centralFaceDirections, unitAxis] at hn
  rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hn with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp [centralGridDirections, centralFaceDirections, Frame.transpose,
      Frame.act, unitAxis, N3.get, V3.get, fr, n3, v]

private theorem forward_grid_direction {f : Frame} (hf : f ∈ allFrames)
    {n : V3} (hn : n ∈ centralGridDirections) :
    f.act n ∈ centralGridDirections ∧ f.transpose.act (f.act n) = n := by
  have hcheck : allFrames.all (fun f => centralGridDirections.all fun n =>
      centralGridDirections.contains (f.act n) &&
        f.transpose.act (f.act n) == n) = true := by decide
  have hfcheck := List.all_eq_true.mp hcheck f hf
  have hncheck := List.all_eq_true.mp hfcheck n hn
  simp only [Bool.and_eq_true] at hncheck
  exact ⟨List.contains_iff_mem.mp hncheck.1, v3_eq_of_beq hncheck.2⟩

private theorem cellLower_add (f : Frame) (hf : f ∈ allFrames)
    (t a b : V3) :
    cellLower f t (a.add b) = (cellLower f t a).add (f.act b) := by
  unfold allFrames at hf
  obtain ⟨perm, hperm, hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨sign, hsign, rfl⟩ := List.mem_map.mp hf
  simp [coordinatePermutations] at hperm
  simp [signTriples] at hsign
  rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases t with ⟨tx, ty, tz⟩ <;> rcases a with ⟨ax, ay, az⟩ <;>
    rcases b with ⟨bx, byv, bz⟩ <;>
    simp [cellLower, Frame.act, V3.add, N3.get, V3.get, fr, n3, v] <;>
    ring_nf <;> simp

private theorem body_rootPose : body rootPose = chairCells := by decide

private theorem touch_relative_iff {p q : Pose}
    (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames) :
    touch p q = true ↔ touch rootPose (p.relative q) = true := by
  rw [touch_iff_cellFaceAdjacent, touch_iff_cellFaceAdjacent]
  constructor
  · rintro ⟨x, hx, axis, sgn, hdir, hneighbor, houtp, houtq⟩
    obtain ⟨d, hd, hxd⟩ := body_mem_iff.mp hx
    obtain ⟨e, he, hxe⟩ := (body_relative_mem hp hq).mp hneighbor
    let n := unitAxis axis sgn
    have hn : n ∈ centralGridDirections := by
      unfold centralGridDirections
      exact List.mem_map.mpr ⟨(axis, sgn), hdir, rfl⟩
    let nlocal := p.frame.transpose.act n
    have hnlocal : nlocal ∈ centralGridDirections :=
      (inverse_grid_direction hp hn).1
    have hact : p.frame.act nlocal = n := (inverse_grid_direction hp hn).2
    obtain ⟨dir, hdirLocal, hdirEq⟩ := List.mem_map.mp hnlocal
    rcases dir with ⟨axisLocal, sgnLocal⟩
    simp only at hdirEq
    have heq : e = d.add nlocal := by
      apply cellLower_injective hp p.shift
      calc
        cellLower p.frame p.shift e = x.add n := hxe.symm
        _ = (cellLower p.frame p.shift d).add n := by rw [← hxd]
        _ = cellLower p.frame p.shift (d.add nlocal) := by
          rw [cellLower_add p.frame hp, hact]
    refine ⟨d, ?_, axisLocal, sgnLocal, hdirLocal, ?_, ?_, ?_⟩
    · rw [body_rootPose]
      exact hd
    · rw [hdirEq, ← heq]
      exact he
    · intro hmem
      rw [body_rootPose] at hmem
      rw [hdirEq] at hmem
      have hglobal : cellLower p.frame p.shift (d.add nlocal) ∈ body p :=
        body_mem_iff.mpr ⟨d.add nlocal, hmem, rfl⟩
      rw [cellLower_add p.frame hp, hact, ← hxd] at hglobal
      exact houtp hglobal
    · intro hmem
      have hglobal : cellLower p.frame p.shift d ∈ body q :=
        (body_relative_mem hp hq).mpr ⟨d, hmem, rfl⟩
      rw [← hxd] at hglobal
      exact houtq hglobal
  · rintro ⟨d, hd, axis, sgn, hdir, hneighbor, houtRoot, houtRel⟩
    let nlocal := unitAxis axis sgn
    have hnlocal : nlocal ∈ centralGridDirections := by
      unfold centralGridDirections
      exact List.mem_map.mpr ⟨(axis, sgn), hdir, rfl⟩
    let n := p.frame.act nlocal
    have hn : n ∈ centralGridDirections := (forward_grid_direction hp hnlocal).1
    obtain ⟨dir, hdirGlobal, hdirEq⟩ := List.mem_map.mp hn
    rcases dir with ⟨axisGlobal, sgnGlobal⟩
    simp only at hdirEq
    let x := cellLower p.frame p.shift d
    have hdchair : d ∈ chairCells := by
      rw [← body_rootPose]
      exact hd
    have hx : x ∈ body p := body_mem_iff.mpr ⟨d, hdchair, rfl⟩
    have hqcell : cellLower p.frame p.shift (d.add nlocal) ∈ body q :=
      (body_relative_mem hp hq).mpr ⟨d.add nlocal, hneighbor, rfl⟩
    refine ⟨x, hx, axisGlobal, sgnGlobal, hdirGlobal, ?_, ?_, ?_⟩
    · rw [hdirEq]
      simpa only [x, n, cellLower_add p.frame hp] using hqcell
    · intro hmem
      rw [hdirEq] at hmem
      have hmem' : cellLower p.frame p.shift (d.add nlocal) ∈ body p := by
        simpa [x, n, cellLower_add p.frame hp] using hmem
      obtain ⟨e, he, heq⟩ := body_mem_iff.mp hmem'
      have hed : e = d.add nlocal := cellLower_injective hp p.shift
        (heq.symm.trans rfl)
      subst e
      exact houtRoot (by rw [body_rootPose]; exact he)
    · intro hmem
      obtain ⟨e, he, heq⟩ := (body_relative_mem hp hq).mp hmem
      have hed : e = d := by
        apply cellLower_injective hp p.shift
        calc
          cellLower p.frame p.shift e = x := heq.symm
          _ = cellLower p.frame p.shift d := rfl
      exact houtRel (hed ▸ he)

private theorem fine_neighbor_bases {a d b c : V3} {axis : Nat} {sgn : Int}
    (hb : b ∈ bits) (hc : c ∈ bits)
    (hdir : (axis, sgn) ∈ centralFaceDirections)
    (hadj : ((a.smul 2).add b).add (unitAxis axis sgn) =
      (d.smul 2).add c) :
    d = a ∨ d = a.add (unitAxis axis sgn) := by
  obtain ⟨hbx0, hbx2, hby0, hby2, hbz0, hbz2⟩ := bit_coordinate_bounds hb
  obtain ⟨hcx0, hcx2, hcy0, hcy2, hcz0, hcz2⟩ := bit_coordinate_bounds hc
  simp [centralFaceDirections] at hdir
  rcases a with ⟨ax, ay, az⟩
  rcases d with ⟨dx, dy, dz⟩
  rcases b with ⟨bx, byv, bz⟩
  rcases c with ⟨cx, cy, cz⟩
  simp only [V3.x, V3.y, V3.z] at hbx0 hbx2 hby0 hby2 hbz0 hbz2
  simp only [V3.x, V3.y, V3.z] at hcx0 hcx2 hcy0 hcy2 hcz0 hcz2
  rcases hdir with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    simp [V3.smul, V3.add, unitAxis, v] at hadj ⊢
  all_goals
    by_cases heq : dx = ax ∧ dy = ay ∧ dz = az
    · exact Or.inl heq
    · exact Or.inr (by omega)

private theorem refine_touch_implies_parent_touch
    (hchildren : childrenPartitionCheck = true)
    {p q u w : Pose} (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames)
    (hu : u ∈ refine p) (hw : w ∈ refine q)
    (hpq : (body p).Disjoint (body q))
    (htouch : touch u w = true) : touch p q = true := by
  obtain ⟨x, hxu, axis, sgn, hdir, hxw, _, _⟩ :=
    touch_iff_cellFaceAdjacent.mp htouch
  have hxRefine : x ∈ (refine p).flatMap body :=
    List.mem_flatMap.mpr ⟨u, hu, hxu⟩
  have hyRefine : x.add (unitAxis axis sgn) ∈
      (refine q).flatMap body :=
    List.mem_flatMap.mpr ⟨w, hw, hxw⟩
  obtain ⟨a, ha, b, hb, hxab⟩ :=
    refined_cell_in_parent_block hchildren hp hxRefine
  obtain ⟨d, hd, c, hc, hydc⟩ :=
    refined_cell_in_parent_block hchildren hq hyRefine
  have hadj : ((a.smul 2).add b).add (unitAxis axis sgn) =
      (d.smul 2).add c := by rw [← hxab, ← hydc]
  have hbase := fine_neighbor_bases hb hc hdir hadj
  have hne : d ≠ a := by
    intro hda
    rw [hda] at hd
    exact (List.disjoint_left.mp hpq) ha hd
  have hda : d = a.add (unitAxis axis sgn) := hbase.resolve_left hne
  apply touch_iff_cellFaceAdjacent.mpr
  refine ⟨a, ha, axis, sgn, hdir, ?_, ?_, ?_⟩
  · rwa [← hda]
  · intro hmem
    exact (List.disjoint_left.mp hpq) hmem (hda ▸ hd)
  · intro hmem
    exact (List.disjoint_left.mp hpq) ha hmem

private def PoseContactLanguage (xs : List Pose) : Prop :=
  ∀ p, p ∈ xs → ∀ q, q ∈ xs → p ≠ q →
    touch rootPose (p.relative q) = true → p.relative q ∈ closedContacts

private theorem internal_contact_mem {c d : Pose}
    (hc : c ∈ children) (hd : d ∈ children) (hne : c ≠ d)
    (htouch : touch c d = true) : c.relative d ∈ internalContacts := by
  unfold internalContacts
  rw [List.mem_eraseDups]
  apply List.mem_filterMap.mpr
  refine ⟨(c, d), ?_, ?_⟩
  · unfold allPairs
    apply List.mem_flatMap.mpr
    refine ⟨c, hc, ?_⟩
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  · simp [hne, htouch]

private theorem internal_contact_closed {e : Pose} (he : e ∈ internalContacts) :
    e ∈ closedContacts := by
  unfold closedContacts closureStep union
  rw [List.mem_eraseDups]
  exact List.mem_append_left _ he

private theorem closure_offspring_mem {e c z : Pose}
    (he : e ∈ closedContacts) (hc : c ∈ children)
    (hz : z ∈ refine e) (htouch : touch c z = true) :
    c.relative z ∈ closureStep closedContacts := by
  unfold closureStep union
  rw [List.mem_eraseDups]
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨e, he, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨z, hz, by simp [htouch]⟩

private theorem closureStep_closed_subset
    (hcontacts : contactClosureCheck = true) {e : Pose}
    (he : e ∈ closureStep closedContacts) : e ∈ closedContacts := by
  have hset : setEq (closureStep closedContacts) closedContacts = true := by
    unfold contactClosureCheck at hcontacts
    simp only [Bool.and_eq_true] at hcontacts
    aesop
  simp only [setEq, Bool.and_eq_true, subset] at hset
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hset.1 e he)

set_option maxHeartbeats 2000000 in
private theorem refine_contact_language
    (hchildren : childrenPartitionCheck = true)
    (hcontacts : contactClosureCheck = true) {xs : List Pose}
    (hframes : ∀ p ∈ xs, p.frame ∈ allFrames)
    (hcells : (xs.flatMap body).Nodup)
    (hlanguage : PoseContactLanguage xs) :
    PoseContactLanguage (xs.flatMap refine) := by
  intro u hu w hw hne htouchRelative
  obtain ⟨p, hp, hup⟩ := List.mem_flatMap.mp hu
  obtain ⟨q, hq, hwq⟩ := List.mem_flatMap.mp hw
  have hpf := hframes p hp
  have hqf := hframes q hq
  have huf := refine_frame_mem_allFrames hpf hup
  have hwf := refine_frame_mem_allFrames hqf hwq
  have htouch : touch u w = true :=
    (touch_relative_iff huf hwf).mpr htouchRelative
  by_cases hpq : p = q
  · subst q
    obtain ⟨c, hc, d, hd, hrel⟩ :=
      relative_refine_same_parent hpf hup hwq
    have hcd : c ≠ d := by
      intro hcd
      subst d
      have hroot : c.relative c = rootPose :=
        pose_relative_self c (childFrame_mem_allFrames hc)
      have huw : u.relative w = rootPose := hrel.trans hroot
      have htransport := pose_transform_relative u w huf hwf
      rw [huw, pose_transform_root u huf] at htransport
      exact hne htransport
    have htouchCD : touch c d = true := by
      apply (touch_relative_iff (childFrame_mem_allFrames hc)
        (childFrame_mem_allFrames hd)).mpr
      rwa [← hrel]
    rw [hrel]
    exact internal_contact_closed (internal_contact_mem hc hd hcd htouchCD)
  · have hparentDisjoint : (body p).Disjoint (body q) := by
      have hpair := (List.nodup_flatMap.mp hcells).2
      exact pairwise_rel_of_mem_ne (fun h => h.symm) hpair hp hq hpq
    have hparentTouch : touch p q = true :=
      refine_touch_implies_parent_touch hchildren hpf hqf hup hwq
        hparentDisjoint htouch
    have hparentRelative : touch rootPose (p.relative q) = true :=
      (touch_relative_iff hpf hqf).mp hparentTouch
    have heClosed : p.relative q ∈ closedContacts :=
      hlanguage p hp q hq hpq hparentRelative
    obtain ⟨c, hc, z, hz, hrel⟩ :=
      relative_refine_normalize hpf hqf hup hwq
    have hef := allFrames_relative_mem hpf hqf
    have hzf := refine_frame_mem_allFrames hef hz
    have htouchCZ : touch c z = true := by
      have htouchCZRelative : touch rootPose (c.relative z) = true := by
        rw [← hrel]
        exact htouchRelative
      apply (touch_relative_iff (childFrame_mem_allFrames hc) hzf).mpr
      exact htouchCZRelative
    have hclosed : c.relative z ∈ closedContacts :=
      closureStep_closed_subset hcontacts
        (closure_offspring_mem heClosed hc hz htouchCZ)
    exact hrel.symm ▸ hclosed

private theorem hashDedup_contact_language {xs : List Pose}
    (h : PoseContactLanguage xs) : PoseContactLanguage (hashDedup xs) := by
  intro p hp q hq hne htouch
  exact h p (mem_hashDedup_iff.mp hp) q (mem_hashDedup_iff.mp hq) hne htouch

private theorem twoRefinements_contact_language
    (hchildren : childrenPartitionCheck = true)
    (hcontacts : contactClosureCheck = true) {xs : List Pose}
    (hframes : ∀ p ∈ xs, p.frame ∈ allFrames)
    (hcells : (xs.flatMap body).Nodup)
    (hlanguage : PoseContactLanguage xs) :
    PoseContactLanguage (twoRefinements xs) := by
  have hfirstLanguage := refine_contact_language hchildren hcontacts
    hframes hcells hlanguage
  have hfirstCells : ((xs.flatMap refine).flatMap body).Nodup :=
    refine_flat_cells_nodup hchildren hframes hcells
  have hfirstFrames : ∀ p ∈ xs.flatMap refine, p.frame ∈ allFrames := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.mp hp
    exact refine_frame_mem_allFrames (hframes q hq) hpq
  have hsecondLanguage := refine_contact_language hchildren hcontacts
    hfirstFrames hfirstCells hfirstLanguage
  unfold twoRefinements
  exact hashDedup_contact_language hsecondLanguage

private theorem hierarchyPoseLevel_contact_language
    (hchildren : childrenPartitionCheck = true)
    (hcontacts : contactClosureCheck = true) :
    ∀ n : Nat, PoseContactLanguage (hierarchyPoseLevel n) := by
  intro n
  induction n with
  | zero =>
      intro p hp q hq hne _
      simp only [hierarchyPoseLevel, List.mem_singleton] at hp hq
      exact False.elim (hne (hp.trans hq.symm))
  | succ n ih =>
      exact twoRefinements_contact_language hchildren hcontacts
        (hierarchyPoseLevel_frames n)
        (hierarchyPoseLevel_cells_nodup hchildren n) ih

private theorem shiftedPose_relative (s : V3) {p q : Pose} :
    (po p.frame (p.shift.sub s)).relative
      (po q.frame (q.shift.sub s)) = p.relative q := by
  rcases p with ⟨pf, pt⟩
  rcases q with ⟨qf, qt⟩
  unfold Pose.relative Pose.inverse Pose.transform
  simp only [po]
  congr 1
  rw [frame_act_sub, frame_act_sub]
  rcases pf.transpose.act pt with ⟨px, py, pz⟩
  rcases pf.transpose.act qt with ⟨qx, qy, qz⟩
  rcases pf.transpose.act s with ⟨sx, sy, sz⟩
  apply v3_eq <;>
    simp [V3.neg, V3.smul, V3.add, V3.sub, v] <;> ring

private theorem translatedPatch_contact_language {amount : Int} {xs : List Pose}
    (h : PoseContactLanguage xs) :
    PoseContactLanguage (translatedPatch amount xs) := by
  intro p hp q hq hne htouch
  unfold translatedPatch at hp hq
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
  let s := v amount amount amount
  have hrel := shiftedPose_relative s (p := p0) (q := q0)
  have hpq : p0 ≠ q0 := by
    intro heq
    subst q0
    exact hne rfl
  rw [hrel] at htouch ⊢
  exact h p0 hp0 q0 hq0 hpq htouch

private theorem hierarchyPatch_contact_language
    (hchildren : childrenPartitionCheck = true)
    (hcontacts : contactClosureCheck = true) (n : Nat) :
    PoseContactLanguage (hierarchyPatch n) := by
  unfold hierarchyPatch
  exact translatedPatch_contact_language
    (hierarchyPoseLevel_contact_language hchildren hcontacts n)

private theorem hierarchyPatch_frames (n : Nat) {p : Pose}
    (hp : p ∈ hierarchyPatch n) : p.frame ∈ allFrames := by
  unfold hierarchyPatch translatedPatch at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hierarchyPoseLevel_frames n q hq

private theorem hierarchyPatch_mono (hnested : HierarchyPatchesNested)
    {m n : Nat} (hmn : m ≤ n) {p : Pose} (hp : p ∈ hierarchyPatch m) :
    p ∈ hierarchyPatch n := by
  induction n, hmn using Nat.le_induction with
  | base => exact hp
  | succ n _ ih => exact hnested n p ih

/-- R§9 contact-language induction: sibling contacts are the 21 internal
contacts and cross-parent contacts remain in the 30-state refinement fixed
point.  Centering translations and passage to the nested union preserve the
relative pose. -/
theorem nested_contact_language
    (hchildren : childrenPartitionCheck = true)
    (hcontacts : contactClosureCheck = true)
    (hnestedControl : nestedPatchControlsCheck = true) :
    ClosedContactFaceLanguage hierarchyPlacements := by
  have hnested := hierarchy_patch_nesting hnestedControl
  intro g h hg hh hne hadj
  obtain ⟨n, p, hp, hgp⟩ := hg
  obtain ⟨m, q, hq, hhq⟩ := hh
  obtain ⟨r, hrf, hr, htouch⟩ := hadj
  let N := max n m
  have hpN : p ∈ hierarchyPatch N :=
    hierarchyPatch_mono hnested (Nat.le_max_left n m) hp
  have hqN : q ∈ hierarchyPatch N :=
    hierarchyPatch_mono hnested (Nat.le_max_right n m) hq
  have hpf := hierarchyPatch_frames N hpN
  have hqf := hierarchyPatch_frames N hqN
  have hrelReal := realizesPose_relative hgp hhq hpf hqf
  have hre : r = p.relative q :=
    realizesPose_pose_unique hrf (allFrames_relative_mem hpf hqf) hr hrelReal
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hne (realizesPose_unique hgp hhq)
  refine ⟨p.relative q, ?_, hrelReal⟩
  apply hierarchyPatch_contact_language hchildren hcontacts N p hpN q hqN hpq
  rwa [← hre]

/-! ## Geometric assembly of the nested baseline hierarchy

The remaining work in R§9 is purely about the undeformed integral chair.  We
first realize every literal signed-permutation pose as an affine isometry and
identify its image of `P` with the union of the literal cells in `body p`.
-/

private def frameLinearMap (f : Frame) : E3 →ₗ[ℝ] E3 where
  toFun := frameActRealVector f
  map_add' := by
    intro x y
    apply PiLp.ext
    intro i
    simp only [frameActRealVector_apply]
    by_cases h : f.perm.get i < 3 <;>
      simp [frameActReal, frameCoordinate, h] <;> ring
  map_smul' := by
    intro c x
    apply PiLp.ext
    intro i
    simp only [frameActRealVector_apply]
    by_cases h : f.perm.get i < 3 <;>
      simp [frameActReal, frameCoordinate, h] <;> ring

private def frameLinearIsometry (f : Frame) (hf : f ∈ allFrames) :
    E3 →ₗᵢ[ℝ] E3 where
  toLinearMap := frameLinearMap f
  norm_map' := by
    intro x
    change ‖frameActRealVector f x‖ = ‖x‖
    have hsq : ‖frameActRealVector f x‖ ^ 2 = ‖x‖ ^ 2 := by
      unfold allFrames at hf
      obtain ⟨perm, hperm, hf⟩ := List.mem_flatMap.mp hf
      obtain ⟨sign, hsign, hf⟩ := List.mem_map.mp hf
      subst f
      simp [coordinatePermutations] at hperm
      simp [signTriples] at hsign
      rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
        rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        simp [frameActRealVector, frameActReal, frameCoordinate,
          EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, fr, n3, v,
          N3.get, V3.get] <;> ring
    nlinarith [norm_nonneg (frameActRealVector f x), norm_nonneg x]

private noncomputable def frameLinearEquiv (f : Frame) (hf : f ∈ allFrames) :
    E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.ofSurjective (frameLinearIsometry f hf) (by
    intro y
    refine ⟨frameActRealVector f.transpose y, ?_⟩
    exact frameActReal_transpose_right f hf y)

/-- The canonical affine-isometric realization of a literal signed pose. -/
private noncomputable def rigidMotionOfPose (p : Pose)
    (hp : p.frame ∈ allFrames) : RigidMotion :=
  AffineIsometryEquiv.mk'
    (fun x => frameLinearEquiv p.frame hp x + scaledV3 1 p.shift)
    (frameLinearEquiv p.frame hp) 0 (by intro x; simp)

private theorem rigidMotionOfPose_realizes (p : Pose)
    (hp : p.frame ∈ allFrames) :
    RealizesPose (rigidMotionOfPose p hp) p := by
  constructor
  · intro x i
    change frameActRealVector p.frame x i = frameActReal p.frame x i
    rfl
  · intro i
    simp [rigidMotionOfPose, scaledV3]

private theorem realizesPose_apply_vector {g : RigidMotion} {p : Pose}
    (hg : RealizesPose g p) (x : E3) :
    g x = frameActRealVector p.frame x + scaledV3 1 p.shift := by
  have hmap := g.map_vadd (0 : E3) x
  simp only [vadd_eq_add, add_zero] at hmap
  rw [hmap, realizesPose_linear_vector hg, realizesPose_origin_vector hg]

/- A realized signed-permutation pose sends a native unit cell exactly to
the closed unit cell with the literal lower-corner convention. -/
set_option maxHeartbeats 2000000 in
private theorem realizesPose_unitCube {g : RigidMotion} {p : Pose}
    (hp : p.frame ∈ allFrames) (hg : RealizesPose g p) (d : V3) :
    g '' unitCube d = unitCube (cellLower p.frame p.shift d) := by
  rcases p with ⟨f, t⟩
  change f ∈ allFrames at hp
  change RealizesPose g (po f t) at hg
  change g '' unitCube d = unitCube (cellLower f t d)
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    have h0 := congrArg (fun z : E3 => z (0 : Fin 3))
      (realizesPose_apply_vector hg x)
    have h1 := congrArg (fun z : E3 => z (1 : Fin 3))
      (realizesPose_apply_vector hg x)
    have h2 := congrArg (fun z : E3 => z (2 : Fin 3))
      (realizesPose_apply_vector hg x)
    have hx0 := hx (0 : Fin 3)
    have hx1 := hx (1 : Fin 3)
    have hx2 := hx (2 : Fin 3)
    intro i
    unfold allFrames at hp
    obtain ⟨perm, hperm, hf⟩ := List.mem_flatMap.mp hp
    obtain ⟨sign, hsign, hf⟩ := List.mem_map.mp hf
    subst f
    simp [coordinatePermutations] at hperm
    simp [signTriples] at hsign
    rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      fin_cases i
    all_goals
      simp [frameActRealVector, frameActReal, frameCoordinate, cellLower,
        scaledV3, po, fr, n3, v, N3.get, V3.get]
        at h0 h1 h2 hx0 hx1 hx2 ⊢
    all_goals
      first
      | rw [h0]; constructor <;> linarith
      | rw [h1]; constructor <;> linarith
      | rw [h2]; constructor <;> linarith
  · intro y hy
    let x : E3 := g⁻¹ y
    have hxy : g x = y := g.apply_symm_apply y
    refine ⟨x, ?_, hxy⟩
    have h0 := congrArg (fun z : E3 => z (0 : Fin 3))
      (realizesPose_apply_vector hg x)
    have h1 := congrArg (fun z : E3 => z (1 : Fin 3))
      (realizesPose_apply_vector hg x)
    have h2 := congrArg (fun z : E3 => z (2 : Fin 3))
      (realizesPose_apply_vector hg x)
    rw [hxy] at h0 h1 h2
    have hy0 := hy (0 : Fin 3)
    have hy1 := hy (1 : Fin 3)
    have hy2 := hy (2 : Fin 3)
    intro i
    unfold allFrames at hp
    obtain ⟨perm, hperm, hf⟩ := List.mem_flatMap.mp hp
    obtain ⟨sign, hsign, hf⟩ := List.mem_map.mp hf
    subst f
    simp [coordinatePermutations] at hperm
    simp [signTriples] at hsign
    rcases hperm with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      rcases hsign with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      fin_cases i <;>
      simp [frameActRealVector, frameActReal, frameCoordinate, cellLower,
        scaledV3, po, fr, n3, v, N3.get, V3.get] at h0 h1 h2 hy0 hy1 hy2 ⊢ <;>
      constructor <;> linarith

/-- The geometric image of the chair is exactly the union of the seven
literal body cells of the realized pose. -/
private theorem realizesPose_image_P {g : RigidMotion} {p : Pose}
    (hp : p.frame ∈ allFrames) (hg : RealizesPose g p) :
    g '' P = cubesOf (body p) := by
  ext x
  constructor
  · rintro ⟨y, ⟨d, hd, hyd⟩, rfl⟩
    refine ⟨cellLower p.frame p.shift d,
      body_mem_iff.mpr ⟨d, hd, rfl⟩, ?_⟩
    rw [← realizesPose_unitCube hp hg d]
    exact ⟨y, hyd, rfl⟩
  · rintro ⟨a, ha, hxa⟩
    obtain ⟨d, hd, rfl⟩ := body_mem_iff.mp ha
    rw [← realizesPose_unitCube hp hg d] at hxa
    obtain ⟨y, hy, rfl⟩ := hxa
    exact ⟨y, ⟨d, hd, hy⟩, rfl⟩

private def cubeInteriorsOf (xs : List V3) : Set E3 :=
  {x | ∃ a ∈ xs, x ∈ interior (unitCube a)}

private theorem cubeInteriorsOf_nil :
    cubeInteriorsOf [] = (∅ : Set E3) := by
  ext x
  simp [cubeInteriorsOf]

private theorem cubeInteriorsOf_cons (a : V3) (xs : List V3) :
    cubeInteriorsOf (a :: xs) =
      interior (unitCube a) ∪ cubeInteriorsOf xs := by
  ext x
  simp [cubeInteriorsOf]

/-- The open cores of a finite integral cubical body are dense in that body,
including across internal faces. -/
private theorem closure_cubeInteriorsOf (xs : List V3) :
    closure (cubeInteriorsOf xs) = cubesOf xs := by
  induction xs with
  | nil => simp [cubeInteriorsOf_nil, cubesOf_nil]
  | cons a xs ih =>
      rw [cubeInteriorsOf_cons, cubesOf_cons, closure_union,
        unitCube_regularClosed, ih]

private theorem distinct_unitCube_interiors_disjoint {a b : V3}
    (hab : a ≠ b) :
    Disjoint (interior (unitCube a)) (interior (unitCube b)) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  let e := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  have hpreA : unitCube a = e ⁻¹' coordinateBox a := unitCube_eq_preimage a
  have hpreB : unitCube b = e ⁻¹' coordinateBox b := unitCube_eq_preimage b
  rw [hpreA, ← e.preimage_interior, coordinateBox_interior] at hxa
  rw [hpreB, ← e.preimage_interior, coordinateBox_interior] at hxb
  simp only [Set.mem_preimage] at hxa hxb
  have hxa' : ∀ i : Fin 3,
      (a.get i : ℝ) < x i ∧ x i < (a.get i : ℝ) + 1 := by
    simpa [coordinateOpenBox, e, PiLp.homeomorph, WithLp.equiv] using hxa
  have hxb' : ∀ i : Fin 3,
      (b.get i : ℝ) < x i ∧ x i < (b.get i : ℝ) + 1 := by
    simpa [coordinateOpenBox, e, PiLp.homeomorph, WithLp.equiv] using hxb
  apply hab
  apply v3_eq
  · have ha := hxa' (0 : Fin 3)
    have hb := hxb' (0 : Fin 3)
    have h1 : a.x < b.x + 1 := by exact_mod_cast (lt_trans ha.1 hb.2)
    have h2 : b.x < a.x + 1 := by exact_mod_cast (lt_trans hb.1 ha.2)
    omega
  · have ha := hxa' (1 : Fin 3)
    have hb := hxb' (1 : Fin 3)
    have h1 : a.y < b.y + 1 := by exact_mod_cast (lt_trans ha.1 hb.2)
    have h2 : b.y < a.y + 1 := by exact_mod_cast (lt_trans hb.1 ha.2)
    omega
  · have ha := hxa' (2 : Fin 3)
    have hb := hxb' (2 : Fin 3)
    have h1 : a.z < b.z + 1 := by exact_mod_cast (lt_trans ha.1 hb.2)
    have h2 : b.z < a.z + 1 := by exact_mod_cast (lt_trans hb.1 ha.2)
    omega

/-- Two finite unions of integral unit cubes have disjoint interiors whenever
their lower-corner lists are disjoint.  The density argument handles points
on internal faces of either union. -/
private theorem cubesOf_disjoint_interiors {xs ys : List V3}
    (hxy : xs.Disjoint ys) :
    Disjoint (interior (cubesOf xs)) (interior (cubesOf ys)) := by
  rw [Set.disjoint_left]
  intro x hx hy
  let O : Set E3 := interior (cubesOf xs) ∩ interior (cubesOf ys)
  have hO : IsOpen O := isOpen_interior.inter isOpen_interior
  have hxcl : x ∈ closure (cubeInteriorsOf xs) := by
    rw [closure_cubeInteriorsOf]
    exact interior_subset hx
  obtain ⟨y, ⟨hyO, hycore⟩⟩ :=
    (mem_closure_iff.mp hxcl O hO ⟨hx, hy⟩)
  obtain ⟨a, haxs, hya⟩ := hycore
  let Oa : Set E3 := interior (unitCube a) ∩ interior (cubesOf ys)
  have hOa : IsOpen Oa := isOpen_interior.inter isOpen_interior
  have hycl : y ∈ closure (cubeInteriorsOf ys) := by
    rw [closure_cubeInteriorsOf]
    exact interior_subset hyO.2
  obtain ⟨z, ⟨⟨hza, hzys⟩, hzcore⟩⟩ :=
    (mem_closure_iff.mp hycl Oa hOa ⟨hya, hyO.2⟩)
  obtain ⟨b, hbys, hzb⟩ := hzcore
  have hab : a ≠ b := by
    intro heq
    subst b
    exact (List.disjoint_left.mp hxy) haxs hbys
  exact Set.disjoint_left.mp (distinct_unitCube_interiors_disjoint hab) hza hzb

private theorem orientationGroup_mul_child_mem {f : Frame} {c : Pose}
    (hf : f ∈ orientationGroup) (hc : c ∈ children) :
    f.mul c.frame ∈ orientationGroup := by
  have hcheck : orientationGroup.all (fun f =>
      children.all fun c => orientationGroup.contains (f.mul c.frame)) = true := by
    decide
  have hfcheck := List.all_eq_true.mp hcheck f hf
  have hccheck := List.all_eq_true.mp hfcheck c hc
  exact List.contains_iff_mem.mp hccheck

private theorem hierarchyPoseLevel_orientations :
    ∀ n : Nat, ∀ p ∈ hierarchyPoseLevel n, p.frame ∈ orientationGroup := by
  intro n
  induction n with
  | zero =>
      intro p hp
      simp only [hierarchyPoseLevel, List.mem_singleton] at hp
      subst p
      decide
  | succ n ih =>
      intro p hp
      change p ∈ twoRefinements (hierarchyPoseLevel n) at hp
      unfold twoRefinements hashDedup at hp
      rw [Std.HashSet.mem_toList, Std.HashSet.mem_ofList,
        List.contains_iff_mem] at hp
      obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.mp hp
      obtain ⟨r, hr, hqr⟩ := List.mem_flatMap.mp hq
      unfold refine at hqr hpq
      obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.mp hqr
      obtain ⟨c₂, hc₂, rfl⟩ := List.mem_map.mp hpq
      exact orientationGroup_mul_child_mem
        (orientationGroup_mul_child_mem (ih r hr) hc₁) hc₂

private theorem hierarchyPatch_orientation {n : Nat} {p : Pose}
    (hp : p ∈ hierarchyPatch n) : p.frame ∈ orientationGroup := by
  unfold hierarchyPatch translatedPatch at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hierarchyPoseLevel_orientations n q hq

private noncomputable def registeredPose_of_realizes {g : RigidMotion} {p : Pose}
    (hframe : p.frame ∈ orientationGroup) (hreal : RealizesPose g p) :
    RegisteredPose g := by
  let i := Classical.choose (List.mem_iff_get.mp hframe)
  have hi := Classical.choose_spec (List.mem_iff_get.mp hframe)
  have hlen : orientationGroup.length = 24 := by decide
  let j : Fin 24 := ⟨i.val, by simpa [hlen] using i.isLt⟩
  have hjlt : j.val < orientationGroup.length := by
    simpa [hlen] using j.isLt
  have hget : getD orientationGroup j.val identityFrame = p.frame := by
    simpa [getD, hjlt, j] using hi
  refine {
    frameIndex := j
    shift := p.shift
    linear_eq := ?_
    origin_eq := hreal.2
  }
  intro x k
  rw [hget]
  exact hreal.1 x k

/-- R§9 baseline assembly: the directed union of the centered hierarchy
patches is a registered tiling by the literal seven-cube chair. -/
theorem nested_baseline_assembly
    (hnested : HierarchyPatchesNested)
    (hdisjoint : HierarchyCellsDisjoint)
    (hcontain : HierarchyBoxContainment)
    (hexhaust : HierarchyBoxesExhaust) :
    Nonempty (RegisteredBaselineTiling hierarchyPlacements) := by
  let T : Tiling P := {
    placements := hierarchyPlacements
    disjoint_interiors := by
      intro g h hg hh hne
      obtain ⟨n, p, hp, hgp⟩ := hg
      obtain ⟨m, q, hq, hhq⟩ := hh
      let N := max n m
      have hpN : p ∈ hierarchyPatch N :=
        hierarchyPatch_mono hnested (Nat.le_max_left n m) hp
      have hqN : q ∈ hierarchyPatch N :=
        hierarchyPatch_mono hnested (Nat.le_max_right n m) hq
      have hpq : p ≠ q := by
        intro hpq
        subst q
        exact hne (realizesPose_unique hgp hhq)
      have hflat := List.nodup_flatMap.mp (hdisjoint N)
      have hpqCells : (body p).Disjoint (body q) :=
        pairwise_rel_of_mem_ne (fun h => h.symm) hflat.2 hpN hqN hpq
      rw [realizesPose_image_P (hierarchyPatch_frames N hpN) hgp,
        realizesPose_image_P (hierarchyPatch_frames N hqN) hhq]
      exact cubesOf_disjoint_interiors hpqCells
    covers := by
      intro x
      obtain ⟨n, hxn⟩ := hexhaust x
      obtain ⟨a, ha, hxa⟩ := hcontain n hxn
      obtain ⟨p, hp, hap⟩ := List.mem_flatMap.mp ha
      have hpf := hierarchyPatch_frames n hp
      let g := rigidMotionOfPose p hpf
      have hreal : RealizesPose g p := rigidMotionOfPose_realizes p hpf
      refine ⟨g, ⟨n, p, hp, hreal⟩, ?_⟩
      rw [realizesPose_image_P hpf hreal]
      exact ⟨a, hap, hxa⟩
  }
  refine ⟨{
    tiling := T
    placements_eq := rfl
    registered := ?_
  }⟩
  refine ⟨{
    ambient := 1
    pose := ?_
  }⟩
  intro g hg
  let n := Classical.choose hg
  have hn := Classical.choose_spec hg
  let p := Classical.choose hn
  have hpdata := Classical.choose_spec hn
  have hp : p ∈ hierarchyPatch n := hpdata.1
  have hreal : RealizesPose g p := hpdata.2
  simpa using registeredPose_of_realizes
    (hierarchyPatch_orientation hp) hreal

/-- The complete R§9 baseline endpoint: the assembled hierarchy tiling has
only face adjacencies licensed by the literal 44-contact atlas.  This is the
atlas-strengthened form consumed by geometric realization. -/
theorem nested_atlas_baseline_assembly
    (hchildren : childrenPartitionCheck = true)
    (hcontacts : contactClosureCheck = true)
    (hnested : nestedPatchControlsCheck = true) :
    Nonempty (AtlasBaselineTiling hierarchyPlacements) := by
  have hnests : HierarchyPatchesNested := hierarchy_patch_nesting hnested
  have hdisjoint : HierarchyCellsDisjoint := hierarchy_cells_disjoint hchildren
  have hboxes : HierarchyBoxContainment :=
    hierarchy_box_containment hchildren hierarchy_cell_controls
  let B := Classical.choice
    (nested_baseline_assembly hnests hdisjoint hboxes
      hierarchy_boxes_exhaust)
  let C : HierarchyBaselineTiling hierarchyPlacements := {
    toRegisteredBaselineTiling := B
    closed_faces := nested_contact_language hchildren hcontacts hnested
  }
  exact ⟨C.toAtlas atlas_44⟩

private theorem external_neighbor_shell {f : Frame} (hf : f ∈ allFrames)
    {t d e n : V3} (hd : d ∈ chairCells) (hn : n ∈ centralGridDirections)
    (heq : cellLower f t e = (cellLower f t d).add n)
    (hout : (cellLower f t d).add n ∉ body (po f t)) :
    e ∈ shellCells := by
  let nlocal := f.transpose.act n
  have hnlocal := (inverse_grid_direction hf hn).1
  have hact := (inverse_grid_direction hf hn).2
  have htrans : cellLower f t (d.add nlocal) =
      (cellLower f t d).add n := by rw [cellLower_add f hf, hact]
  have he : e = d.add nlocal :=
    cellLower_injective hf t (heq.trans htrans.symm)
  subst e
  have hnotchair : d.add nlocal ∉ chairCells := by
    intro hchair
    exact hout (body_mem_iff.mpr ⟨d.add nlocal, hchair, htrans.symm⟩)
  have hcand : d.add nlocal ∈
      chairCells.flatMap fun x => centralFaceDirections.map fun a =>
        x.add (unitAxis a.1 a.2) := by
    apply List.mem_flatMap.mpr
    refine ⟨d, hd, ?_⟩
    obtain ⟨a, ha, han⟩ := List.mem_map.mp hnlocal
    exact List.mem_map.mpr ⟨a, ha, by rw [han]⟩
  have hneighbor : d.add nlocal ∈ neighborShell := by
    unfold neighborShell diff
    apply List.mem_filter.mpr
    refine ⟨List.mem_eraseDups.mpr hcand, ?_⟩
    have hcfalse : chairCells.contains (d.add nlocal) = false := by
      apply Bool.eq_false_iff.mpr
      intro hc
      exact hnotchair (List.contains_iff_mem.mp hc)
    rw [hcfalse]
    decide
  have hatlas := atlas_44
  unfold atlasCheck at hatlas
  simp only [Bool.and_eq_true] at hatlas
  have hset : setEq neighborShell shellCells = true := by aesop
  simp only [setEq, Bool.and_eq_true, subset] at hset
  apply List.contains_iff_mem.mp
  exact List.all_eq_true.mp hset.1 (d.add nlocal) hneighbor

/-- Lattice face-touching yields ownership of a shell cell after normalizing
by the first literal pose. -/
theorem touch_relative_has_shell_cell {p q : Pose}
    (hp : p.frame ∈ allFrames) (hq : q.frame ∈ allFrames)
    (htouch : touch p q = true) :
    ∃ c ∈ shellCells, c ∈ body (p.relative q) := by
  unfold touch at htouch
  obtain ⟨F, hF, hFG⟩ := List.any_eq_true.mp htouch
  obtain ⟨G, hG, hop⟩ := List.any_eq_true.mp hFG
  obtain ⟨x, hx, axis, sgn, hdir, hout, rfl⟩ := mem_faces_iff.mp hF
  obtain ⟨y, hy, axis', sgn', hdir', hout', hGeq⟩ := mem_faces_iff.mp hG
  subst G
  obtain ⟨_, _, hyx⟩ := opposite_cell hdir hdir' hop
  obtain ⟨d, hd, hxd⟩ := body_mem_iff.mp hx
  obtain ⟨e, he, hye⟩ := (body_relative_mem hp hq).mp hy
  let n := unitAxis axis sgn
  have hn : n ∈ centralGridDirections := by
    unfold centralGridDirections
    exact List.mem_map.mpr ⟨(axis, sgn), hdir, rfl⟩
  have heq : cellLower p.frame p.shift e =
      (cellLower p.frame p.shift d).add n := by rw [← hye, ← hxd, hyx]
  have hout' : (cellLower p.frame p.shift d).add n ∉ body p := by
    rw [← hxd]
    exact hout
  exact ⟨e, external_neighbor_shell hp hd hn heq hout', he⟩

private def ComponentPoseAt (T : Tiling Q) (g h : RigidMotion) (p : Pose) : Prop :=
  h ∈ T.placements ∧ SameFeatureComponent T g h ∧
    p.frame ∈ allFrames ∧ RealizesPose (relativeMotion g h) p

private theorem sameFeatureComponent_left_mem {T : Tiling Q}
    {g h : RigidMotion} (hcomp : SameFeatureComponent T g h)
    (hh : h ∈ T.placements) : g ∈ T.placements := by
  apply Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => a ∈ T.placements) hcomp
  · exact hh
  · intro a c hac _ _
    exact hac.1

private theorem component_poses_compatible
    (T : Tiling Q) (hgrid : BaselineComponentCoversGrid Q)
    (hshell : CertifiedFirstShells T)
    {g h k : RigidMotion} {p q : Pose}
    (hp : ComponentPoseAt T g h p) (hq : ComponentPoseAt T g k q) :
    compatible legalContacts p q = true := by
  rcases hp with ⟨hh, hhcomp, hpf, hpreal⟩
  rcases hq with ⟨hk, hkcomp, hqf, hqreal⟩
  by_cases hpq : p = q
  · simp [compatible, hpq]
  have hhk : h ≠ k := by
    intro heq
    subst k
    exact hpq (realizesPose_pose_unique hpf hqf hpreal hqreal)
  have hoverlap : bodiesOverlap p q = false := by
    apply Bool.eq_false_iff.mpr
    intro hover
    unfold bodiesOverlap at hover
    obtain ⟨c, hcp, hcq⟩ := List.any_eq_true.mp hover
    have hcq' : c ∈ body q := List.contains_iff_mem.mp hcq
    obtain ⟨A, hAg, _, _, hdisjoint⟩ :=
      hgrid T g (sameFeatureComponent_left_mem hhcomp hh)
    exact hhk (component_cell_owner_unique hAg hh hk hhcomp hkcomp hdisjoint
      hpf hqf hpreal hqreal hcp hcq')
  by_cases htouch : touch p q = true
  · obtain ⟨c, hc, hcq⟩ := touch_relative_has_shell_cell hpf hqf htouch
    have hkcomp' : SameFeatureComponent T h k :=
      (sameFeatureComponent_symm hhcomp).trans hkcomp
    have hrreal : RealizesPose (relativeMotion h k) (p.relative q) := by
      have hr := realizesPose_relative hpreal hqreal hpf hqf
      have heq : relativeMotion (relativeMotion g h) (relativeMotion g k) =
          relativeMotion h k := by unfold relativeMotion; group
      rwa [heq] at hr
    have hkown : ComponentOwnsShellCell T h c k :=
      ⟨hk, hkcomp', p.relative q, allFrames_relative_mem hpf hqf, hrreal, hcq⟩
    obtain ⟨shell, _, _, hindexed, _⟩ := hshell h hh
    obtain ⟨i, _, hiowner⟩ := hindexed c hc k hkown
    have hipose : poseAt i ∈ legalContacts := by
      have hi' : i < legalContacts.length := List.mem_range.mp hiowner.2.1
      simp [poseAt, getD, hi']
    have hpose : p.relative q = poseAt i :=
      realizesPose_pose_unique (allFrames_relative_mem hpf hqf)
        (legalContact_frame_mem hipose) hrreal hiowner.2.2.1
    unfold compatible
    simp [hpq, hoverlap, htouch]
    rw [hpose]
    exact hipose
  · unfold compatible
    simp [hpq, hoverlap, htouch]

private def shellRoleAt (sid : Nat) : Nat := getD computedRoles sid 99

private def shellCenterAt (sid : Nat) : Pose :=
  (getD children (shellRoleAt sid) rootPose).inverse.transform
    (getD children 7 rootPose)

private theorem shell_role_lt (sid : Nat) (hsid : sid < shellSolutions.length) :
    shellRoleAt sid < 8 := by
  have hcheck : (List.range shellSolutions.length).all fun sid =>
      shellRoleAt sid < 8 = true := by decide
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck sid (List.mem_range.mpr hsid))

private theorem center_in_noncentral_shell (sid : Nat)
    (hsid : sid < shellSolutions.length) (hncentral : shellRoleAt sid ≠ 7) :
    ∃ idx ∈ getD shellSolutions sid [], poseAt idx = shellCenterAt sid := by
  have hcheck : (List.range shellSolutions.length).all fun sid =>
      shellRoleAt sid == 7 ||
        (getD shellSolutions sid []).any fun idx =>
          poseAt idx == shellCenterAt sid := by decide
  have hs := List.all_eq_true.mp hcheck sid (List.mem_range.mpr hsid)
  simpa [hncentral] using hs

private theorem central_shell_unique (sid : Nat)
    (hsid : sid < shellSolutions.length) (hcentral : shellRoleAt sid = 7) :
    sid = 0 := by
  have hcheck : (List.range shellSolutions.length).all fun sid =>
      shellRoleAt sid == 7 → sid == 0 := by decide
  have hs := List.all_eq_true.mp hcheck sid (List.mem_range.mpr hsid)
  simpa [hcentral] using hs

private theorem expected_viable_zero {sid j : Nat}
    (hcase : (sid, centralViable sid (shellRoleAt sid)) ∈ expectedCentralCases)
    (hj : j ∈ centralViable sid (shellRoleAt sid)) : j = 0 := by
  have hcheck : expectedCentralCases.all (fun rec =>
      rec.2.all fun j => j == 0) = true := by decide
  have hr := List.all_eq_true.mp hcheck
    (sid, centralViable sid (shellRoleAt sid)) hcase
  simpa using (List.all_eq_true.mp hr j hj)

private theorem realizesPose_one_root : RealizesPose (1 : RigidMotion) rootPose := by
  constructor
  · intro x i
    change x i = frameActReal identityFrame x i
    exact (frameActReal_identity x i).symm
  · intro i
    change 0 = ((v 0 0 0).get i : ℝ)
    fin_cases i <;> simp [v, V3.get]

/-- Realized literal poses compose according to `Pose.transform`. -/
theorem realizesPose_transform {g h : RigidMotion} {p q : Pose}
    (hg : RealizesPose g p) (hh : RealizesPose h q)
    (hpf : p.frame ∈ allFrames) (hqf : q.frame ∈ allFrames) :
    RealizesPose (g * h) (p.transform q) := by
  constructor
  · intro x i
    change (g.linearIsometryEquiv (h.linearIsometryEquiv x)) i = _
    rw [hg.1, realizesPose_linear_vector hh]
    unfold Pose.transform
    exact (frameActReal_mul p.frame q.frame
      (fun j => perm_lt_three hpf j)
      (fun j => perm_lt_three hqf j) x i).symm
  · intro i
    have hmap := congrArg (fun y : E3 => y i) (g.map_vadd 0 (h 0))
    simp only [vadd_eq_add, add_zero] at hmap
    change (g (h 0)) i = _
    rw [hmap]
    change (g.linearIsometryEquiv (h 0)) i + (g 0) i = _
    rw [realizesPose_origin_vector hh, hg.1]
    have hscaled := congrArg (fun y : E3 => y i)
      (frameActReal_scaledV3_one p.frame
        (fun j => perm_lt_three hpf j) q.shift)
    simp only [frameActRealVector_apply] at hscaled
    rw [hscaled, hg.2]
    unfold Pose.transform
    simp only [scaledV3, div_one, po]
    change ((p.frame.act q.shift).get i : ℝ) + (p.shift.get i : ℝ) =
      ((p.shift.add (p.frame.act q.shift)).get i : ℝ)
    rcases i with ⟨i, hi⟩
    interval_cases i <;> simp [scaledV3, V3.add, V3.get, v] <;> ring

private theorem componentPose_root {T : Tiling Q} {g : RigidMotion}
    (hg : g ∈ T.placements) : ComponentPoseAt T g g rootPose := by
  refine ⟨hg, Relation.ReflTransGen.refl, ?_, ?_⟩
  · decide
  · have heq : relativeMotion g g = 1 := by unfold relativeMotion; group
    rw [heq]
    exact realizesPose_one_root

private theorem componentPose_transform {T : Tiling Q}
    {g h k : RigidMotion} {p q : Pose}
    (hp : ComponentPoseAt T g h p)
    (hk : k ∈ T.placements) (hhk : SameFeatureComponent T h k)
    (hqf : q.frame ∈ allFrames)
    (hqreal : RealizesPose (relativeMotion h k) q) :
    ComponentPoseAt T g k (p.transform q) := by
  rcases hp with ⟨hh, hgh, hpf, hpreal⟩
  refine ⟨hk, hgh.trans hhk, ?_, ?_⟩
  · have hcheck : allFrames.all (fun f => allFrames.all fun q =>
        allFrames.contains (f.mul q)) = true := by decide
    exact List.contains_iff_mem.mp
      (List.all_eq_true.mp (List.all_eq_true.mp hcheck p.frame hpf)
        q.frame hqf)
  · have hr := realizesPose_transform hpreal hqreal hpf hqf
    have heq : relativeMotion g h * relativeMotion h k =
        relativeMotion g k := by unfold relativeMotion; group
    rwa [heq] at hr

private theorem certified_shell_pose
    {T : Tiling Q} (hshell : CertifiedFirstShells T)
    {g : RigidMotion} (hg : g ∈ T.placements)
    {shell : List Nat}
    (hdata :
      (∀ c ∈ shellCells, ∃! h : RigidMotion,
        ComponentOwnsShellCell T g c h) ∧
      (∀ c ∈ shellCells, ∀ h : RigidMotion,
        ComponentOwnsShellCell T g c h →
          ∃ k ∈ shell, ShellCellOwner T g c h k) ∧
      ∀ k ∈ shell, ∃ c ∈ shellCells, ∃ h : RigidMotion,
        ShellCellOwner T g c h k)
    {i : Nat} (hi : i ∈ shell) :
    ∃ h : RigidMotion, ComponentPoseAt T g h (poseAt i) := by
  obtain ⟨c, hc, h, hiowner⟩ := hdata.2.2 i hi
  rcases hiowner with ⟨⟨hh, hhcomp, p, hpf, hpreal, _⟩,
    hirange, hireal, _⟩
  have hipose : poseAt i ∈ legalContacts := by
    have hi' : i < legalContacts.length := List.mem_range.mp hirange
    simp [poseAt, getD, hi']
  have hp : p = poseAt i := realizesPose_pose_unique hpf
    (legalContact_frame_mem hipose) hpreal hireal
  subst p
  exact ⟨h, hh, hhcomp, legalContact_frame_mem hipose, hireal⟩

private def centralExisting (sid : Nat) : List Pose :=
  rootPose :: shellPoseSet (getD shellSolutions sid [])

private theorem certified_existing_pose
    {T : Tiling Q} (hshell : CertifiedFirstShells T)
    {g : RigidMotion} (hg : g ∈ T.placements)
    {sid : Nat} {shell : List Nat}
    (hshellEq : shell = getD shellSolutions sid [])
    (hdata :
      (∀ c ∈ shellCells, ∃! h : RigidMotion,
        ComponentOwnsShellCell T g c h) ∧
      (∀ c ∈ shellCells, ∀ h : RigidMotion,
        ComponentOwnsShellCell T g c h →
          ∃ k ∈ shell, ShellCellOwner T g c h k) ∧
      ∀ k ∈ shell, ∃ c ∈ shellCells, ∃ h : RigidMotion,
        ShellCellOwner T g c h k)
    {p : Pose} (hp : p ∈ centralExisting sid) :
    ∃ h : RigidMotion, ComponentPoseAt T g h p := by
  simp only [centralExisting, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ⟨g, componentPose_root hg⟩
  · unfold shellPoseSet at hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    apply certified_shell_pose hshell hg (hdata := hdata)
    rwa [hshellEq]

private theorem central_required_in_center_shell
    {T : Tiling Q} (hshell : CertifiedFirstShells T)
    (hgrid : BaselineComponentCoversGrid Q)
    {g k : RigidMotion} {sid j : Nat} {center r : Pose}
    (hcenter : ComponentPoseAt T g k center)
    {shell : List Nat}
    (hrootData :
      (∀ c ∈ shellCells, ∃! h : RigidMotion,
        ComponentOwnsShellCell T g c h) ∧
      (∀ c ∈ shellCells, ∀ h : RigidMotion,
        ComponentOwnsShellCell T g c h →
          ∃ k ∈ shell, ShellCellOwner T g c h k) ∧
      ∀ k ∈ shell, ∃ c ∈ shellCells, ∃ h : RigidMotion,
        ShellCellOwner T g c h k)
    (hrootEq : shell = getD shellSolutions sid [])
    {centerShell : List Nat}
    (hcenterData :
      (∀ c ∈ shellCells, ∃! h : RigidMotion,
        ComponentOwnsShellCell T k c h) ∧
      (∀ c ∈ shellCells, ∀ h : RigidMotion,
        ComponentOwnsShellCell T k c h →
          ∃ k' ∈ centerShell, ShellCellOwner T k c h k') ∧
      ∀ k' ∈ centerShell, ∃ c ∈ shellCells, ∃ h : RigidMotion,
        ShellCellOwner T k c h k')
    (hcenterEq : centerShell = getD shellSolutions j [])
    (hr : r ∈ (centralExisting sid).filterMap fun p =>
      if p != center && touch center p then some (center.relative p) else none) :
    r ∈ shellPoseSet (getD shellSolutions j []) := by
  simp only [List.mem_filterMap] at hr
  obtain ⟨p, hp, hif⟩ := hr
  by_cases hne : p != center
  · by_cases ht : touch center p = true
    · simp [hne, ht] at hif
      subst r
      obtain ⟨u, hu⟩ := certified_existing_pose hshell
        (sameFeatureComponent_left_mem hcenter.2.1 hcenter.1)
        hrootEq hrootData hp
      have hku : SameFeatureComponent T k u :=
        (sameFeatureComponent_symm hcenter.2.1).trans hu.2.1
      have hrel : RealizesPose (relativeMotion k u) (center.relative p) := by
        have hr := realizesPose_relative hcenter.2.2.2 hu.2.2.2
          hcenter.2.2.1 hu.2.2.1
        have heq : relativeMotion (relativeMotion g k) (relativeMotion g u) =
            relativeMotion k u := by unfold relativeMotion; group
        rwa [heq] at hr
      obtain ⟨c, hc, hcbody⟩ := touch_relative_has_shell_cell
        hcenter.2.2.1 hu.2.2.1 ht
      have hown : ComponentOwnsShellCell T k c u :=
        ⟨hu.1, hku, center.relative p,
          allFrames_relative_mem hcenter.2.2.1 hu.2.2.1, hrel, hcbody⟩
      obtain ⟨idx, hidx, hiowner⟩ := hcenterData.2.1 c hc u hown
      have hipose : poseAt idx ∈ legalContacts := by
        have hi' : idx < legalContacts.length :=
          List.mem_range.mp hiowner.2.1
        simp [poseAt, getD, hi']
      have hpose : center.relative p = poseAt idx :=
        realizesPose_pose_unique
          (allFrames_relative_mem hcenter.2.2.1 hu.2.2.1)
          (legalContact_frame_mem hipose) hrel hiowner.2.2.1
      unfold shellPoseSet
      apply List.mem_map.mpr
      exact ⟨idx, by rwa [hcenterEq] at hidx, hpose.symm⟩
    · simp [hne, ht] at hif
  · simp [hne] at hif

private theorem certified_center_shell_viable
    {T : Tiling Q} (hshell : CertifiedFirstShells T)
    (hgrid : BaselineComponentCoversGrid Q)
    {g k : RigidMotion} {sid j : Nat}
    (hjsid : j < shellSolutions.length)
    {rootShell centerShell : List Nat}
    (hrootEq : rootShell = getD shellSolutions sid [])
    (hcenterEq : centerShell = getD shellSolutions j [])
    (hrootData :
      (∀ c ∈ shellCells, ∃! h : RigidMotion,
        ComponentOwnsShellCell T g c h) ∧
      (∀ c ∈ shellCells, ∀ h : RigidMotion,
        ComponentOwnsShellCell T g c h →
          ∃ i ∈ rootShell, ShellCellOwner T g c h i) ∧
      ∀ i ∈ rootShell, ∃ c ∈ shellCells, ∃ h : RigidMotion,
        ShellCellOwner T g c h i)
    (hcenterData :
      (∀ c ∈ shellCells, ∃! h : RigidMotion,
        ComponentOwnsShellCell T k c h) ∧
      (∀ c ∈ shellCells, ∀ h : RigidMotion,
        ComponentOwnsShellCell T k c h →
          ∃ i ∈ centerShell, ShellCellOwner T k c h i) ∧
      ∀ i ∈ centerShell, ∃ c ∈ shellCells, ∃ h : RigidMotion,
        ShellCellOwner T k c h i)
    (hcenter : ComponentPoseAt T g k (shellCenterAt sid)) :
    j ∈ centralViable sid (shellRoleAt sid) := by
  unfold centralViable
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr hjsid, ?_⟩
  simp only [Bool.and_eq_true]
  constructor
  · unfold subset
    apply List.all_eq_true.mpr
    intro r hr
    apply List.contains_iff_mem.mpr
    apply central_required_in_center_shell hshell hgrid hcenter
      hrootData hrootEq hcenterData hcenterEq
    simpa [centralExisting, shellCenterAt, shellRoleAt] using hr
  · apply List.all_eq_true.mpr
    intro worldPose hworld
    obtain ⟨neighborPose, hneighbor, rfl⟩ := List.mem_map.mp hworld
    unfold shellPoseSet at hneighbor
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hneighbor
    have hidxCenter : idx ∈ centerShell := by rwa [hcenterEq]
    obtain ⟨u, hu⟩ := certified_shell_pose hshell hcenter.1
      (hdata := hcenterData) hidxCenter
    have huk : SameFeatureComponent T k u := hu.2.1
    have huWorld : ComponentPoseAt T g u
        ((shellCenterAt sid).transform (poseAt idx)) :=
      componentPose_transform hcenter hu.1 huk hu.2.2.1 hu.2.2.2
    apply List.all_eq_true.mpr
    intro existingPose hexisting
    obtain ⟨w, hw⟩ := certified_existing_pose hshell
      (sameFeatureComponent_left_mem hcenter.2.1 hcenter.1)
      hrootEq hrootData hexisting
    exact component_poses_compatible T hgrid hshell huWorld hw

private theorem shellSolution_index {shell : List Nat}
    (hshell : shell ∈ shellSolutions) :
    ∃ sid, sid < shellSolutions.length ∧
      shell = getD shellSolutions sid [] := by
  obtain ⟨i, hi⟩ := List.get_of_mem hshell
  refine ⟨i.val, i.isLt, ?_⟩
  rw [show getD shellSolutions i.val [] = shellSolutions.get i by
    simp [getD, i.isLt, List.get_eq_getElem]]
  exact hi.symm

private theorem computedCentralCases_eq_expected
    (hcentral : centralCompletionCheck = true) :
    computedCentralCases = expectedCentralCases := by
  unfold centralCompletionCheck at hcentral
  simp only [Bool.and_eq_true] at hcentral
  have hbeq : (computedCentralCases == expectedCentralCases) = true :=
    hcentral.1.1.1.1.1.1
  simpa using hbeq

private theorem central_case_mem_computed (sid : Nat)
    (hsid : sid < shellSolutions.length)
    (hncentral : shellRoleAt sid ≠ 7) :
    (sid, centralViable sid (shellRoleAt sid)) ∈ computedCentralCases := by
  unfold computedCentralCases
  apply List.mem_filterMap.mpr
  refine ⟨sid, List.mem_range.mpr hsid, ?_⟩
  have hn : getD computedRoles sid 99 ≠ 7 := by
    simpa [shellRoleAt] using hncentral
  simp [hn, shellRoleAt]

private theorem central_shell_zero_of_viable
    (hcentral : centralCompletionCheck = true)
    {sid j : Nat} (hsid : sid < shellSolutions.length)
    (hncentral : shellRoleAt sid ≠ 7)
    (hj : j ∈ centralViable sid (shellRoleAt sid)) : j = 0 := by
  apply expected_viable_zero
  · rw [← computedCentralCases_eq_expected hcentral]
    exact central_case_mem_computed sid hsid hncentral
  · exact hj

private theorem realizesPose_translation (t : V3) :
    RealizesPose (translation (cellCorner t)) (po identityFrame t) := by
  constructor
  · intro x i
    change x i = frameActReal identityFrame x i
    exact (frameActReal_identity x i).symm
  · intro i
    simp [translation, cellCorner, po]

private theorem central_child_pose :
    literalChildPose centralChildIndex = po identityFrame (v 1 1 1) := by
  decide

private theorem noncentral_child_in_central_shell (i : Fin 8) :
    i = centralChildIndex ∨
      ∃ idx ∈ getD shellSolutions 0 [],
        poseAt idx = (literalChildPose centralChildIndex).relative
          (literalChildPose i) := by
  fin_cases i <;> decide

private theorem proposed_role_identity (sid : Nat)
    (hsid : sid < shellSolutions.length) :
    (literalChildPose centralChildIndex).transform
        ((shellCenterAt sid).relative rootPose) =
      getD children (shellRoleAt sid) rootPose := by
  have hcheck : (List.range shellSolutions.length).all fun sid =>
      (literalChildPose centralChildIndex).transform
          ((shellCenterAt sid).relative rootPose) ==
        getD children (shellRoleAt sid) rootPose := by decide
  have hs := List.all_eq_true.mp hcheck sid
  exact eq_of_beq (hs (List.mem_range.mpr hsid))

private theorem complete_parent_from_central_shell
    {T : Tiling Q} (hshell : CertifiedFirstShells T)
    {g k : RigidMotion} {sid : Nat}
    (hsid : sid < shellSolutions.length)
    (hg : g ∈ T.placements)
    (hcenter : ComponentPoseAt T g k (shellCenterAt sid))
    {centerShell : List Nat}
    (hcenterEq : centerShell = getD shellSolutions 0 [])
    (hcenterData :
      (∀ c ∈ shellCells, ∃! h : RigidMotion,
        ComponentOwnsShellCell T k c h) ∧
      (∀ c ∈ shellCells, ∀ h : RigidMotion,
        ComponentOwnsShellCell T k c h →
          ∃ i ∈ centerShell, ShellCellOwner T k c h i) ∧
      ∀ i ∈ centerShell, ∃ c ∈ shellCells, ∃ h : RigidMotion,
        ShellCellOwner T k c h i) :
    ∃ π : RigidMotion, CompleteParent T π ∧
      ChildOfParent π ⟨shellRoleAt sid, shell_role_lt sid hsid⟩ g := by
  let τ : RigidMotion := translation (cellCorner (v 1 1 1))
  let π : RigidMotion := k * τ⁻¹
  have hτ : RealizesPose τ (literalChildPose centralChildIndex) := by
    rw [central_child_pose]
    exact realizesPose_translation (v 1 1 1)
  have hcomplete : CompleteParent T π := by
    intro i
    rcases noncentral_child_in_central_shell i with hi | ⟨idx, hidx, hpose⟩
    · subst i
      refine ⟨k, hcenter.1, ?_⟩
      unfold ChildOfParent π
      have heq : π⁻¹ * k = τ := by dsimp [π]; group
      rwa [heq]
    · have hidx' : idx ∈ centerShell := by rwa [hcenterEq]
      obtain ⟨u, hu⟩ := certified_shell_pose hshell hcenter.1
        (hdata := hcenterData) hidx'
      refine ⟨u, hu.1, ?_⟩
      unfold ChildOfParent
      have hprod : RealizesPose (τ * relativeMotion k u)
          ((literalChildPose centralChildIndex).transform (poseAt idx)) :=
        realizesPose_transform hτ hu.2.2.2 (by decide) hu.2.2.1
      have heq : π⁻¹ * u = τ * relativeMotion k u := by
        dsimp [π]
        unfold relativeMotion
        group
      rw [heq]
      rw [hpose] at hprod
      rw [pose_transform_relative (literalChildPose centralChildIndex)
        (literalChildPose i) (by decide) (by
          exact childFrame_mem_allFrames (by
            have hi : i.val < children.length := by
              rw [show children.length = 8 by decide]
              exact i.isLt
            simp [literalChildPose, getD, hi]))] at hprod
      exact hprod
  refine ⟨π, hcomplete, ?_⟩
  unfold ChildOfParent
  have hkg : RealizesPose (relativeMotion k g)
      ((shellCenterAt sid).relative rootPose) := by
    have hr := realizesPose_relative hcenter.2.2.2
      (componentPose_root hg).2.2.2 hcenter.2.2.1 (by decide)
    have heq : relativeMotion (relativeMotion g k) (relativeMotion g g) =
        relativeMotion k g := by unfold relativeMotion; group
    rwa [heq] at hr
  have hprod := realizesPose_transform hτ hkg (by decide)
    (allFrames_relative_mem hcenter.2.2.1 (by decide))
  have heq : π⁻¹ * g = τ * relativeMotion k g := by
    dsimp [π]
    unfold relativeMotion
    group
  rw [heq]
  rw [proposed_role_identity sid hsid] at hprod
  exact hprod

/-- R§7 central completion: the proposed role of a certified first shell
determines an actual central placement; the 14/18 literal census forces that
placement's certified shell to be the unique central row, which supplies all
eight children. -/
theorem certified_shells_complete_parents
    (T : Tiling Q) (_hregistered : Registered T)
    (hshell : CertifiedFirstShells T)
    (hgrid : BaselineComponentCoversGrid Q)
    (_hchildren : childrenPartitionCheck = true)
    (hcentral : centralCompletionCheck = true) :
    EveryPlacementHasCompleteParent T := by
  intro g hg
  obtain ⟨rootShell, hrootMem, hrootUnique, hrootIndex, hrootOccurs⟩ :=
    hshell g hg
  have hrootData :
      (∀ c ∈ shellCells, ∃! h : RigidMotion,
        ComponentOwnsShellCell T g c h) ∧
      (∀ c ∈ shellCells, ∀ h : RigidMotion,
        ComponentOwnsShellCell T g c h →
          ∃ i ∈ rootShell, ShellCellOwner T g c h i) ∧
      ∀ i ∈ rootShell, ∃ c ∈ shellCells, ∃ h : RigidMotion,
        ShellCellOwner T g c h i :=
    ⟨hrootUnique, hrootIndex, hrootOccurs⟩
  obtain ⟨sid, hsid, hrootEq⟩ := shellSolution_index hrootMem
  by_cases hcentralRole : shellRoleAt sid = 7
  · have hsid0 := central_shell_unique sid hsid hcentralRole
    subst sid
    have hcenterEq : shellCenterAt 0 = rootPose := by decide
    have hcenter : ComponentPoseAt T g g (shellCenterAt 0) := by
      rw [hcenterEq]
      exact componentPose_root hg
    obtain ⟨π, hπ, hgrole⟩ := complete_parent_from_central_shell hshell
      (sid := 0) (by decide) hg hcenter hrootEq hrootData
    exact ⟨π, hπ, ⟨⟨shellRoleAt 0, shell_role_lt 0 (by decide)⟩, hgrole⟩⟩
  · obtain ⟨centerIdx, hcenterIdx, hcenterPose⟩ :=
      center_in_noncentral_shell sid hsid hcentralRole
    have hcenterIdx' : centerIdx ∈ rootShell := by rwa [hrootEq]
    obtain ⟨k, hk⟩ := certified_shell_pose hshell hg
      (hdata := hrootData) hcenterIdx'
    rw [hcenterPose] at hk
    obtain ⟨centerShell, hcenterMem, hcenterUnique, hcenterIndex,
      hcenterOccurs⟩ := hshell k hk.1
    have hcenterData :
        (∀ c ∈ shellCells, ∃! h : RigidMotion,
          ComponentOwnsShellCell T k c h) ∧
        (∀ c ∈ shellCells, ∀ h : RigidMotion,
          ComponentOwnsShellCell T k c h →
            ∃ i ∈ centerShell, ShellCellOwner T k c h i) ∧
        ∀ i ∈ centerShell, ∃ c ∈ shellCells, ∃ h : RigidMotion,
          ShellCellOwner T k c h i :=
      ⟨hcenterUnique, hcenterIndex, hcenterOccurs⟩
    obtain ⟨j, hjlen, hcenterEq⟩ := shellSolution_index hcenterMem
    have hjviable : j ∈ centralViable sid (shellRoleAt sid) :=
      certified_center_shell_viable hshell hgrid
        hjlen hrootEq hcenterEq hrootData hcenterData hk
    have hj0 : j = 0 :=
      central_shell_zero_of_viable hcentral hsid hcentralRole hjviable
    subst j
    obtain ⟨π, hπ, hgrole⟩ := complete_parent_from_central_shell hshell
      hsid hg hk hcenterEq hcenterData
    exact ⟨π, hπ,
      ⟨⟨shellRoleAt sid, shell_role_lt sid hsid⟩, hgrole⟩⟩

private theorem realizesPose_eighthGrid {m : RigidMotion} {p : Pose}
    (hpf : p.frame ∈ allFrames) (hreal : RealizesPose m p) :
    EighthGridMotion m := by
  refine ⟨p.frame, hpf, hreal.1, ?_⟩
  intro i
  refine ⟨8 * p.shift.get i, ?_⟩
  rw [hreal.2]
  push_cast
  ring

/-- Two actual tiles cannot own the same registered baseline unit cell.  This
version does not presuppose that they are already known to lie in one feature
component: retained-core overlap promotes the baseline overlap to a physical
`Q`-overlap, and the tiling's disjoint-interior law identifies the tiles. -/
private theorem placed_body_cell_unique
    (H : Hypotheses) (T : Tiling Q) {g h k : RigidMotion} {p q : Pose}
    (hh : h ∈ T.placements) (hk : k ∈ T.placements)
    (hpf : p.frame ∈ allFrames) (hqf : q.frame ∈ allFrames)
    (hpreal : RealizesPose (relativeMotion g h) p)
    (hqreal : RealizesPose (relativeMotion g k) q)
    {c : V3} (hcp : c ∈ body p) (hcq : c ∈ body q) : h = k := by
  by_contra hne
  have hpInterior : cellCenter c ∈ interior ((relativeMotion g h) '' P) :=
    body_cellCenter_mem_interior hpf hpreal hcp
  have hqInterior : cellCenter c ∈ interior ((relativeMotion g k) '' P) :=
    body_cellCenter_mem_interior hqf hqreal hcq
  have hphysical := retained_core_overlap_holds (tube_ball H) mates_census
    (relativeMotion g h) (relativeMotion g k)
    (by
      have hr : RealizesPose
          (relativeMotion (relativeMotion g h) (relativeMotion g k))
          (p.relative q) := realizesPose_relative hpreal hqreal hpf hqf
      exact realizesPose_eighthGrid (allFrames_relative_mem hpf hqf) hr)
    ⟨cellCenter c, hpInterior, hqInterior⟩
  obtain ⟨x, hxH, hxK⟩ := hphysical
  have himageH : g '' ((relativeMotion g h) '' Q) = h '' Q := by
    rw [← mul_image]
    congr 1
    unfold relativeMotion
    group
  have himageK : g '' ((relativeMotion g k) '' Q) = k '' Q := by
    rw [← mul_image]
    congr 1
    unfold relativeMotion
    group
  have hgxH : g x ∈ interior (h '' Q) := by
    rw [← himageH]
    change g.toHomeomorph x ∈
      interior (g.toHomeomorph '' ((relativeMotion g h) '' Q))
    rw [← g.toHomeomorph.image_interior]
    exact ⟨x, hxH, rfl⟩
  have hgxK : g x ∈ interior (k '' Q) := by
    rw [← himageK]
    change g.toHomeomorph x ∈
      interior (g.toHomeomorph '' ((relativeMotion g k) '' Q))
    rw [← g.toHomeomorph.image_interior]
    exact ⟨x, hxK, rfl⟩
  exact Set.disjoint_left.mp (T.disjoint_interiors hh hk hne) hgxH hgxK

private theorem shellCell_role {c : V3} (hc : c ∈ shellCells) :
    ∃ r : Role, featureFarCell (nativeFeatureData r) = c := by
  have hcontrols := registered_shell_cell_controls
  simp only [registeredShellCellControlsCheck, Bool.and_eq_true] at hcontrols
  have hset : setEq roleFarCells shellCells = true := hcontrols.1.1.1.1.2
  simp only [setEq, Bool.and_eq_true, subset] at hset
  have hcmem : c ∈ roleFarCells := by
    apply List.contains_iff_mem.mp
    exact List.all_eq_true.mp hset.2 c hc
  obtain ⟨rn, hrn, hfar⟩ := List.mem_map.mp hcmem
  have hrnlt : rn < 192 := List.mem_range.mp hrn
  exact ⟨⟨rn, hrnlt⟩, by
    simpa [roleFarCells, nativeFeatureData] using hfar⟩

/-- An actual registered neighbour which owns a root-shell cell has a legal
atlas pose. -/
private theorem shell_occupying_pose_legal
    (H : Hypotheses) (T : Tiling Q) {h k : RigidMotion} {p : Pose}
    (hh : h ∈ T.placements) (hk : k ∈ T.placements)
    (hpf : p.frame ∈ allFrames)
    (hreal : RealizesPose (relativeMotion h k) p)
    {c : V3} (hcShell : c ∈ shellCells) (hcBody : c ∈ body p) :
    p ∈ legalContacts := by
  obtain ⟨r, hfar⟩ := shellCell_role hcShell
  obtain ⟨ell, hell, _, s, hmate, pe, hpe, hpereal, hpeCell⟩ :=
    role_companion_owns_far_cell H T hh r
  rw [hfar] at hpeCell
  have hkell : k = ell := placed_body_cell_unique H T hk hell
    hpf (legalContact_frame_mem hpe) hreal hpereal hcBody hpeCell
  subst ell
  have hp : p = pe := realizesPose_pose_unique hpf
    (legalContact_frame_mem hpe) hreal hpereal
  rwa [hp]

/-- Any two actual placements represented in one registered coordinate system
satisfy the exact finite compatibility predicate. -/
private theorem placed_poses_compatible
    (H : Hypotheses) (T : Tiling Q) {g h k : RigidMotion} {p q : Pose}
    (hh : h ∈ T.placements) (hk : k ∈ T.placements)
    (hpf : p.frame ∈ allFrames) (hqf : q.frame ∈ allFrames)
    (hpreal : RealizesPose (relativeMotion g h) p)
    (hqreal : RealizesPose (relativeMotion g k) q) :
    compatible legalContacts p q = true := by
  by_cases hpq : p = q
  · simp [compatible, hpq]
  have hhk : h ≠ k := by
    intro heq
    subst k
    exact hpq (realizesPose_pose_unique hpf hqf hpreal hqreal)
  have hoverlap : bodiesOverlap p q = false := by
    apply Bool.eq_false_iff.mpr
    intro hover
    unfold bodiesOverlap at hover
    obtain ⟨c, hcp, hcq⟩ := List.any_eq_true.mp hover
    exact hhk (placed_body_cell_unique H T hh hk hpf hqf hpreal hqreal
      hcp (List.contains_iff_mem.mp hcq))
  by_cases htouch : touch p q = true
  · have hrelative : RealizesPose (relativeMotion h k) (p.relative q) := by
      have hr := realizesPose_relative hpreal hqreal hpf hqf
      have heq : relativeMotion (relativeMotion g h) (relativeMotion g k) =
          relativeMotion h k := by unfold relativeMotion; group
      rwa [heq] at hr
    obtain ⟨c, hcShell, hcBody⟩ :=
      touch_relative_has_shell_cell hpf hqf htouch
    have hlegal : p.relative q ∈ legalContacts :=
      shell_occupying_pose_legal H T hh hk
        (allFrames_relative_mem hpf hqf) hrelative hcShell hcBody
    unfold compatible
    simp [hpq, hoverlap, htouch, hlegal]
  · unfold compatible
    simp [hpq, hoverlap, htouch]

private theorem child_index_of_mem {c : Pose} (hc : c ∈ children) :
    ∃ i : Fin 8, literalChildPose i = c := by
  obtain ⟨j, hj⟩ := List.get_of_mem hc
  have hlen : children.length = 8 := by decide
  let i : Fin 8 := ⟨j.val, by simpa [hlen] using j.isLt⟩
  refine ⟨i, ?_⟩
  change getD children j.val rootPose = c
  rw [show getD children j.val rootPose = children.get j by
    simp [getD, j.isLt, List.get_eq_getElem]]
  exact hj

/-- Every fine cross-contact induced by two actual complete parent fibres is
    one of the 44 legal contacts.  This is the geometric-to-finite half of
    R§8's macro-atlas readout. -/
theorem actual_parent_crossContacts_legal
    (H : Hypotheses) (T : Tiling Q) (A : ParentPartition T)
    {π ρ : RigidMotion} (hπ : π ∈ A.parents) (hρ : ρ ∈ A.parents)
    (hπρ : π ≠ ρ) {m : Pose} (hmf : m.frame ∈ allFrames)
    (hm : RealizesPose (relativeMotion π ρ) m) :
    subset (crossContacts m) legalContacts = true := by
  unfold subset
  apply List.all_eq_true.mpr
  intro e he
  unfold crossContacts at he
  rw [List.mem_eraseDups] at he
  obtain ⟨a, ha, he⟩ := List.mem_flatMap.mp he
  obtain ⟨z, hz, hez⟩ := List.mem_filterMap.mp he
  by_cases htouch : touch a z = true
  · simp [htouch] at hez
    subst e
    unfold macroChildren at hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
    obtain ⟨i, hai⟩ := child_index_of_mem ha
    obtain ⟨j, hbj⟩ := child_index_of_mem hb
    obtain ⟨g, hg, hgchild⟩ := A.each_child π hπ i
    obtain ⟨h, hh, hhchild⟩ := A.each_child ρ hρ j
    have hgchildRole := hgchild
    have hhchildRole := hhchild
    change RealizesPose (relativeMotion π g) (literalChildPose i) at hgchild
    change RealizesPose (relativeMotion ρ h) (literalChildPose j) at hhchild
    rw [hai] at hgchild
    rw [hbj] at hhchild
    have hzframe : (m.transform b).frame ∈ allFrames :=
      allFrames_mul_mem hmf (childFrame_mem_allFrames hb)
    have hhFromPi :
        RealizesPose (relativeMotion π h) (m.transform b) := by
      have hprod := realizesPose_transform hm hhchild hmf
        (childFrame_mem_allFrames hb)
      have heq : relativeMotion π ρ * relativeMotion ρ h =
          relativeMotion π h := by
        unfold relativeMotion
        group
      rwa [heq] at hprod
    have hcompat := placed_poses_compatible H T hg hh
      (childFrame_mem_allFrames ha) hzframe hgchild hhFromPi
    have hgh : g ≠ h := by
      intro hsame
      subst h
      exact hπρ (A.disjoint hπ hρ hgchildRole hhchildRole).1
    have hposeNe : a ≠ m.transform b := by
      intro hsame
      have hrel : relativeMotion π g = relativeMotion π h :=
        realizesPose_unique hgchild (hsame ▸ hhFromPi)
      apply hgh
      calc
        g = π * relativeMotion π g := by unfold relativeMotion; group
        _ = π * relativeMotion π h := by rw [hrel]
        _ = h := by unfold relativeMotion; group
    unfold compatible at hcompat
    simp [hposeNe, htouch] at hcompat
    exact List.contains_iff_mem.mpr hcompat.2
  · simp [htouch] at hez

private def poseRightQuotient (q b : Pose) : Pose :=
  let g := q.frame.mul b.frame.transpose
  po g (q.shift.sub (g.act b.shift))

private theorem pose_transform_inverse_right (p : Pose)
    (hp : p.frame ∈ allFrames) : p.transform p.inverse = rootPose := by
  have hframe : p.frame.mul p.frame.transpose = identityFrame :=
    allFrames_mul_transpose p.frame hp
  rcases p with ⟨pf, pt⟩
  unfold Pose.inverse Pose.transform rootPose
  simp only [po] at hp hframe ⊢
  rw [hframe]
  congr 1
  have hs := shift_cancel pf hp pt (v 0 0 0)
  have hzero : pf.transpose.act (v 0 0 0) = v 0 0 0 := by
    have hget (i : Nat) : (v 0 0 0).get i = 0 := by
      rcases i with _ | i
      · rfl
      · rcases i with _ | i <;> rfl
    apply v3_eq
    · change pf.transpose.sign.x * (v 0 0 0).get pf.transpose.perm.x = 0
      rw [hget]
      ring
    · change pf.transpose.sign.y * (v 0 0 0).get pf.transpose.perm.y = 0
      rw [hget]
      ring
    · change pf.transpose.sign.z * (v 0 0 0).get pf.transpose.perm.z = 0
      rw [hget]
      ring
  rw [hzero] at hs
  simpa [V3.neg, V3.smul, V3.add, v] using hs

private theorem poseRightQuotient_eq {q b m : Pose}
    (hq : q.frame ∈ allFrames) (hb : b.frame ∈ allFrames)
    (hm : m.frame ∈ allFrames) (heq : q = m.transform b) :
    poseRightQuotient q b = m := by
  have hbinv : b.inverse.frame ∈ allFrames := allFrames_transpose_mem _ hb
  have hquot : poseRightQuotient q b = q.transform b.inverse := by
    rcases q with ⟨qf, qt⟩
    rcases b with ⟨bf, bt⟩
    unfold poseRightQuotient Pose.inverse Pose.transform
    simp only [po] at hq hb ⊢
    congr 1
    change qt.sub ((qf.mul bf.transpose).act bt) =
      qt.add (qf.act ((bf.transpose.act bt).smul (-1)))
    rw [frameAct_smul, ← frame_act_mul_int qf bf.transpose hq]
    rcases (qf.mul bf.transpose).act bt with ⟨x, y, z⟩
    rcases qt with ⟨qx, qy, qz⟩
    apply v3_eq <;>
      simp [V3.sub, V3.neg, V3.smul, V3.add, v] <;> ring
  rw [hquot, heq, pose_transform_assoc hm hb hbinv,
    pose_transform_inverse_right b hb, pose_transform_root m hm]

/-- A fine child contact supplies the explicit witness triple in the
    `8 × 44 × 8` macro-candidate enumeration.  This is a structural list
    membership theorem; it performs no census evaluation. -/
private theorem mem_computedMacroCandidates_of_cross
    {m e : Pose} (hmf : m.frame ∈ allFrames)
    (he : e ∈ crossContacts m) (helegal : e ∈ legalContacts)
    (hmroot : m ≠ rootPose) : m ∈ computedMacroCandidates := by
  unfold crossContacts at he
  rw [List.mem_eraseDups] at he
  obtain ⟨a, ha, he⟩ := List.mem_flatMap.mp he
  obtain ⟨z, hz, hez⟩ := List.mem_filterMap.mp he
  by_cases htouch : touch a z = true
  · simp [htouch] at hez
    subst e
    unfold macroChildren at hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
    have haf : a.frame ∈ allFrames := childFrame_mem_allFrames ha
    have hbf : b.frame ∈ allFrames := childFrame_mem_allFrames hb
    have hzf : (m.transform b).frame ∈ allFrames :=
      allFrames_mul_mem hmf hbf
    have hq : a.transform (a.relative (m.transform b)) = m.transform b :=
      pose_transform_relative a (m.transform b) haf hzf
    have hquot : poseRightQuotient
        (a.transform (a.relative (m.transform b))) b = m :=
      poseRightQuotient_eq
        (allFrames_mul_mem haf (allFrames_relative_mem haf hzf)) hbf hmf hq
    unfold computedMacroCandidates diff
    apply List.mem_filter.mpr
    refine ⟨List.mem_eraseDups.mpr ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨a, ha, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨a.relative (m.transform b), helegal, ?_⟩
      apply List.mem_map.mpr
      refine ⟨b, hb, ?_⟩
      simpa [poseRightQuotient] using hquot
    · simpa using hmroot
  · simp [htouch] at hez

private theorem mem_rootMacroBody_iff {x : V3} :
    x ∈ rootMacroBody ↔ x ∈ children.flatMap body := by
  simp [rootMacroBody, unions]

private theorem macroChildren_doubledPose (p : Pose) :
    macroChildren (doubledPose p) = refine p := by
  rfl

private theorem mem_macroBody_doubledPose_iff {p : Pose} {x : V3} :
    x ∈ macroBody (doubledPose p) ↔ x ∈ (refine p).flatMap body := by
  rw [macroBody, macroChildren_doubledPose]
  simp [unions]

/-- Structural membership in the first macro filter: transported exact child
    dissections of disjoint parent bodies have disjoint macro cell lists. -/
private theorem mem_macroNonoverlap
    (hchildren : childrenPartitionCheck = true) {p : Pose}
    (hpf : p.frame ∈ allFrames)
    (hcandidate : doubledPose p ∈ computedMacroCandidates)
    (hdisjoint : (body rootPose).Disjoint (body p)) :
    doubledPose p ∈ macroNonoverlap := by
  unfold macroNonoverlap
  apply List.mem_filter.mpr
  refine ⟨hcandidate, ?_⟩
  have hrefined :
      ((refine rootPose).flatMap body).Disjoint
        ((refine p).flatMap body) :=
    refine_cells_disjoint_of_body_disjoint hchildren (by decide) hpf hdisjoint
  have hchildrenEq : refine rootPose = children := by
    exact refine_root
  rw [List.isEmpty_iff]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  unfold inter at hx
  have hxroot : x ∈ rootMacroBody := (List.mem_filter.mp hx).1
  have hxmacro : x ∈ macroBody (doubledPose p) :=
    List.contains_iff_mem.mp (List.mem_filter.mp hx).2
  rw [mem_rootMacroBody_iff, ← hchildrenEq] at hxroot
  rw [mem_macroBody_doubledPose_iff] at hxmacro
  exact List.disjoint_left.mp hrefined hxroot hxmacro

/-- The second macro filter is likewise entered structurally once a child
    contact witnesses nonemptiness and all induced contacts are legal. -/
private theorem mem_computedMacroLegal
    {m e : Pose} (hnonoverlap : m ∈ macroNonoverlap)
    (he : e ∈ crossContacts m)
    (hcross : subset (crossContacts m) legalContacts = true) :
    m ∈ computedMacroLegal := by
  unfold computedMacroLegal
  apply List.mem_filter.mpr
  refine ⟨hnonoverlap, ?_⟩
  have hne : (crossContacts m).isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro hempty
    rw [List.isEmpty_iff] at hempty
    rw [hempty] at he
    simp at he
  simp [hne, hcross]

private def doubledBodyCells (p : Pose) : List V3 :=
  (body p).flatMap fun a => bits.map fun b => (a.smul 2).add b

private theorem doubledBodyCells_length {p : Pose}
    (hpf : p.frame ∈ allFrames) : (doubledBodyCells p).length = 56 := by
  have hlen (xs : List V3) :
      (xs.flatMap fun a => bits.map fun b => (a.smul 2).add b).length =
        8 * xs.length := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
        rw [List.flatMap_cons, List.length_append, ih, List.length_map]
        rw [show bits.length = 8 by decide]
        simp only [List.length_cons]
        omega
  unfold doubledBodyCells
  rw [hlen, body_length_seven_hierarchy hpf]

/-- Exact refinement fills all eight unit subcubes of every baseline cube,
    not merely a subset of those doubled blocks.  The reverse inclusion is
    obtained structurally from the transported partition, nodupness, and the
    common cardinality 56. -/
private theorem refined_cells_iff_doubledBodyCells
    (hchildren : childrenPartitionCheck = true) {p : Pose}
    (hpf : p.frame ∈ allFrames) {x : V3} :
    x ∈ (refine p).flatMap body ↔ x ∈ doubledBodyCells p := by
  have hsubset : (refine p).flatMap body ⊆ doubledBodyCells p := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      refined_cell_in_parent_block hchildren hpf hy
    unfold doubledBodyCells
    apply List.mem_flatMap.mpr
    exact ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩
  have hsubperm := List.subperm_of_subset
    (refine_cells_nodup hchildren p hpf) hsubset
  have hrefineLen : ((refine p).flatMap body).length = 56 := by
    rw [flatMap_body_length_seven]
    · rw [show (refine p).length = children.length by simp [refine]]
      rw [show children.length = 8 by decide]
    · intro q hq
      exact refine_frame_mem_allFrames hpf hq
  have hperm := hsubperm.perm_of_length_le (by
    rw [doubledBodyCells_length hpf, hrefineLen])
  exact hperm.mem_iff

private theorem face_refinement_bits {x : V3} {axis : Nat} {sgn : Int}
    (hdir : (axis, sgn) ∈ centralFaceDirections) :
    ∃ b ∈ bits, ∃ c ∈ bits,
      ((x.smul 2).add b).add (unitAxis axis sgn) =
        ((x.add (unitAxis axis sgn)).smul 2).add c := by
  simp [centralFaceDirections] at hdir
  rcases hdir with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases x with ⟨xx, xy, xz⟩
  · exact ⟨v 0 0 0, by decide, v 1 0 0, by decide, by
      simp [V3.smul, V3.add, unitAxis, v] <;> ring⟩
  · exact ⟨v 1 0 0, by decide, v 0 0 0, by decide, by
      simp [V3.smul, V3.add, unitAxis, v] <;> ring⟩
  · exact ⟨v 0 0 0, by decide, v 0 1 0, by decide, by
      simp [V3.smul, V3.add, unitAxis, v] <;> ring⟩
  · exact ⟨v 0 1 0, by decide, v 0 0 0, by decide, by
      simp [V3.smul, V3.add, unitAxis, v] <;> ring⟩
  · exact ⟨v 0 0 0, by decide, v 0 0 1, by decide, by
      simp [V3.smul, V3.add, unitAxis, v] <;> ring⟩
  · exact ⟨v 0 0 1, by decide, v 0 0 0, by decide, by
      simp [V3.smul, V3.add, unitAxis, v] <;> ring⟩

/-- Refining two lattice-face-adjacent chairs exposes at least one touching
    pair of literal children across that face. -/
private theorem coarse_touch_has_crossContact
    (hchildren : childrenPartitionCheck = true) {p : Pose}
    (hpf : p.frame ∈ allFrames) (htouch : touch rootPose p = true) :
    ∃ e, e ∈ crossContacts (doubledPose p) := by
  obtain ⟨x, hx, axis, sgn, hdir, hy, hyOut, hxOut⟩ :=
    touch_iff_cellFaceAdjacent.mp htouch
  obtain ⟨b, hb, c, hc, hbc⟩ := face_refinement_bits hdir
  let X := (x.smul 2).add b
  let Y := ((x.add (unitAxis axis sgn)).smul 2).add c
  have hXY : X.add (unitAxis axis sgn) = Y := hbc
  have hXref : X ∈ (refine rootPose).flatMap body := by
    apply (refined_cells_iff_doubledBodyCells hchildren (by decide)).mpr
    unfold doubledBodyCells
    apply List.mem_flatMap.mpr
    exact ⟨x, hx, List.mem_map.mpr ⟨b, hb, rfl⟩⟩
  have hYref : Y ∈ (refine p).flatMap body := by
    apply (refined_cells_iff_doubledBodyCells hchildren hpf).mpr
    unfold doubledBodyCells
    apply List.mem_flatMap.mpr
    exact ⟨x.add (unitAxis axis sgn), hy,
      List.mem_map.mpr ⟨c, hc, rfl⟩⟩
  obtain ⟨a, ha, hXa⟩ := List.mem_flatMap.mp hXref
  obtain ⟨z, hz, hYz⟩ := List.mem_flatMap.mp hYref
  have hnotYa : Y ∉ body a := by
    intro hYa
    have hYroot : Y ∈ (refine rootPose).flatMap body :=
      List.mem_flatMap.mpr ⟨a, ha, hYa⟩
    have hYblock :=
      (refined_cells_iff_doubledBodyCells hchildren (by decide)).mp hYroot
    unfold doubledBodyCells at hYblock
    obtain ⟨d, hd, hYbit⟩ := List.mem_flatMap.mp hYblock
    obtain ⟨c', hc', hYeq⟩ := List.mem_map.mp hYbit
    have hdEq : d = x.add (unitAxis axis sgn) :=
      two_block_base_unique hc' hc (hYeq.trans rfl)
    exact hyOut (hdEq ▸ hd)
  have hnotXz : X ∉ body z := by
    intro hXz
    have hXp : X ∈ (refine p).flatMap body :=
      List.mem_flatMap.mpr ⟨z, hz, hXz⟩
    have hXblock :=
      (refined_cells_iff_doubledBodyCells hchildren hpf).mp hXp
    unfold doubledBodyCells at hXblock
    obtain ⟨d, hd, hXbit⟩ := List.mem_flatMap.mp hXblock
    obtain ⟨b', hb', hXeq⟩ := List.mem_map.mp hXbit
    have hdEq : d = x := two_block_base_unique hb' hb (hXeq.trans rfl)
    exact hxOut (hdEq ▸ hd)
  have haz : touch a z = true := touch_iff_cellFaceAdjacent.mpr
    ⟨X, hXa, axis, sgn, hdir, hXY ▸ hYz, hXY ▸ hnotYa, hnotXz⟩
  have hchildrenEq : refine rootPose = children := refine_root
  rw [hchildrenEq] at ha
  have hzmacro : z ∈ macroChildren (doubledPose p) := by
    rw [macroChildren_doubledPose]
    exact hz
  refine ⟨a.relative z, ?_⟩
  unfold crossContacts
  rw [List.mem_eraseDups]
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨z, hzmacro, ?_⟩
  simp [haz]

private theorem halfPose_one : halfPose (1 : RigidMotion) = 1 := by
  apply AffineIsometryEquiv.ext
  intro x
  simp [halfPose, translation]
  change x = x
  rfl

private theorem halfPose_inverse (g : RigidMotion) :
    halfPose g⁻¹ = (halfPose g)⁻¹ := by
  calc
    halfPose g⁻¹ = 1 * halfPose g⁻¹ := by simp
    _ = ((halfPose g)⁻¹ * halfPose g) * halfPose g⁻¹ := by simp
    _ = (halfPose g)⁻¹ * (halfPose g * halfPose g⁻¹) := by group
    _ = (halfPose g)⁻¹ * halfPose (g * g⁻¹) := by rw [halfPose_mul]
    _ = (halfPose g)⁻¹ := by rw [mul_inv_cancel, halfPose_one]; simp

private theorem halfPose_relative (g h : RigidMotion) :
    relativeMotion (halfPose g) (halfPose h) = halfPose (relativeMotion g h) := by
  unfold relativeMotion
  rw [← halfPose_inverse, ← halfPose_mul]

private theorem halvePose_doubledPose (p : Pose) :
    halvePose (doubledPose p) = p := by
  rcases p with ⟨f, x, y, z⟩
  change po f (v ((2 * x) / 2) ((2 * y) / 2) ((2 * z) / 2)) =
    po f (v x y z)
  apply congrArg (po f)
  apply v3_eq <;> simp [v] <;> omega

private theorem baseline_relative_bodies_disjoint
    {A : Set RigidMotion} (B : RegisteredBaselineTiling A)
    {g h : RigidMotion} (hg : g ∈ A) (hh : h ∈ A) (hne : g ≠ h)
    {p : Pose} (hpf : p.frame ∈ allFrames)
    (hreal : RealizesPose (relativeMotion g h) p) :
    (body rootPose).Disjoint (body p) := by
  rw [List.disjoint_left]
  intro c hcroot hcp
  have hgT : g ∈ B.tiling.placements := by rwa [B.placements_eq]
  have hhT : h ∈ B.tiling.placements := by rwa [B.placements_eq]
  have hrootReal : RealizesPose (relativeMotion g g) rootPose := by
    have heq : relativeMotion g g = 1 := by unfold relativeMotion; group
    rw [heq]
    exact realizesPose_one_root
  have hcG : cellCenter c ∈ interior ((relativeMotion g g) '' P) :=
    body_cellCenter_mem_interior (by decide) hrootReal hcroot
  have hcH : cellCenter c ∈ interior ((relativeMotion g h) '' P) :=
    body_cellCenter_mem_interior hpf hreal hcp
  have himageG : g '' ((relativeMotion g g) '' P) = g '' P := by
    rw [← mul_image]
    congr 1
    unfold relativeMotion
    group
  have himageH : g '' ((relativeMotion g h) '' P) = h '' P := by
    rw [← mul_image]
    congr 1
    unfold relativeMotion
    group
  have hGc : g (cellCenter c) ∈ interior (g '' P) := by
    rw [← himageG]
    change g.toHomeomorph (cellCenter c) ∈
      interior (g.toHomeomorph '' ((relativeMotion g g) '' P))
    rw [← g.toHomeomorph.image_interior]
    exact ⟨cellCenter c, hcG, rfl⟩
  have hHc : g (cellCenter c) ∈ interior (h '' P) := by
    rw [← himageH]
    change g.toHomeomorph (cellCenter c) ∈
      interior (g.toHomeomorph '' ((relativeMotion g h) '' P))
    rw [← g.toHomeomorph.image_interior]
    exact ⟨cellCenter c, hcH, rfl⟩
  exact Set.disjoint_left.mp
    (B.tiling.disjoint_interiors hgT hhT hne) hGc hHc

private theorem completeFeatureMate_comm {g h : RigidMotion} {r s : Role}
    (hm : CompleteFeatureMate g r h s) : CompleteFeatureMate h s g r := by
  rcases hm with ⟨hg, hs, hc⟩
  exact ⟨hg.symm, hs.symm, by omega⟩

private theorem featureAdjacent_atlas
    (H : Hypotheses) (T : Tiling Q) {g h : RigidMotion}
    (ha : FeatureAdjacent T g h) : AtlasRelated g h := by
  rcases ha with ⟨hg, hh, hne, hm | hm⟩
  · exact registered_mates H T g h hg hh hne hm
  · obtain ⟨r, s, hrs⟩ := hm
    exact registered_mates H T g h hg hh hne
      ⟨s, r, completeFeatureMate_comm hrs⟩

private theorem literalChild_mem_early (i : Fin 8) :
    literalChildPose i ∈ children := by
  have hi : i.val < children.length := by
    rw [show children.length = 8 by decide]
    exact i.isLt
  simp [literalChildPose, getD, hi]

private theorem child_pose_mem_allFrames (i : Fin 8) :
    (literalChildPose i).frame ∈ allFrames :=
  childFrame_mem_allFrames (literalChild_mem_early i)

private theorem orientationGroup_mem_allFrames {f : Frame}
    (hf : f ∈ orientationGroup) : f ∈ allFrames := by
  have hall : orientationGroup.all (fun g => allFrames.contains g) = true := by
    decide
  exact List.contains_iff_mem.mp (List.all_eq_true.mp hall f hf)

private theorem orientationGroup_mul_mem {f g : Frame}
    (hf : f ∈ orientationGroup) (hg : g ∈ orientationGroup) :
    f.mul g ∈ orientationGroup := by
  have hall : orientationGroup.all (fun f => orientationGroup.all fun g =>
      orientationGroup.contains (f.mul g)) = true := by decide
  exact List.contains_iff_mem.mp
    (List.all_eq_true.mp (List.all_eq_true.mp hall f hf) g hg)

private theorem realizesPose_inverse {g : RigidMotion} {p : Pose}
    (hpf : p.frame ∈ allFrames) (hg : RealizesPose g p) :
    RealizesPose g⁻¹ p.inverse := by
  have hr := realizesPose_relative hg realizesPose_one_root hpf (by decide)
  have hm : relativeMotion g 1 = g⁻¹ := by
    unfold relativeMotion
    simp
  have hp : p.relative rootPose = p.inverse := by
    unfold Pose.relative
    rw [pose_transform_root p.inverse (allFrames_transpose_mem p.frame hpf)]
  rwa [hm, hp] at hr

private theorem relative_parent_pose
    {π ρ g h : RigidMotion} {i j : Fin 8} {e : Pose}
    (hgi : ChildOfParent π i g) (hhj : ChildOfParent ρ j h)
    (hef : e.frame ∈ allFrames)
    (he : RealizesPose (relativeMotion g h) e) :
    let m := ((literalChildPose i).transform e).transform
      (literalChildPose j).inverse
    m.frame ∈ allFrames ∧ RealizesPose (relativeMotion π ρ) m := by
  let ci := literalChildPose i
  let cj := literalChildPose j
  have hcif : ci.frame ∈ allFrames := child_pose_mem_allFrames i
  have hcjf : cj.frame ∈ allFrames := child_pose_mem_allFrames j
  have hleft : RealizesPose (relativeMotion π h) (ci.transform e) := by
    have ht := realizesPose_transform hgi he hcif hef
    have hm : π⁻¹ * g * relativeMotion g h =
        relativeMotion π h := by unfold relativeMotion; group
    rwa [hm] at ht
  have hrightInv : RealizesPose (relativeMotion ρ h)⁻¹ cj.inverse :=
    realizesPose_inverse hcjf hhj
  have htotal := realizesPose_transform hleft hrightInv
    (allFrames_mul_mem hcif hef) (allFrames_transpose_mem cj.frame hcjf)
  have hm : relativeMotion π h * (relativeMotion ρ h)⁻¹ =
      relativeMotion π ρ := by unfold relativeMotion; group
  exact ⟨allFrames_mul_mem (allFrames_mul_mem hcif hef)
      (allFrames_transpose_mem cj.frame hcjf), by rwa [hm] at htotal⟩

private theorem macro_pose_in_candidates
    {i j : Fin 8} {e m : Pose}
    (he : e ∈ legalContacts)
    (hmf : m.frame ∈ allFrames)
    (hm : m = ((literalChildPose i).transform e).transform
      (literalChildPose j).inverse)
    (hmroot : m ≠ rootPose) : m ∈ computedMacroCandidates := by
  have hcif := child_pose_mem_allFrames i
  have hcjf := child_pose_mem_allFrames j
  have hef := legalContact_frame_mem he
  have hminv : (literalChildPose j).inverse.frame ∈ allFrames :=
    allFrames_transpose_mem _ hcjf
  have hqf : ((literalChildPose i).transform e).frame ∈ allFrames :=
    allFrames_mul_mem hcif hef
  have hcompose :
      (((literalChildPose i).transform e).transform
          (literalChildPose j).inverse).transform (literalChildPose j) =
        (literalChildPose i).transform e := by
    rw [pose_transform_assoc hqf hminv hcjf,
      pose_inverse_transform_self (literalChildPose j) hcjf,
      pose_transform_root _ hqf]
  have hquot : poseRightQuotient
      ((literalChildPose i).transform e) (literalChildPose j) = m := by
    apply poseRightQuotient_eq hqf hcjf hmf
    rw [hm]
    exact hcompose.symm
  unfold computedMacroCandidates diff
  apply List.mem_filter.mpr
  refine ⟨List.mem_eraseDups.mpr ?_, by simpa using hmroot⟩
  apply List.mem_flatMap.mpr
  refine ⟨literalChildPose i, literalChild_mem_early i, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨e, he, ?_⟩
  apply List.mem_map.mpr
  refine ⟨literalChildPose j, literalChild_mem_early j, ?_⟩
  simpa [poseRightQuotient] using hquot

/-- Distinct actual parent fibres have disjoint literal macro-cell bodies in
    coordinates normalized at the first parent. -/
private theorem actual_parent_macroBodies_disjoint
    (H : Hypotheses) (T : Tiling Q) (A : ParentPartition T)
    {π ρ : RigidMotion} (hπ : π ∈ A.parents) (hρ : ρ ∈ A.parents)
    (hπρ : π ≠ ρ) {m : Pose} (hmf : m.frame ∈ allFrames)
    (hm : RealizesPose (relativeMotion π ρ) m) :
    rootMacroBody.Disjoint (macroBody m) := by
  rw [List.disjoint_left]
  intro c hcroot hcm
  rw [mem_rootMacroBody_iff] at hcroot
  obtain ⟨a, ha, hca⟩ := List.mem_flatMap.mp hcroot
  unfold macroBody unions at hcm
  rw [List.mem_eraseDups] at hcm
  obtain ⟨z, hz, hcz⟩ := List.mem_flatMap.mp hcm
  unfold macroChildren at hz
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
  obtain ⟨i, hai⟩ := child_index_of_mem ha
  obtain ⟨j, hbj⟩ := child_index_of_mem hb
  obtain ⟨g, hg, hgi⟩ := A.each_child π hπ i
  obtain ⟨h, hh, hhj⟩ := A.each_child ρ hρ j
  have hga : RealizesPose (relativeMotion π g) a := by rwa [← hai]
  have hhb : RealizesPose (relativeMotion ρ h) b := by rwa [← hbj]
  have hhπ : RealizesPose (relativeMotion π h) (m.transform b) := by
    have ht := realizesPose_transform hm hhb hmf
      (childFrame_mem_allFrames hb)
    have heq : relativeMotion π ρ * relativeMotion ρ h =
        relativeMotion π h := by unfold relativeMotion; group
    rwa [heq] at ht
  have hgh : g = h := placed_body_cell_unique H T hg hh
    (childFrame_mem_allFrames ha)
    (allFrames_mul_mem hmf (childFrame_mem_allFrames hb))
    hga hhπ hca hcz
  subst h
  exact hπρ (A.disjoint hπ hρ hgi hhj).1

/- One feature-graph edge between children of two distinct parents forces
    their relative macro pose into the admitted parent atlas, hence gives an
    even relative origin. -/
set_option maxRecDepth 100000 in
private theorem adjacent_child_parents_even
    (H : Hypotheses) (T : Tiling Q) (A : ParentPartition T)
    {π ρ g h : RigidMotion} {i j : Fin 8}
    (hπ : π ∈ A.parents) (hρ : ρ ∈ A.parents)
    (hgi : ChildOfParent π i g) (hhj : ChildOfParent ρ j h)
    (hadj : FeatureAdjacent T g h)
    (hatlas : parentAtlasCheck = true) :
    ∃ m : Pose, m.frame ∈ orientationGroup ∧
      RealizesPose (relativeMotion π ρ) m ∧ evenPose m = true := by
  by_cases hπρ : π = ρ
  · subst ρ
    refine ⟨rootPose, by decide, ?_, by decide⟩
    have heq : relativeMotion π π = 1 := by unfold relativeMotion; group
    rw [heq]
    exact realizesPose_one_root
  obtain ⟨e, helegal, hereal⟩ := featureAdjacent_atlas H T hadj
  let m := ((literalChildPose i).transform e).transform
    (literalChildPose j).inverse
  have hmdata := relative_parent_pose hgi hhj
    (legalContact_frame_mem helegal) hereal
  have hmf : m.frame ∈ allFrames := hmdata.1
  have hmreal : RealizesPose (relativeMotion π ρ) m := hmdata.2
  have hcandidate : m ∈ computedMacroCandidates :=
    macro_pose_in_candidates helegal hmf rfl (by
      intro hmroot
      have hone : relativeMotion π ρ = 1 := realizesPose_unique
        (hmroot ▸ hmreal) realizesPose_one_root
      apply hπρ
      calc π = π * 1 := by simp
        _ = π * relativeMotion π ρ := by rw [hone]
        _ = ρ := by unfold relativeMotion; group)
  have hmacroDisjoint : rootMacroBody.Disjoint (macroBody m) :=
    actual_parent_macroBodies_disjoint H T A hπ hρ hπρ hmf hmreal
  have hnonoverlap : m ∈ macroNonoverlap := by
    unfold macroNonoverlap
    apply List.mem_filter.mpr
    refine ⟨hcandidate, ?_⟩
    rw [List.isEmpty_iff]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro c hc
    exact List.disjoint_left.mp hmacroDisjoint
      (List.mem_filter.mp hc).1
      (List.contains_iff_mem.mp (List.mem_filter.mp hc).2)
  have hcross : subset (crossContacts m) legalContacts = true :=
    actual_parent_crossContacts_legal H T A hπ hρ hπρ hmf hmreal
  have hecross : e ∈ crossContacts m := by
    unfold crossContacts
    rw [List.mem_eraseDups]
    apply List.mem_flatMap.mpr
    refine ⟨literalChildPose i, literalChild_mem_early i, ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨m.transform (literalChildPose j), ?_, ?_⟩
    · unfold macroChildren
      exact List.mem_map.mpr ⟨literalChildPose j, literalChild_mem_early j, rfl⟩
    · have heq : m.transform (literalChildPose j) =
          (literalChildPose i).transform e := by
        dsimp only [m]
        rw [pose_transform_assoc
          (allFrames_mul_mem (child_pose_mem_allFrames i)
            (legalContact_frame_mem helegal))
          (allFrames_transpose_mem _ (child_pose_mem_allFrames j))
          (child_pose_mem_allFrames j),
          pose_inverse_transform_self _ (child_pose_mem_allFrames j),
          pose_transform_root _
            (allFrames_mul_mem (child_pose_mem_allFrames i)
              (legalContact_frame_mem helegal))]
      have htouchRoot : touch rootPose e = true := by
        have hall : legalContacts.all (fun p => touch rootPose p) = true := by
          decide
        exact List.all_eq_true.mp hall e helegal
      have hrelative : (literalChildPose i).relative
          ((literalChildPose i).transform e) = e := by
        apply pose_transform_left_cancel (child_pose_mem_allFrames i)
          (allFrames_relative_mem (child_pose_mem_allFrames i)
            (allFrames_mul_mem (child_pose_mem_allFrames i)
              (legalContact_frame_mem helegal)))
          (legalContact_frame_mem helegal)
        exact pose_transform_relative (literalChildPose i)
          ((literalChildPose i).transform e)
          (child_pose_mem_allFrames i)
          (allFrames_mul_mem (child_pose_mem_allFrames i)
            (legalContact_frame_mem helegal))
      have htouch : touch (literalChildPose i)
          ((literalChildPose i).transform e) = true := by
        rw [touch_relative_iff (child_pose_mem_allFrames i)
          (allFrames_mul_mem (child_pose_mem_allFrames i)
            (legalContact_frame_mem helegal))]
        rw [hrelative]
        exact htouchRoot
      simp [heq, htouch, hrelative]
  have hmlegal : m ∈ computedMacroLegal :=
    mem_computedMacroLegal hnonoverlap hecross hcross
  have hmorientation : m.frame ∈ orientationGroup := by
    have hset : setEq (computedMacroLegal.map halvePose) legalContacts = true := by
      unfold parentAtlasCheck at hatlas
      simp only [Bool.and_eq_true] at hatlas
      aesop
    have hmapped : halvePose m ∈ computedMacroLegal.map halvePose :=
      List.mem_map.mpr ⟨m, hmlegal, rfl⟩
    have hmlegalFine : halvePose m ∈ legalContacts := by
      simp only [setEq, Bool.and_eq_true] at hset
      exact mem_of_subset_true hset.1 hmapped
    have hall : legalContacts.all (fun p =>
        orientationGroup.contains p.frame) = true := by decide
    exact List.contains_iff_mem.mp
      (List.all_eq_true.mp hall (halvePose m) hmlegalFine)
  exact ⟨m, hmorientation, hmreal,
    computedMacroLegal_even hatlas hmlegal⟩

private def registeredLiteralPose {g : RigidMotion}
    (r : RegisteredPose g) : Pose :=
  po (getD orientationGroup r.frameIndex identityFrame) r.shift

private theorem registeredLiteralPose_frame {g : RigidMotion}
    (r : RegisteredPose g) : (registeredLiteralPose r).frame ∈ allFrames := by
  have hindex : r.frameIndex.val < orientationGroup.length := by
    rw [show orientationGroup.length = 24 by decide]
    exact r.frameIndex.isLt
  have horientation : (registeredLiteralPose r).frame ∈ orientationGroup := by
    change getD orientationGroup r.frameIndex.val identityFrame ∈
      orientationGroup
    rw [show getD orientationGroup r.frameIndex.val identityFrame =
        orientationGroup[r.frameIndex.val] by simp [getD, hindex]]
    exact List.getElem_mem hindex
  exact orientationGroup_mem_allFrames horientation

private theorem registeredLiteralPose_realizes {g : RigidMotion}
    (r : RegisteredPose g) : RealizesPose g (registeredLiteralPose r) := by
  exact ⟨r.linear_eq, r.origin_eq⟩

private theorem cellCenter_mem_unitCube_eq {a b : V3}
    (h : cellCenter a ∈ unitCube b) : a = b := by
  have h0 := h (0 : Fin 3)
  have h1 := h (1 : Fin 3)
  have h2 := h (2 : Fin 3)
  change (b.x : ℝ) ≤ (a.x : ℝ) + 1 / 2 ∧
      (a.x : ℝ) + 1 / 2 ≤ (b.x : ℝ) + 1 at h0
  change (b.y : ℝ) ≤ (a.y : ℝ) + 1 / 2 ∧
      (a.y : ℝ) + 1 / 2 ≤ (b.y : ℝ) + 1 at h1
  change (b.z : ℝ) ≤ (a.z : ℝ) + 1 / 2 ∧
      (a.z : ℝ) + 1 / 2 ≤ (b.z : ℝ) + 1 at h2
  have hx₁ : b.x < a.x + 1 := by
    exact_mod_cast (show (b.x : ℝ) < (a.x : ℝ) + 1 by linarith)
  have hx₂ : a.x < b.x + 1 := by
    exact_mod_cast (show (a.x : ℝ) < (b.x : ℝ) + 1 by linarith)
  have hy₁ : b.y < a.y + 1 := by
    exact_mod_cast (show (b.y : ℝ) < (a.y : ℝ) + 1 by linarith)
  have hy₂ : a.y < b.y + 1 := by
    exact_mod_cast (show (a.y : ℝ) < (b.y : ℝ) + 1 by linarith)
  have hz₁ : b.z < a.z + 1 := by
    exact_mod_cast (show (b.z : ℝ) < (a.z : ℝ) + 1 by linarith)
  have hz₂ : a.z < b.z + 1 := by
    exact_mod_cast (show (a.z : ℝ) < (b.z : ℝ) + 1 by linarith)
  apply v3_eq <;> omega

private theorem cellCenter_mem_cubesOf_iff {a : V3} {xs : List V3} :
    cellCenter a ∈ cubesOf xs ↔ a ∈ xs := by
  constructor
  · rintro ⟨b, hb, hcenter⟩
    rwa [cellCenter_mem_unitCube_eq hcenter]
  · intro ha
    exact ⟨a, ha, cellCenter_mem_interior_unitCube a |>
      interior_subset⟩

/-- Grid coverage by one feature component, together with global
    registration and retained-core overlap, implies that every placement is
    in that component. -/
private theorem all_placements_sameFeatureComponent
    (H : Hypotheses) (T : Tiling Q) (hregistered : Registered T)
    (hgrid : BaselineComponentCoversGrid Q)
    {g h : RigidMotion} (hg : g ∈ T.placements) (hh : h ∈ T.placements) :
    SameFeatureComponent T g h := by
  let R := Classical.choice hregistered
  let rg := R.pose g hg
  let rh := R.pose h hh
  let pg := registeredLiteralPose rg
  let ph := registeredLiteralPose rh
  have hpgf : pg.frame ∈ allFrames := registeredLiteralPose_frame rg
  have hphf : ph.frame ∈ allFrames := registeredLiteralPose_frame rh
  have hpgh : RealizesPose (relativeMotion g h) (pg.relative ph) := by
    have hr := realizesPose_relative
      (registeredLiteralPose_realizes rg)
      (registeredLiteralPose_realizes rh) hpgf hphf
    have heq : relativeMotion (R.ambient * g) (R.ambient * h) =
        relativeMotion g h := by unfold relativeMotion; group
    rwa [heq] at hr
  obtain ⟨c, hc⟩ := body_nonempty_hierarchy (pg.relative ph)
  obtain ⟨N, hNg, hcomponentRegistered, hcover, _⟩ := hgrid T g hg
  obtain ⟨k, hk, hkcomp, hkcenter⟩ := hcover (cellCenter c)
  let rk := Classical.choice (hcomponentRegistered k hk hkcomp)
  let pk := registeredLiteralPose rk
  have hpkf : pk.frame ∈ allFrames := registeredLiteralPose_frame rk
  have hNk : RealizesPose (N * k) pk := registeredLiteralPose_realizes rk
  have hNkeq : N * k = relativeMotion g k := by
    calc
      N * k = (N * g) * (g⁻¹ * k) := by group
      _ = relativeMotion g k := by rw [hNg]; simp [relativeMotion]
  have hpkreal : RealizesPose (relativeMotion g k) pk := by rwa [← hNkeq]
  have hkimage : (N * k) '' P = cubesOf (body pk) :=
    realizesPose_image_P hpkf hNk
  have hkc : c ∈ body pk := by
    apply cellCenter_mem_cubesOf_iff.mp
    rw [← hkimage]
    exact hkcenter
  have hhk : h = k := placed_body_cell_unique H T hh hk
    (allFrames_relative_mem hpgf hphf) hpkf hpgh hpkreal hc hkc
  rwa [hhk]

private def ParentEvenRelated (π ρ : RigidMotion) : Prop :=
  ∃ p : Pose, p.frame ∈ orientationGroup ∧
    RealizesPose (relativeMotion π ρ) p ∧ evenPose p = true

private theorem parentEvenRelated_refl (π : RigidMotion) :
    ParentEvenRelated π π := by
  refine ⟨rootPose, by decide, ?_, by decide⟩
  have heq : relativeMotion π π = 1 := by unfold relativeMotion; group
  rw [heq]
  exact realizesPose_one_root

private theorem parentEvenRelated_trans {π ρ σ : RigidMotion}
    (hπρ : ParentEvenRelated π ρ) (hρσ : ParentEvenRelated ρ σ) :
    ParentEvenRelated π σ := by
  obtain ⟨p, hpf, hpreal, hpeven⟩ := hπρ
  obtain ⟨q, hqf, hqreal, hqeven⟩ := hρσ
  have hpf' := orientationGroup_mem_allFrames hpf
  have hqf' := orientationGroup_mem_allFrames hqf
  refine ⟨p.transform q, orientationGroup_mul_mem hpf hqf, ?_,
    evenPose_transform hpf' hpeven hqeven⟩
  have ht := realizesPose_transform hpreal hqreal hpf' hqf'
  have heq : relativeMotion π ρ * relativeMotion ρ σ =
      relativeMotion π σ := by unfold relativeMotion; group
  rwa [heq] at ht

/-- The connected feature graph propagates the even macro phase from a
    parent of its first placement to a parent of its last placement. -/
private theorem component_parents_even
    (H : Hypotheses) (T : Tiling Q) (A : ParentPartition T)
    (hatlas : parentAtlasCheck = true)
    {g h π ρ : RigidMotion} {i j : Fin 8}
    (hπ : π ∈ A.parents) (hρ : ρ ∈ A.parents)
    (hgi : ChildOfParent π i g) (hhj : ChildOfParent ρ j h)
    (hcomp : SameFeatureComponent T g h) : ParentEvenRelated π ρ := by
  have general : ∀ {a b : RigidMotion}, SameFeatureComponent T a b →
      ∀ (σ τ : RigidMotion) (u v : Fin 8),
        σ ∈ A.parents → τ ∈ A.parents →
        ChildOfParent σ u a → ChildOfParent τ v b →
        ParentEvenRelated σ τ := by
    intro a b hab
    induction hab using Relation.ReflTransGen.trans_induction_on with
    | refl a =>
        intro σ τ u v hσ hτ hσu hτv
        obtain ⟨hστ, _⟩ := A.disjoint hσ hτ hσu hτv
        subst τ
        exact parentEvenRelated_refl σ
    | single hab =>
        intro σ τ u v hσ hτ hσu hτv
        exact adjacent_child_parents_even H T A hσ hτ hσu hτv hab hatlas
    | trans hab hbc ihab ihbc =>
        intro σ τ u v hσ hτ hσu hτv
        have ha : _ ∈ T.placements := (A.covers _).mpr ⟨σ, hσ, u, hσu⟩
        have hb : _ ∈ T.placements :=
          sameFeatureComponent_left_mem
            (sameFeatureComponent_symm hab) ha
        obtain ⟨μ, hμ, k, hμk⟩ := (A.covers _).mp hb
        exact parentEvenRelated_trans
          (ihab σ μ u k hσ hμ hσu hμk)
          (ihbc μ τ k v hμ hτ hμk hτv)
  exact general hcomp π ρ i j hπ hρ hgi hhj

/-- All actual parent poses lie in one common parity class.  Connectivity is
    supplied by the already constructed feature component: its registered
    baseline bodies cover the grid, so retained-core disjointness forces
    every placement, and hence one child of every parent, into it. -/
theorem parent_common_parity
    (H : Hypotheses) (T : Tiling Q) (hregistered : Registered T)
    (hgrid : BaselineComponentCoversGrid Q) (A : ParentPartition T)
    (hatlas : parentAtlasCheck = true) :
    ∀ ⦃π ρ : RigidMotion⦄, π ∈ A.parents → ρ ∈ A.parents →
      ParentEvenRelated π ρ := by
  intro π ρ hπ hρ
  obtain ⟨g, hg, hgi⟩ := A.each_child π hπ centralChildIndex
  obtain ⟨h, hh, hhj⟩ := A.each_child ρ hρ centralChildIndex
  have hcomp : SameFeatureComponent T g h :=
    all_placements_sameFeatureComponent H T hregistered hgrid hg hh
  exact component_parents_even H T A hatlas hπ hρ hgi hhj hcomp

private theorem doubledPose_halvePose_of_even {p : Pose}
    (hp : evenPose p = true) : doubledPose (halvePose p) = p := by
  simp only [evenPose, Bool.and_eq_true, beq_iff_eq] at hp
  rcases p with ⟨f, x, y, z⟩
  change ((x % 2 = 0 ∧ y % 2 = 0) ∧ z % 2 = 0) at hp
  change po f (v (2 * (x / 2)) (2 * (y / 2)) (2 * (z / 2))) =
    po f (v x y z)
  congr 1
  apply v3_eq <;> simp [v] <;> omega

private theorem two_smul_mem_parent_cube {x : E3} {a b : V3}
    (hb : b ∈ bits)
    (hx : (2 : ℝ) • x ∈ unitCube ((a.smul 2).add b)) :
    x ∈ unitCube a := by
  intro i
  have hi := hx i
  simp [bits] at hb
  rcases hb with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    fin_cases i <;>
    simp [unitCube, V3.smul, V3.add, V3.get, v, smul_eq_mul] at hi ⊢ <;>
    constructor <;> linarith

private theorem half_point_of_macro
    (hchildren : childrenPartitionCheck = true) {p : Pose}
    (hpf : p.frame ∈ allFrames) (heven : evenPose p = true) {x : E3}
    (hx : (2 : ℝ) • x ∈ cubesOf (macroBody p)) :
    x ∈ cubesOf (body (halvePose p)) := by
  obtain ⟨c, hc, hxc⟩ := hx
  have hpdouble : doubledPose (halvePose p) = p :=
    doubledPose_halvePose_of_even heven
  have hcmacro : c ∈ macroBody (doubledPose (halvePose p)) := by
    rwa [hpdouble]
  have hcrefine : c ∈ (refine (halvePose p)).flatMap body :=
    mem_macroBody_doubledPose_iff.mp hcmacro
  have hhf : (halvePose p).frame ∈ allFrames := by
    change p.frame ∈ allFrames
    exact hpf
  have hcblock : c ∈ doubledBodyCells (halvePose p) :=
    (refined_cells_iff_doubledBodyCells hchildren hhf).mp hcrefine
  unfold doubledBodyCells at hcblock
  obtain ⟨a, ha, hcbit⟩ := List.mem_flatMap.mp hcblock
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hcbit
  exact ⟨a, ha, two_smul_mem_parent_cube hb hxc⟩

/-- In coordinates of any actual parent, the undeformed baseline copies of
    all placements cover space.  This is the geometric form of the component
    grid cover needed by the coarsening packaging. -/
private theorem parent_relative_baseline_cover
    (H : Hypotheses) (T : Tiling Q) (hregistered : Registered T)
    (hgrid : BaselineComponentCoversGrid Q) (A : ParentPartition T)
    {π : RigidMotion} (hπ : π ∈ A.parents) (x : E3) :
    ∃ h ∈ T.placements, ∃ q : Pose, q.frame ∈ allFrames ∧
      RealizesPose (relativeMotion π h) q ∧ x ∈ cubesOf (body q) := by
  obtain ⟨g, hg, hchild⟩ := A.each_child π hπ centralChildIndex
  obtain ⟨N, hNg, hcomponentRegistered, hcover, _⟩ := hgrid T g hg
  let k := relativeMotion π g
  let y : E3 := k⁻¹ x
  obtain ⟨h, hh, hhcomp, hy⟩ := hcover y
  let rh := Classical.choice (hcomponentRegistered h hh hhcomp)
  let s := registeredLiteralPose rh
  have hsf : s.frame ∈ allFrames := registeredLiteralPose_frame rh
  have hsN : RealizesPose (N * h) s := registeredLiteralPose_realizes rh
  have hNrel : N * h = relativeMotion g h := by
    calc
      N * h = (N * g) * (g⁻¹ * h) := by group
      _ = relativeMotion g h := by rw [hNg]; simp [relativeMotion]
  have hsrel : RealizesPose (relativeMotion g h) s := by rwa [← hNrel]
  let c := literalChildPose centralChildIndex
  have hcf : c.frame ∈ allFrames := child_pose_mem_allFrames centralChildIndex
  have hqreal : RealizesPose (relativeMotion π h) (c.transform s) := by
    have ht := realizesPose_transform hchild hsrel hcf hsf
    change RealizesPose
      (relativeMotion π g * relativeMotion g h) (c.transform s) at ht
    have heq : relativeMotion π g * relativeMotion g h =
        relativeMotion π h := by unfold relativeMotion; group
    rwa [heq] at ht
  have hkx : k y = x := by
    dsimp [y]
    exact k.apply_symm_apply x
  have hy' : y ∈ (relativeMotion g h) '' P := by rwa [← hNrel]
  have hxrel : x ∈ (relativeMotion π h) '' P := by
    have himage : k '' ((relativeMotion g h) '' P) =
        (relativeMotion π h) '' P := by
      rw [← mul_image]
      have heq : k * relativeMotion g h = relativeMotion π h := by
        dsimp [k]
        unfold relativeMotion
        group
      rw [heq]
    rw [← himage]
    exact ⟨y, hy', hkx⟩
  refine ⟨h, hh, c.transform s, allFrames_mul_mem hcf hsf, hqreal, ?_⟩
  rw [← realizesPose_image_P (allFrames_mul_mem hcf hsf) hqreal]
  exact hxrel

private theorem parent_macro_cover
    (H : Hypotheses) (T : Tiling Q) (hregistered : Registered T)
    (hgrid : BaselineComponentCoversGrid Q) (A : ParentPartition T)
    (hparity : ∀ {π ρ : RigidMotion}, π ∈ A.parents → ρ ∈ A.parents →
      ParentEvenRelated π ρ)
    {π : RigidMotion} (hπ : π ∈ A.parents) (x : E3) :
    ∃ ρ ∈ A.parents, ∃ m : Pose, m.frame ∈ orientationGroup ∧
      RealizesPose (relativeMotion π ρ) m ∧ evenPose m = true ∧
      x ∈ cubesOf (macroBody m) := by
  obtain ⟨h, hh, q, hqf, hqreal, hxq⟩ :=
    parent_relative_baseline_cover H T hregistered hgrid A hπ x
  obtain ⟨ρ, hρ, i, hchild⟩ := (A.covers h).mp hh
  obtain ⟨m, hmf, hmreal, hmeven⟩ := hparity hπ hρ
  have hmf' : m.frame ∈ allFrames := orientationGroup_mem_allFrames hmf
  have hcif : (literalChildPose i).frame ∈ allFrames :=
    child_pose_mem_allFrames i
  have hmchild : RealizesPose (relativeMotion π h)
      (m.transform (literalChildPose i)) := by
    have ht := realizesPose_transform hmreal hchild hmf' hcif
    change RealizesPose
      (relativeMotion π ρ * relativeMotion ρ h)
        (m.transform (literalChildPose i)) at ht
    have heq : relativeMotion π ρ * relativeMotion ρ h =
        relativeMotion π h := by unfold relativeMotion; group
    rwa [heq] at ht
  have hqeq : q = m.transform (literalChildPose i) :=
    realizesPose_pose_unique hqf (allFrames_mul_mem hmf' hcif)
      hqreal hmchild
  obtain ⟨c, hcq, hxc⟩ := hxq
  refine ⟨ρ, hρ, m, hmf, hmreal, hmeven, c, ?_, hxc⟩
  rw [hqeq] at hcq
  unfold macroBody unions macroChildren
  rw [List.mem_eraseDups]
  apply List.mem_flatMap.mpr
  refine ⟨m.transform (literalChildPose i), ?_, hcq⟩
  apply List.mem_map.mpr
  exact ⟨literalChildPose i, literalChild_mem_early i, rfl⟩

private theorem double_cell_mem_macro
    (hchildren : childrenPartitionCheck = true) {p : Pose}
    (hpf : p.frame ∈ allFrames) (heven : evenPose p = true)
    {a : V3} (ha : a ∈ body (halvePose p)) :
    a.smul 2 ∈ macroBody p := by
  have hpdouble : doubledPose (halvePose p) = p :=
    doubledPose_halvePose_of_even heven
  rw [← hpdouble, mem_macroBody_doubledPose_iff]
  apply (refined_cells_iff_doubledBodyCells hchildren (by
    change p.frame ∈ allFrames
    exact hpf)).mpr
  unfold doubledBodyCells
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  apply List.mem_map.mpr
  refine ⟨v 0 0 0, by decide, ?_⟩
  rcases a with ⟨ax, ay, az⟩
  apply v3_eq <;> simp [V3.smul, V3.add, v]

private theorem halved_parent_body_cells_disjoint
    (H : Hypotheses) (T : Tiling Q) (A : ParentPartition T)
    (hchildren : childrenPartitionCheck = true)
    {π ρ : RigidMotion} (hπ : π ∈ A.parents) (hρ : ρ ∈ A.parents)
    (hπρ : π ≠ ρ) {m : Pose} (hmf : m.frame ∈ allFrames)
    (hmreal : RealizesPose (relativeMotion π ρ) m)
    (hmeven : evenPose m = true) :
    (body rootPose).Disjoint (body (halvePose m)) := by
  have hmacro := actual_parent_macroBodies_disjoint H T A hπ hρ hπρ hmf hmreal
  rw [List.disjoint_left]
  intro a haroot hahalf
  have haRootMacro : a.smul 2 ∈ rootMacroBody := by
    rw [mem_rootMacroBody_iff, ← refine_root]
    apply (refined_cells_iff_doubledBodyCells hchildren (by decide)).mpr
    unfold doubledBodyCells
    apply List.mem_flatMap.mpr
    refine ⟨a, ?_, ?_⟩
    · exact haroot
    · apply List.mem_map.mpr
      refine ⟨v 0 0 0, by decide, ?_⟩
      rcases a with ⟨ax, ay, az⟩
      apply v3_eq <;> simp [V3.smul, V3.add, v]
  have haMacro : a.smul 2 ∈ macroBody m :=
    double_cell_mem_macro hchildren hmf hmeven hahalf
  exact List.disjoint_left.mp hmacro haRootMacro haMacro

private theorem placed_P_disjoint_of_relative_cells
    {g h : RigidMotion} {p : Pose} (hpf : p.frame ∈ allFrames)
    (hreal : RealizesPose (relativeMotion g h) p)
    (hcells : (body rootPose).Disjoint (body p)) :
    Disjoint (interior (g '' P)) (interior (h '' P)) := by
  have hrootReal : RealizesPose (relativeMotion g g) rootPose := by
    have heq : relativeMotion g g = 1 := by unfold relativeMotion; group
    rw [heq]
    exact realizesPose_one_root
  have hrelativeDisjoint :
      Disjoint (interior ((relativeMotion g g) '' P))
        (interior ((relativeMotion g h) '' P)) := by
    rw [realizesPose_image_P (by decide) hrootReal,
      realizesPose_image_P hpf hreal]
    exact cubesOf_disjoint_interiors hcells
  have himageG : g '' ((relativeMotion g g) '' P) = g '' P := by
    rw [← mul_image]
    congr 1
    unfold relativeMotion
    group
  have himageH : g '' ((relativeMotion g h) '' P) = h '' P := by
    rw [← mul_image]
    congr 1
    unfold relativeMotion
    group
  rw [Set.disjoint_left]
  intro x hxg hxh
  let y : E3 := g⁻¹ x
  have hgy : g y = x := g.apply_symm_apply x
  have hyG : y ∈ interior ((relativeMotion g g) '' P) := by
    rw [← himageG] at hxg
    change x ∈ interior (g.toHomeomorph ''
      ((relativeMotion g g) '' P)) at hxg
    rw [← g.toHomeomorph.image_interior] at hxg
    obtain ⟨z, hz, hzx⟩ := hxg
    have hzy : z = y := g.injective (hzx.trans hgy.symm)
    rwa [hzy] at hz
  have hyH : y ∈ interior ((relativeMotion g h) '' P) := by
    rw [← himageH] at hxh
    change x ∈ interior (g.toHomeomorph ''
      ((relativeMotion g h) '' P)) at hxh
    rw [← g.toHomeomorph.image_interior] at hxh
    obtain ⟨z, hz, hzx⟩ := hxh
    have hzy : z = y := g.injective (hzx.trans hgy.symm)
    rwa [hzy] at hz
  exact Set.disjoint_left.mp hrelativeDisjoint hyG hyH

/-- R§8's baseline packaging theorem.  The actual parent fibres partition
    the component baseline tiling into exact 56-cell doubled chairs; common
    parity makes their halves registered in one parent-relative frame. -/
theorem halved_parent_baseline_tiling
    (H : Hypotheses) (hgrid : BaselineComponentCoversGrid Q)
    (T : Tiling Q) (hregistered : Registered T) (A : ParentPartition T)
    (hchildren : childrenPartitionCheck = true) :
    Nonempty (RegisteredBaselineTiling (halvedParentPoses A)) := by
  have hparity := parent_common_parity H T hregistered hgrid A
    parent_atlas_eq_fine
  obtain ⟨g₀, hg₀, _⟩ := T.covers (0 : E3)
  obtain ⟨π₀, hπ₀, i₀, hπ₀child⟩ := (A.covers g₀).mp hg₀
  let B : RigidMotion := (halfPose π₀)⁻¹
  let U : Tiling P := {
    placements := halvedParentPoses A
    disjoint_interiors := by
      intro g h hg hh hne
      obtain ⟨π, hπ, rfl⟩ := hg
      obtain ⟨ρ, hρ, rfl⟩ := hh
      have hπρ : π ≠ ρ := by
        intro heq
        subst ρ
        exact hne rfl
      obtain ⟨m, hmf, hmreal, hmeven⟩ := hparity hπ hρ
      have hmf' : m.frame ∈ allFrames := orientationGroup_mem_allFrames hmf
      have hmhalf : RealizesPose
          (relativeMotion (halfPose π) (halfPose ρ)) (halvePose m) := by
        have hh := halfPose_realizes_halvePose hmreal hmeven
        rw [halfPose_relative]
        exact hh
      exact placed_P_disjoint_of_relative_cells
        (by change m.frame ∈ allFrames; exact hmf') hmhalf
        (halved_parent_body_cells_disjoint H T A hchildren hπ hρ hπρ
          hmf' hmreal hmeven)
    covers := by
      intro x
      let y : E3 := (halfPose π₀)⁻¹ x
      obtain ⟨ρ, hρ, m, hmf, hmreal, hmeven, hz⟩ :=
        parent_macro_cover H T hregistered hgrid A
          (fun {π ρ} hπ hρ => @hparity π ρ hπ hρ) hπ₀
          ((2 : ℝ) • y)
      have hmf' : m.frame ∈ allFrames := orientationGroup_mem_allFrames hmf
      have hycells : y ∈ cubesOf (body (halvePose m)) :=
        half_point_of_macro hchildren hmf' hmeven hz
      have hmhalf : RealizesPose
          (relativeMotion (halfPose π₀) (halfPose ρ)) (halvePose m) := by
        have hh := halfPose_realizes_halvePose hmreal hmeven
        rw [halfPose_relative]
        exact hh
      have hyimage : y ∈
          (relativeMotion (halfPose π₀) (halfPose ρ)) '' P := by
        rw [realizesPose_image_P (by
          change m.frame ∈ allFrames
          exact hmf') hmhalf]
        exact hycells
      refine ⟨halfPose ρ, ⟨ρ, hρ, rfl⟩, ?_⟩
      have himage : halfPose π₀ ''
          ((relativeMotion (halfPose π₀) (halfPose ρ)) '' P) =
          halfPose ρ '' P := by
        rw [← mul_image]
        congr 1
        unfold relativeMotion
        group
      rw [← himage]
      refine ⟨y, hyimage, ?_⟩
      dsimp [y]
      exact (halfPose π₀).apply_symm_apply x
  }
  refine ⟨{
    tiling := U
    placements_eq := rfl
    registered := ?_
  }⟩
  refine ⟨{
    ambient := B
    pose := ?_
  }⟩
  intro g hg
  let π := Classical.choose hg
  have hπdata := Classical.choose_spec hg
  have hπ : π ∈ A.parents := hπdata.1
  have hgEq : halfPose π = g := hπdata.2
  let m := Classical.choose (hparity hπ₀ hπ)
  have hmdata := Classical.choose_spec (hparity hπ₀ hπ)
  have hmf : m.frame ∈ orientationGroup := hmdata.1
  have hmreal : RealizesPose (relativeMotion π₀ π) m := hmdata.2.1
  have hmeven : evenPose m = true := hmdata.2.2
  have hmhalf : RealizesPose (B * g) (halvePose m) := by
    have hh := halfPose_realizes_halvePose hmreal hmeven
    have heq : B * g =
        relativeMotion (halfPose π₀) (halfPose π) := by
      rw [← hgEq]
      rfl
    rw [heq, halfPose_relative]
    exact hh
  exact registeredPose_of_realizes (by
    change m.frame ∈ orientationGroup
    exact hmf) hmhalf

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- R§8's finite-to-geometric readout, proved from the actual parent fibres:
    a coarse face supplies a legal child cross-contact, which enters the
    candidate, nonoverlap, and all-cross-contacts-legal filters in order. -/
theorem parent_atlas_admissibility
    (H : Hypotheses) (T : Tiling Q) (A : ParentPartition T)
    (B : RegisteredBaselineTiling (halvedParentPoses A))
    (hatlas : parentAtlasCheck = true) :
    Nonempty (AtlasBaselineTiling (halvedParentPoses A)) := by
  refine ⟨{
    toRegisteredBaselineTiling := B
    atlas_faces := ?_
  }⟩
  intro g h hg hh hne hface
  obtain ⟨π, hπ, rfl⟩ := hg
  obtain ⟨ρ, hρ, rfl⟩ := hh
  obtain ⟨p, hpf, hreal, htouch⟩ := hface
  have hπρ : π ≠ ρ := by
    intro heq
    subst ρ
    exact hne rfl
  have hhalf := halfPose_relative π ρ
  rw [hhalf] at hreal
  have hmacroReal :
      RealizesPose (relativeMotion π ρ) (doubledPose p) :=
    halfPose_realizes_doubledPose hreal
  have hcross : subset (crossContacts (doubledPose p)) legalContacts = true :=
    actual_parent_crossContacts_legal H T A hπ hρ hπρ hpf hmacroReal
  obtain ⟨e, hecross⟩ :=
    coarse_touch_has_crossContact children_partition_2P hpf htouch
  have helegal : e ∈ legalContacts :=
    mem_of_subset_true hcross hecross
  have hmacroNe : doubledPose p ≠ rootPose := by
    intro heq
    have hpRoot : p = rootPose := by
      have := congrArg halvePose heq
      rw [halvePose_doubledPose] at this
      have hroot : halvePose rootPose = rootPose := by decide
      rwa [hroot] at this
    subst p
    have hfalse : touch rootPose rootPose = false := by decide
    have : False := by simpa [hfalse] using htouch
    exact this.elim
  have hcandidate : doubledPose p ∈ computedMacroCandidates :=
    mem_computedMacroCandidates_of_cross hpf hecross helegal hmacroNe
  have hbodyDisjoint : (body rootPose).Disjoint (body p) :=
    baseline_relative_bodies_disjoint B
      ⟨π, hπ, rfl⟩ ⟨ρ, hρ, rfl⟩ hne hpf
      (by simpa [halfPose_relative] using hreal)
  have hnonoverlap : doubledPose p ∈ macroNonoverlap :=
    mem_macroNonoverlap children_partition_2P hpf hcandidate hbodyDisjoint
  have hmacroLegal : doubledPose p ∈ computedMacroLegal :=
    mem_computedMacroLegal hnonoverlap hecross hcross
  have hmapped : p ∈ computedMacroLegal.map halvePose := by
    rw [← halvePose_doubledPose p]
    exact List.mem_map.mpr ⟨doubledPose p, hmacroLegal, rfl⟩
  have hset : setEq (computedMacroLegal.map halvePose) legalContacts = true := by
    unfold parentAtlasCheck at hatlas
    simp only [Bool.and_eq_true] at hatlas
    aesop
  have hpLegal : p ∈ legalContacts := by
    simp only [setEq, Bool.and_eq_true] at hset
    exact mem_of_subset_true hset.1 hmapped
  exact ⟨p, hpLegal, by simpa [halfPose_relative] using hreal⟩

private def candidateParent (i : Fin 8) : List Pose :=
  parentThroughRoot (literalChildPose i)

private theorem literalChild_mem (i : Fin 8) : literalChildPose i ∈ children := by
  have hi : i.val < children.length := by
    rw [show children.length = 8 by decide]
    exact i.isLt
  simp [literalChildPose, getD, hi]

private theorem candidateParent_pose_realized
    (T : Tiling Q) {π g : RigidMotion} {i : Fin 8}
    (hcomplete : CompleteParent T π) (hgi : ChildOfParent π i g)
    {p : Pose} (hp : p ∈ candidateParent i) :
    ∃ h ∈ T.placements,
      p.frame ∈ allFrames ∧ RealizesPose (relativeMotion g h) p := by
  unfold candidateParent parentThroughRoot at hp
  obtain ⟨a, ha, hpa⟩ := List.mem_map.mp hp
  obtain ⟨aidx, haidx⟩ := List.get_of_mem ha
  have halen : children.length = 8 := by decide
  let ai : Fin 8 := ⟨aidx.val, by simpa [halen] using aidx.isLt⟩
  have haliteral : literalChildPose ai = a := by
    change getD children aidx.val rootPose = a
    rw [show getD children aidx.val rootPose = children.get aidx by
      simp [getD, aidx.isLt, List.get_eq_getElem]]
    exact haidx
  obtain ⟨h, hh, hha⟩ := hcomplete ai
  have hreal := realizesPose_relative hgi hha
    (childFrame_mem_allFrames (literalChild_mem i))
    (childFrame_mem_allFrames (literalChild_mem ai))
  have hmotion : relativeMotion (π⁻¹ * g) (π⁻¹ * h) =
      relativeMotion g h := by unfold relativeMotion; group
  rw [hmotion] at hreal
  rw [haliteral] at hreal
  have hpose : (literalChildPose i).relative a = p := by
    simpa [Pose.relative] using hpa
  rw [hpose] at hreal
  have hpframe : p.frame ∈ allFrames := hpose ▸ allFrames_relative_mem
    (childFrame_mem_allFrames (literalChild_mem i))
    (childFrame_mem_allFrames ha)
  exact ⟨h, hh, hpframe, hreal⟩

private theorem unorderedPair_members {α : Type} {xs : List α} {a b : α}
    (h : (a, b) ∈ unorderedPairs xs) : a ∈ xs ∧ b ∈ xs := by
  induction xs with
  | nil => simp [unorderedPairs] at h
  | cons x xs ih =>
      simp only [unorderedPairs, List.mem_append, List.mem_map] at h
      rcases h with h | h
      · obtain ⟨y, hy, heq⟩ := h
        cases heq
        exact ⟨by simp, by simp [hy]⟩
      · obtain ⟨ha, hb⟩ := ih h
        exact ⟨by simp [ha], by simp [hb]⟩

private theorem all_computed_parent_pairs_conflict
    (hconflicts : parentConflictsCheck = true) :
    ∀ pair ∈ unorderedPairs computedParents,
      parentsConflict pair.1 pair.2 = true := by
  unfold parentConflictsCheck at hconflicts
  simp only [Bool.and_eq_true] at hconflicts
  have hpairsLen : (unorderedPairs computedParents).length = 28 := by
    simpa using hconflicts.1.2
  have hfilterLen :
      (unorderedPairs computedParents |>.filter fun pair =>
        parentsConflict pair.1 pair.2).length = 28 := by
    simpa [computedParentConflictCount] using hconflicts.2
  have hsameLen :
      (unorderedPairs computedParents |>.filter fun pair =>
        parentsConflict pair.1 pair.2).length =
        (unorderedPairs computedParents).length := by omega
  have heq := List.Sublist.eq_of_length List.filter_sublist hsameLen
  exact List.filter_eq_self.mp heq

set_option maxHeartbeats 2000000 in
private theorem candidate_parent_pair_mem (i j : Fin 8) (hij : i ≠ j) :
    (candidateParent i, candidateParent j) ∈ unorderedPairs computedParents ∨
      (candidateParent j, candidateParent i) ∈ unorderedPairs computedParents := by
  fin_cases i <;> fin_cases j <;> simp_all <;>
    decide

private theorem mem_union_iff {a b : List Pose} {p : Pose} :
    p ∈ union a b ↔ p ∈ a ∨ p ∈ b := by
  unfold union
  rw [List.mem_eraseDups, List.mem_append]

private theorem incompatible_witness {a b : List Pose}
    (hconflict : parentsConflict a b = true) :
    ∃ p q, p ∈ union a b ∧ q ∈ union a b ∧
      compatible legalContacts p q = false := by
  unfold parentsConflict at hconflict
  obtain ⟨pair, hpair, hbad⟩ := List.any_eq_true.mp hconflict
  rcases pair with ⟨p, q⟩
  have hpq := unorderedPair_members hpair
  refine ⟨p, q, hpq.1, hpq.2, ?_⟩
  simpa using hbad

private theorem candidate_pose_pair_compatible
    (H : Hypotheses) (T : Tiling Q)
    {π ρ g : RigidMotion} {i j : Fin 8}
    (hπ : CompleteParent T π) (hρ : CompleteParent T ρ)
    (hπi : ChildOfParent π i g) (hρj : ChildOfParent ρ j g)
    {p q : Pose}
    (hp : p ∈ union (candidateParent i) (candidateParent j))
    (hq : q ∈ union (candidateParent i) (candidateParent j)) :
    compatible legalContacts p q = true := by
  rw [mem_union_iff] at hp hq
  rcases hp with hpi | hpj <;> rcases hq with hqi | hqj
  · obtain ⟨u, hu, hpf, hureal⟩ :=
      candidateParent_pose_realized T hπ hπi hpi
    obtain ⟨w, hw, hqf, hwreal⟩ :=
      candidateParent_pose_realized T hπ hπi hqi
    exact placed_poses_compatible H T hu hw hpf hqf hureal hwreal
  · obtain ⟨u, hu, hpf, hureal⟩ :=
      candidateParent_pose_realized T hπ hπi hpi
    obtain ⟨w, hw, hqf, hwreal⟩ :=
      candidateParent_pose_realized T hρ hρj hqj
    exact placed_poses_compatible H T hu hw hpf hqf hureal hwreal
  · obtain ⟨u, hu, hpf, hureal⟩ :=
      candidateParent_pose_realized T hρ hρj hpj
    obtain ⟨w, hw, hqf, hwreal⟩ :=
      candidateParent_pose_realized T hπ hπi hqi
    exact placed_poses_compatible H T hu hw hpf hqf hureal hwreal
  · obtain ⟨u, hu, hpf, hureal⟩ :=
      candidateParent_pose_realized T hρ hρj hpj
    obtain ⟨w, hw, hqf, hwreal⟩ :=
      candidateParent_pose_realized T hρ hρj hqj
    exact placed_poses_compatible H T hu hw hpf hqf hureal hwreal

set_option maxHeartbeats 2000000 in
/-- R§7 conflict readout: two complete literal parents containing the same
placement have the same canonical role and the same parent pose. -/
theorem complete_parent_conflicts
    (H : Hypotheses) (T : Tiling Q) (_hregistered : Registered T)
    (_hexists : EveryPlacementHasCompleteParent T)
    (_hchildren : childrenPartitionCheck = true)
    (hconflicts : parentConflictsCheck = true) :
    CompleteParentsDisjoint T := by
  intro π ρ g i j hπ hρ hπi hρj
  have hij : i = j := by
    by_contra hne
    obtain hpairs | hpairs := candidate_parent_pair_mem i j hne
    · have hconflict := all_computed_parent_pairs_conflict hconflicts
        (candidateParent i, candidateParent j) hpairs
      obtain ⟨p, q, hp, hq, hbad⟩ := incompatible_witness hconflict
      rw [candidate_pose_pair_compatible H T hπ hρ hπi hρj hp hq] at hbad
      contradiction
    · have hconflict := all_computed_parent_pairs_conflict hconflicts
        (candidateParent j, candidateParent i) hpairs
      obtain ⟨p, q, hp, hq, hbad⟩ := incompatible_witness hconflict
      rw [candidate_pose_pair_compatible H T hρ hπ hρj hπi hp hq] at hbad
      contradiction
  subst j
  have hrel : π⁻¹ * g = ρ⁻¹ * g := realizesPose_unique hπi hρj
  have hinv : π⁻¹ = ρ⁻¹ := calc
    π⁻¹ = (π⁻¹ * g) * g⁻¹ := by group
    _ = (ρ⁻¹ * g) * g⁻¹ := by rw [hrel]
    _ = ρ⁻¹ := by group
  have hπρ : π = ρ := by
    simpa using congrArg Inv.inv hinv
  exact ⟨hπρ, rfl⟩

/-- Theorem 6.3: the alignment chain sends every arbitrary congruent tiling to
    the registered integer/proper-cubic interface. -/
theorem registration_of_tiling (H : Hypotheses) (T : Tiling Q) : Registered T := by
  apply unrestricted_alignment_holds orientation_group_24
  apply component_solids_cover_holds (tube_ball H)
  apply baseline_component_covers_grid_holds (registered_mates H) atlas_44

/-- Theorem 7.1's logical assembly.  The remaining fields now stop at its
    three substantive geometric/certificate bridges; construction and
    uniqueness of the parent-pose set are proved by
    `hasUniqueParent_of_completeParents`. -/
theorem parent_local_to_global (H : Hypotheses) (T : Tiling Q)
    (hregistered : Registered T) (hchildren : childrenPartitionCheck = true)
    (hshells : firstShellsCheck = true)
    (hcentral : centralCompletionCheck = true)
    (hconflicts : parentConflictsCheck = true) : HasUniqueParent T := by
  have hmates : OnlyRegisteredMates Q := registered_mates H
  have hgrid : BaselineComponentCoversGrid Q :=
    baseline_component_covers_grid_holds hmates atlas_44
  have hshell : CertifiedFirstShells T :=
    registered_first_shells H T hregistered hshells
  have hcomplete : EveryPlacementHasCompleteParent T :=
    certified_shells_complete_parents T hregistered hshell hgrid
      hchildren hcentral
  exact hasUniqueParent_of_completeParents T hcomplete
    (complete_parent_conflicts H T hregistered hcomplete hchildren hconflicts)

/-- Theorem 7.1: every registered tiling has its unique intrinsic eight-copy
    parent partition. -/
theorem unique_parent (H : Hypotheses) (T : Tiling Q) : HasUniqueParent T :=
  parent_local_to_global H T (registration_of_tiling H T)
    children_partition_2P first_shells_33 central_completion parent_conflicts_28

/-- The unique geometric parent partition selected without any phase or role
    choice.  Subsingletonness makes all uses independent of this `choice`. -/
noncomputable def uniqueParentPartition (H : Hypotheses) (T : Tiling Q) :
    ParentPartition T :=
  Classical.choice (unique_parent H T).1

theorem uniqueParentPartition_translate (H : Hypotheses) (v : E3)
    (T : Tiling Q) :
    uniqueParentPartition H (translateTiling v T) =
      translateParentPartition v (uniqueParentPartition H T) :=
  (unique_parent H (translateTiling v T)).2.elim _ _

/-- A coarsening is simply an endomap of the tiling space.  The particular
    map below is derived from the unique parent poses; it carries no assumed
    covariance field. -/
abbrev Coarsening (S : Set E3) := Tiling S → Tiling S

/-- R§8 reconstructed from its three exact stages: baseline macro-chair
    partition, parent-atlas admissibility, and the shared small-collar
    realization. -/
theorem coarsening_realization (H : Hypotheses) (T : Tiling Q)
    (hregistered : Registered T) (A : ParentPartition T)
    (hchildren : childrenPartitionCheck = true)
    (hatlas : parentAtlasCheck = true) :
    ∃ D : Tiling Q, D.placements = halvedParentPoses A := by
  let B := Classical.choice
    (halved_parent_baseline_tiling H
      (baseline_component_covers_grid_holds (registered_mates H) atlas_44)
      T hregistered A hchildren)
  let C := Classical.choice (parent_atlas_admissibility H T A B hatlas)
  exact small_collar_realization_holds (tube_homeomorphism H) (halvedParentPoses A)
    C

/-- Theorem 8.1's remaining realization step for a specified geometric
    parent partition. -/
theorem coarsening_is_tiling (H : Hypotheses) (T : Tiling Q)
    (A : ParentPartition T) :
    ∃ D : Tiling Q, D.placements = halvedParentPoses A :=
  coarsening_realization H T (registration_of_tiling H T) A
    children_partition_2P parent_atlas_eq_fine

/-- `D(T)`: divide the unique parent origins by two and restandardize each
    macro-body as a fresh native copy of the concrete `Q`. -/
noncomputable def coarsening (H : Hypotheses) : Coarsening Q :=
  fun T => Classical.choose
    (coarsening_is_tiling H T (uniqueParentPartition H T))

theorem coarsening_placements (H : Hypotheses) (T : Tiling Q) :
    (coarsening H T).placements =
      halvedParentPoses (uniqueParentPartition H T) :=
  Classical.choose_spec
    (coarsening_is_tiling H T (uniqueParentPartition H T))

/-- The derived coarsening is translation-equivariant with scale one half. -/
theorem coarsening_translation_equivariant (H : Hypotheses) (T : Tiling Q)
    (v : E3) :
    coarsening H (translateTiling v T) =
      translateTiling ((2 : ℝ)⁻¹ • v) (coarsening H T) := by
  apply Tiling.ext
  rw [coarsening_placements]
  change halvedParentPoses (uniqueParentPartition H (translateTiling v T)) =
    translation ((2 : ℝ)⁻¹ • v) • (coarsening H T).placements
  rw [uniqueParentPartition_translate, coarsening_placements,
    halvedParentPoses_translate]

private theorem tileFamily_translate {S : Set E3} (T : Tiling S) (v : E3) :
    tileFamily (translateTiling v T) = translation v • tileFamily T := by
  ext A
  constructor
  · rintro ⟨g, hg, rfl⟩
    change g ∈ translation v • T.placements at hg
    rw [Set.mem_smul_set] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    exact Set.mem_smul_set.mpr
      ⟨h '' S, ⟨h, hh, rfl⟩, rigid_smul_image S (translation v) h⟩
  · intro hA
    rw [Set.mem_smul_set] at hA
    obtain ⟨B, ⟨h, hh, rfl⟩, rfl⟩ := hA
    refine ⟨translation v * h,
      Set.mem_smul_set.mpr ⟨h, hh, rfl⟩, ?_⟩
    exact rigid_smul_image S (translation v) h

private theorem translated_eq_of_period (H : Hypotheses) (T : Tiling Q)
    {p : E3} (hp : p ∈ Per T) : translateTiling p T = T := by
  apply Tiling.ext
  ext g
  constructor
  · intro hg
    change g ∈ translation p • T.placements at hg
    rw [Set.mem_smul_set] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    exact symmetry_sends_placement T
      (native_asymmetry_reduction (native_asymmetry_planar_reduction H) no_native_symmetry)
      ⟨translation p, hp⟩ h hh
  · intro hg
    change g ∈ translation p • T.placements
    have hinv : (translation p)⁻¹ ∈ Sym T := (Sym T).inv_mem hp
    have hpre : (translation p)⁻¹ * g ∈ T.placements :=
      symmetry_sends_placement T
        (native_asymmetry_reduction (native_asymmetry_planar_reduction H) no_native_symmetry)
        ⟨(translation p)⁻¹, hinv⟩ g hg
    refine Set.mem_smul_set.mpr ⟨(translation p)⁻¹ * g, hpre, ?_⟩
    change translation p * ((translation p)⁻¹ * g) = g
    group

private theorem period_of_translated_eq (T : Tiling Q) (v : E3)
    (h : translateTiling v T = T) : v ∈ Per T := by
  change translation v • tileFamily T = tileFamily T
  rw [← tileFamily_translate T v, h]

/-- Translation covariance of the derived `D` halves every translation
    period; no period implication is assumed in `Hypotheses`. -/
theorem period_halving (H : Hypotheses) (T : Tiling Q) {p : E3}
    (hp : p ∈ Per T) : (2 : ℝ)⁻¹ • p ∈ Per (coarsening H T) := by
  apply period_of_translated_eq
  have heq := coarsening_translation_equivariant H T p
  rw [translated_eq_of_period H T hp] at heq
  exact heq.symm

def coarseningIterate (H : Hypotheses) : Nat → Tiling Q → Tiling Q
  | 0, T => T
  | n + 1, T => coarsening H (coarseningIterate H n T)

/-! ## Canonical and geometric carrier hierarchies

Ruling R7 isolates the hierarchy which is valid for every tiling from the
stronger, false assertion that the ancestors of one fixed cell exhaust space.
At level `n` a supertile is represented by the normalized chair placement in
`D^n(T)`; multiplying its geometric support by `2^n` returns the corresponding
supertile in the coordinates of `T`.  This is the registered-pose version of
the three-dimensional chair inflation described by Lee--Moody: one doubled
chair is the union of the eight child poses checked by
`children_partition_2P`.
-/

/-- A registered carrier cell is a placed copy of `Q`, regarded only through
its chair carrier in the same rigid pose. -/
abbrev CarrierCell (T : Tiling Q) := {g : RigidMotion // g ∈ T.placements}

/-- A level-`n` supertile pose is an actual normalized placement in the
`n`-fold coarsening.  In particular, the `mem` field is a canonical-coarsening
constraint: this is not the type of an arbitrary geometric level pose.  Its
physical support in the original scale is defined below as a `2^n`-scaled
chair. -/
structure LevelSupertilePose (H : Hypotheses) (T : Tiling Q) (n : Nat) where
  pose : RigidMotion
  mem : pose ∈ (coarseningIterate H n T).placements

@[ext] theorem LevelSupertilePose.ext {H : Hypotheses} {T : Tiling Q} {n : Nat}
    {a b : LevelSupertilePose H T n} (h : a.pose = b.pose) : a = b := by
  cases a
  cases b
  simp_all

/-- The geometric chair represented by a normalized level pose, restored to
the original scale.  Scaling the whole normalized placement also scales its
origin, which is exactly inverse to the repeated `halfPose` operation. -/
def LevelSupertilePose.support {H : Hypotheses} {T : Tiling Q} {n : Nat}
    (s : LevelSupertilePose H T n) : Set E3 :=
  (fun x : E3 => ((2 : ℝ) ^ n) • x) '' (s.pose '' P)

/-- Forget the level wrapper and use a normalized supertile as a carrier cell
of the corresponding coarsened tiling. -/
def LevelSupertilePose.cell {H : Hypotheses} {T : Tiling Q} {n : Nat}
    (s : LevelSupertilePose H T n) : CarrierCell (coarseningIterate H n T) :=
  ⟨s.pose, s.mem⟩

/-- Wrap a carrier cell of `D^n(T)` as a level-`n` supertile pose. -/
def LevelSupertilePose.ofCell {H : Hypotheses} {T : Tiling Q} {n : Nat}
    (c : CarrierCell (coarseningIterate H n T)) :
    LevelSupertilePose H T n := ⟨c.1, c.2⟩

@[simp] theorem LevelSupertilePose.cell_ofCell
    {H : Hypotheses} {T : Tiling Q} {n : Nat}
    (c : CarrierCell (coarseningIterate H n T)) :
    (LevelSupertilePose.ofCell c : LevelSupertilePose H T n).cell = c := rfl

/-- The common registration chosen at level `n`.  It is data already supplied
by `registration_of_tiling`, not a new hypothesis. -/
noncomputable def carrierLevelRegistration (H : Hypotheses) (T : Tiling Q)
    (n : Nat) : Registration (coarseningIterate H n T) :=
  Classical.choice (registration_of_tiling H (coarseningIterate H n T))

/-- Every level supertile has a literal proper-cubic, integer registered pose
after the common ambient normalization at that level. -/
theorem LevelSupertilePose.registered {H : Hypotheses} {T : Tiling Q} {n : Nat}
    (s : LevelSupertilePose H T n) :
    Nonempty (RegisteredPose
      ((carrierLevelRegistration H T n).ambient * s.pose)) :=
  ⟨(carrierLevelRegistration H T n).pose s.pose s.mem⟩

/-- The physical `2^n`-scaled chair carried by an arbitrary normalized
geometric pose.  Unlike `LevelSupertilePose.support`, this definition imposes
no membership in `D^n(T)`. -/
def geometricSupertileSupport (n : Nat) (g : RigidMotion) : Set E3 :=
  (fun x : E3 => ((2 : ℝ) ^ n) • x) '' (g '' P)

/-- The parent pose selected by a geometric parent partition for one cell. -/
noncomputable def ParentPartition.parentOf {T : Tiling Q}
    (A : ParentPartition T) (g : CarrierCell T) : {p // p ∈ A.parents} := by
  let h := (A.covers g.1).mp g.2
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem ParentPartition.childOf_parentOf {T : Tiling Q}
    (A : ParentPartition T) (g : CarrierCell T) :
    ∃ i : Fin 8, ChildOfParent (A.parentOf g).1 i g.1 := by
  exact (Classical.choose_spec ((A.covers g.1).mp g.2)).2

/-- The unique `i`th child cell of a specified parent pose. -/
noncomputable def ParentPartition.childAt {T : Tiling Q}
    (A : ParentPartition T) (p : {p // p ∈ A.parents}) (i : Fin 8) :
    CarrierCell T := by
  let h := A.each_child p.1 p.2 i
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem ParentPartition.childAt_is_child {T : Tiling Q}
    (A : ParentPartition T) (p : {p // p ∈ A.parents}) (i : Fin 8) :
    ChildOfParent p.1 i (A.childAt p i).1 := by
  exact (Classical.choose_spec (A.each_child p.1 p.2 i)).2

theorem ParentPartition.parentOf_eq_of_child {T : Tiling Q}
    (A : ParentPartition T) (g : CarrierCell T)
    (p : {p // p ∈ A.parents}) (i : Fin 8)
    (hchild : ChildOfParent p.1 i g.1) : A.parentOf g = p := by
  apply Subtype.ext
  obtain ⟨j, hj⟩ := A.childOf_parentOf g
  exact (A.disjoint (A.parentOf g).2 p.2 hj hchild).1

/-- Halving the affine origin while retaining the linear frame is injective. -/
theorem halfPose_injective : Function.Injective halfPose := by
  intro g h heq
  have hlinear : g.linearIsometryEquiv = h.linearIsometryEquiv := by
    have h := congrArg AffineIsometryEquiv.linearIsometryEquiv heq
    exact h
  have horiginHalf := congrArg (fun k : RigidMotion => k (0 : E3)) heq
  have horigin : g (0 : E3) = h (0 : E3) := by
    simp only [halfPose, AffineIsometryEquiv.coe_mul, Function.comp_apply] at horiginHalf
    simp [translation] at horiginHalf
    apply_fun fun x : E3 => (2 : ℝ) • x at horiginHalf
    simpa [smul_smul] using horiginHalf
  apply AffineIsometryEquiv.ext
  intro x
  have hg := g.map_vadd (0 : E3) x
  have hh := h.map_vadd (0 : E3) x
  simp only [vadd_eq_add, add_zero] at hg hh
  rw [hg, hh, hlinear, horigin]

/-- A parent pose gives the corresponding normalized cell in `D(T)`. -/
def coarsenedParentCell (H : Hypotheses) (T : Tiling Q)
    (p : {p // p ∈ (uniqueParentPartition H T).parents}) :
    CarrierCell (coarsening H T) := by
  refine ⟨halfPose p.1, ?_⟩
  rw [coarsening_placements]
  exact ⟨p.1, p.2, rfl⟩

/-- Send one carrier cell to the normalized pose of its unique parent. -/
noncomputable def coarsenCarrierCell (H : Hypotheses) (T : Tiling Q)
    (g : CarrierCell T) : CarrierCell (coarsening H T) :=
  coarsenedParentCell H T ((uniqueParentPartition H T).parentOf g)

/-- The fiber of a coarsened parent is exactly its eight literal child cells. -/
theorem coarsenCarrierCell_eq_parent_iff (H : Hypotheses) (T : Tiling Q)
    (g : CarrierCell T)
    (p : {p // p ∈ (uniqueParentPartition H T).parents}) :
    coarsenCarrierCell H T g = coarsenedParentCell H T p ↔
      ∃ i : Fin 8, g = (uniqueParentPartition H T).childAt p i := by
  let A := uniqueParentPartition H T
  constructor
  · intro heq
    have hhalf := congrArg (fun c : CarrierCell (coarsening H T) => c.1) heq
    have hp : A.parentOf g = p := by
      apply Subtype.ext
      exact halfPose_injective hhalf
    obtain ⟨i, hi⟩ := A.childOf_parentOf g
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact childOfParent_unique (hp ▸ hi) (A.childAt_is_child p i)
  · rintro ⟨i, rfl⟩
    have hp : A.parentOf (A.childAt p i) = p :=
      A.parentOf_eq_of_child (A.childAt p i) p i (A.childAt_is_child p i)
    apply Subtype.ext
    change halfPose (A.parentOf (A.childAt p i)).1 = halfPose p.1
    rw [hp]

/-- The cells assigned by a literal level partition to one supertile pose. -/
def hierarchyFiber {H : Hypotheses} {T : Tiling Q}
    (partition : ∀ n : Nat, CarrierCell T → LevelSupertilePose H T n)
    {n : Nat} (s : LevelSupertilePose H T n) : Set (CarrierCell T) :=
  {c | (partition n c).pose = s.pose}

/-- Eight-child nesting for a family already valued in canonical level poses.
The body of the predicate does not apply the coarsening recurrence, but its
`LevelSupertilePose` codomain still constrains every pose to `D^n(T)`.  The
unconstrained geometric analogue is `GeometricHierarchyNested` below. -/
def IntrinsicCarrierHierarchyNested {H : Hypotheses} {T : Tiling Q}
    (partition : ∀ n : Nat, CarrierCell T → LevelSupertilePose H T n) : Prop :=
  ∀ (n : Nat) (c : CarrierCell T),
    ∃ parentPose : RigidMotion,
      halfPose parentPose = (partition (n + 1) c).pose ∧
      ∃ childPoses : Fin 8 → LevelSupertilePose H T n,
        (∀ i : Fin 8, ChildOfParent parentPose i (childPoses i).pose) ∧
        (∀ i : Fin 8, ∃ d : CarrierCell T, partition n d = childPoses i) ∧
        hierarchyFiber partition (partition (n + 1) c) =
          ⋃ i : Fin 8, hierarchyFiber partition (childPoses i)

/-- A canonical carrier hierarchy is a family of cell-to-supertile functions
whose `LevelSupertilePose.mem` proofs place every level-`n` value in `D^n(T)`.
Its nesting law is geometric, but its partition codomain carries this
canonical-coarsening constraint.  `GeometricHierarchy` below is the genuinely
unconstrained raw-pose structure. -/
structure CarrierHierarchy (H : Hypotheses) (T : Tiling Q) where
  partition : ∀ n : Nat, CarrierCell T → LevelSupertilePose H T n
  level_zero : ∀ c : CarrierCell T, (partition 0 c).pose = c.1
  nested : IntrinsicCarrierHierarchyNested partition

/-- The cells of `T` assigned to one level supertile. -/
def CarrierHierarchy.fiber {H : Hypotheses} {T : Tiling Q}
    (K : CarrierHierarchy H T) {n : Nat} (s : LevelSupertilePose H T n) :
    Set (CarrierCell T) := hierarchyFiber K.partition s

/-- Public spelling of the intrinsic nesting field. -/
def CarrierHierarchyNested {H : Hypotheses} {T : Tiling Q}
    (K : CarrierHierarchy H T) : Prop :=
  IntrinsicCarrierHierarchyNested K.partition

/-- The cells assigned by a raw geometric level partition to one pose. -/
def geometricHierarchyFiber {T : Tiling Q}
    (partition : ∀ n : Nat, CarrierCell T → RigidMotion)
    {n : Nat} (s : RigidMotion) : Set (CarrierCell T) :=
  {c | partition n c = s}

/-- Intrinsic eight-child nesting for raw geometric poses.  The parent and
child relations are stated through `ChildOfParent`, every child occurs in the
same level-`n` partition, and the parent fiber is exactly the union of the
eight child fibers.  This predicate contains no reference to `coarsening`,
`coarseningIterate`, or `LevelSupertilePose`. -/
def GeometricHierarchyNested {T : Tiling Q}
    (partition : ∀ n : Nat, CarrierCell T → RigidMotion) : Prop :=
  ∀ (n : Nat) (c : CarrierCell T),
    ∃ parentPose : RigidMotion,
      halfPose parentPose = partition (n + 1) c ∧
      ∃ childPoses : Fin 8 → RigidMotion,
        (∀ i : Fin 8, ChildOfParent parentPose i (childPoses i)) ∧
        (∀ i : Fin 8, ∃ d : CarrierCell T, partition n d = childPoses i) ∧
        geometricHierarchyFiber (n := n + 1) partition (partition (n + 1) c) =
          ⋃ i : Fin 8, geometricHierarchyFiber (n := n) partition (childPoses i)

/-- An arbitrary geometric hierarchy of normalized poses.  No partition value
is assumed to lie in `D^n(T)`.  At each level one common ambient motion
registers all normalized poses; `geometricSupertileSupport n` restores the
physical `2^n`-scaled chairs. -/
structure GeometricHierarchy (H : Hypotheses) (T : Tiling Q) where
  partition : ∀ n : Nat, CarrierCell T → RigidMotion
  level_zero : ∀ c : CarrierCell T, partition 0 c = c.1
  registered : ∀ n : Nat, ∃ A : RigidMotion, ∀ c : CarrierCell T,
    Nonempty (RegisteredPose (A * partition n c))
  nested : GeometricHierarchyNested partition

/-- The raw partition determines a geometric hierarchy; the remaining fields
are propositions. -/
@[ext] theorem GeometricHierarchy.ext {H : Hypotheses} {T : Tiling Q}
    {K K' : GeometricHierarchy H T} (h : K.partition = K'.partition) : K = K' := by
  cases K
  cases K'
  cases h
  rfl

/-- The canonical hierarchy obtained by iterating `D` cell by cell. -/
noncomputable def carrierHierarchyPartition (H : Hypotheses) (T : Tiling Q) :
    ∀ n : Nat, CarrierCell T → LevelSupertilePose H T n
  | 0, c => ⟨c.1, c.2⟩
  | n + 1, c => @LevelSupertilePose.ofCell H T (n + 1)
      (coarsenCarrierCell H (coarseningIterate H n T)
        (carrierHierarchyPartition H T n c).cell)

private theorem carrierHierarchyPartition_surjective (H : Hypotheses) (T : Tiling Q) :
    ∀ (n : Nat) (s : LevelSupertilePose H T n),
      ∃ c : CarrierCell T, carrierHierarchyPartition H T n c = s := by
  intro n
  induction n with
  | zero =>
      intro s
      refine ⟨s.cell, ?_⟩
      apply LevelSupertilePose.ext
      rfl
  | succ n ih =>
      intro s
      have hs : s.pose ∈
          halvedParentPoses
            (uniqueParentPartition H (coarseningIterate H n T)) := by
        rw [← coarsening_placements]
        exact s.mem
      obtain ⟨p, hp, hpose⟩ := hs
      let ps : {p // p ∈
          (uniqueParentPartition H (coarseningIterate H n T)).parents} := ⟨p, hp⟩
      let child :=
        (uniqueParentPartition H (coarseningIterate H n T)).childAt ps (0 : Fin 8)
      let childLevel : LevelSupertilePose H T n :=
        @LevelSupertilePose.ofCell H T n child
      obtain ⟨c, hc⟩ := ih childLevel
      refine ⟨c, ?_⟩
      apply LevelSupertilePose.ext
      change
        (coarsenCarrierCell H (coarseningIterate H n T)
          (carrierHierarchyPartition H T n c).cell).1 = s.pose
      rw [hc]
      have hparent :=
        (coarsenCarrierCell_eq_parent_iff H (coarseningIterate H n T)
          child ps).mpr ⟨(0 : Fin 8), rfl⟩
      exact (congrArg Subtype.val hparent).trans hpose

private theorem carrierHierarchyPartition_nested (H : Hypotheses) (T : Tiling Q) :
    IntrinsicCarrierHierarchyNested (carrierHierarchyPartition H T) := by
  intro n c
  let s := carrierHierarchyPartition H T (n + 1) c
  have hs : s.pose ∈
      halvedParentPoses
        (uniqueParentPartition H (coarseningIterate H n T)) := by
    rw [← coarsening_placements]
    exact s.mem
  obtain ⟨p, hp, hpose⟩ := hs
  let ps : {p // p ∈
      (uniqueParentPartition H (coarseningIterate H n T)).parents} := ⟨p, hp⟩
  have hsEq : s = @LevelSupertilePose.ofCell H T (n + 1)
      (coarsenedParentCell H (coarseningIterate H n T) ps) := by
    apply LevelSupertilePose.ext
    exact hpose.symm
  refine ⟨p, hpose, fun i => @LevelSupertilePose.ofCell H T n
    ((uniqueParentPartition H (coarseningIterate H n T)).childAt ps i), ?_, ?_, ?_⟩
  · exact fun i =>
      (uniqueParentPartition H (coarseningIterate H n T)).childAt_is_child ps i
  · intro i
    exact carrierHierarchyPartition_surjective H T n _
  · change hierarchyFiber (carrierHierarchyPartition H T) s = _
    rw [hsEq]
    ext d
    simp only [hierarchyFiber, Set.mem_setOf_eq, Set.mem_iUnion]
    change
      (coarsenCarrierCell H (coarseningIterate H n T)
          (carrierHierarchyPartition H T n d).cell).1 =
          (coarsenedParentCell H (coarseningIterate H n T) ps).1 ↔
        ∃ i, (carrierHierarchyPartition H T n d).pose =
          ((uniqueParentPartition H (coarseningIterate H n T)).childAt ps i).1
    constructor
    · intro heq
      have hcell :
          coarsenCarrierCell H (coarseningIterate H n T)
              (carrierHierarchyPartition H T n d).cell =
            coarsenedParentCell H (coarseningIterate H n T) ps := by
        apply Subtype.ext
        exact heq
      obtain ⟨i, hi⟩ :=
        (coarsenCarrierCell_eq_parent_iff H (coarseningIterate H n T)
          (carrierHierarchyPartition H T n d).cell ps).mp hcell
      refine ⟨i, ?_⟩
      exact congrArg Subtype.val hi
    · rintro ⟨i, hi⟩
      have hcell :
          (carrierHierarchyPartition H T n d).cell =
            (uniqueParentPartition H (coarseningIterate H n T)).childAt ps i := by
        apply Subtype.ext
        exact hi
      have hparent :=
        (coarsenCarrierCell_eq_parent_iff H (coarseningIterate H n T)
          (carrierHierarchyPartition H T n d).cell ps).mpr ⟨i, hcell⟩
      exact congrArg Subtype.val hparent

/-- The canonical hierarchy constructed by iterating the derived coarsening.
Its `LevelSupertilePose` codomain records membership in `D^n(T)`, while its
additional nesting field records the intrinsic geometric fiber law. -/
noncomputable def carrierHierarchy (H : Hypotheses) (T : Tiling Q) :
    CarrierHierarchy H T where
  partition := carrierHierarchyPartition H T
  level_zero := by intro c; rfl
  nested := carrierHierarchyPartition_nested H T

/-- Existence of an intrinsic carrier hierarchy, witnessed by iterated `D`. -/
theorem carrier_hierarchy_exists (H : Hypotheses) (T : Tiling Q) :
    Nonempty (CarrierHierarchy H T) :=
  ⟨carrierHierarchy H T⟩

/-- Forget the canonical membership proofs in a `CarrierHierarchy`, retaining
its raw geometric poses, common level registrations, and intrinsic nesting. -/
noncomputable def CarrierHierarchy.toGeometric {H : Hypotheses} {T : Tiling Q}
    (K : CarrierHierarchy H T) : GeometricHierarchy H T where
  partition := fun n c => (K.partition n c).pose
  level_zero := K.level_zero
  registered := by
    intro n
    refine ⟨(carrierLevelRegistration H T n).ambient, ?_⟩
    intro c
    exact (K.partition n c).registered
  nested := by
    unfold GeometricHierarchyNested
    intro n c
    obtain ⟨p, hpPose, childPoses, hpChildren, hpOccurs, hpFibers⟩ :=
      K.nested n c
    refine ⟨p, hpPose, fun i => (childPoses i).pose, hpChildren, ?_, ?_⟩
    · intro i
      obtain ⟨d, hd⟩ := hpOccurs i
      exact ⟨d, congrArg LevelSupertilePose.pose hd⟩
    · simpa [geometricHierarchyFiber, hierarchyFiber] using hpFibers

/-- The canonical carrier hierarchy supplies an unconstrained geometric
hierarchy witness after its membership proofs are forgotten. -/
theorem carrierHierarchy_geometric (H : Hypotheses) (T : Tiling Q) :
    Nonempty (GeometricHierarchy H T) :=
  ⟨(carrierHierarchy H T).toGeometric⟩

/-- Every complete geometric parent is one of the parents selected by T7.1.
This is the bridge needed before a raw next-level pose may be put in `D(T)`. -/
private theorem completeParent_mem_uniqueParentPartition
    (H : Hypotheses) (T : Tiling Q) {p : RigidMotion}
    (hp : CompleteParent T p) :
    p ∈ (uniqueParentPartition H T).parents := by
  let A := uniqueParentPartition H T
  obtain ⟨g, hg, hpg⟩ := hp centralChildIndex
  obtain ⟨q, hq, j, hqg⟩ := (A.covers g).mp hg
  have hexists : EveryPlacementHasCompleteParent T := by
    intro h hh
    obtain ⟨r, hr, i, hri⟩ := (A.covers h).mp hh
    exact ⟨r, A.each_child r hr, i, hri⟩
  have hpq := complete_parent_conflicts H T (registration_of_tiling H T)
    hexists children_partition_2P parent_conflicts_28 hp (A.each_child q hq)
    hpg hqg
  rwa [hpq.1]

/-- Theorem 6.6's written induction: every arbitrary geometrically nested
registered hierarchy is forced into the canonical iterated coarsenings. -/
theorem geometric_hierarchy_canonical (H : Hypotheses) (T : Tiling Q)
    (K : GeometricHierarchy H T) : ∀ (n : Nat) (c : CarrierCell T),
    K.partition n c ∈ (coarseningIterate H n T).placements := by
  intro n
  induction n with
  | zero =>
      intro c
      simpa [coarseningIterate, K.level_zero c] using c.2
  | succ n ih =>
      intro c
      have hNested := K.nested
      unfold GeometricHierarchyNested at hNested
      obtain ⟨p, hpPose, childPoses, hpChildren, hpOccurs, _hpFibers⟩ :=
        hNested n c
      have hpComplete : CompleteParent (coarseningIterate H n T) p := by
        intro i
        obtain ⟨d, hd⟩ := hpOccurs i
        refine ⟨childPoses i, ?_, hpChildren i⟩
        rw [← hd]
        exact ih d
      have hpMem := completeParent_mem_uniqueParentPartition
        H (coarseningIterate H n T) hpComplete
      rw [coarseningIterate, coarsening_placements]
      exact ⟨p, hpMem, hpPose⟩

private theorem parent_mem_of_level_pose {H : Hypotheses} {T : Tiling Q}
    {n : Nat} (s : LevelSupertilePose H T (n + 1)) (p : RigidMotion)
    (hpose : halfPose p = s.pose) :
    p ∈ (uniqueParentPartition H (coarseningIterate H n T)).parents := by
  have hs : s.pose ∈
      halvedParentPoses
        (uniqueParentPartition H (coarseningIterate H n T)) := by
    rw [← coarsening_placements]
    exact s.mem
  obtain ⟨q, hq, hqpose⟩ := hs
  have hpq : p = q := halfPose_injective (hpose.trans hqpose.symm)
  rwa [hpq]

/-- Intrinsic uniqueness.  At each level the two candidate next-level poses
share the preceding-level cell, so Theorem 7.1's unique `ParentPartition`
identifies their geometric parent poses. -/
theorem carrier_hierarchy_unique (H : Hypotheses) (T : Tiling Q)
    (K K' : CarrierHierarchy H T) : K = K' := by
  have hpartition : K.partition = K'.partition := by
    funext n c
    induction n with
    | zero =>
        apply LevelSupertilePose.ext
        exact (K.level_zero c).trans (K'.level_zero c).symm
    | succ n ih =>
        obtain ⟨p, hpPose, childPoses, hpChildren, _hpOccurs, hpFibers⟩ :=
          K.nested n c
        obtain ⟨q, hqPose, childPoses', hqChildren, _hqOccurs, hqFibers⟩ :=
          K'.nested n c
        have hcP : c ∈ hierarchyFiber K.partition (K.partition (n + 1) c) := rfl
        rw [hpFibers] at hcP
        simp only [Set.mem_iUnion, hierarchyFiber, Set.mem_setOf_eq] at hcP
        obtain ⟨i, hi⟩ := hcP
        have hcQ : c ∈ hierarchyFiber K'.partition (K'.partition (n + 1) c) := rfl
        rw [hqFibers] at hcQ
        simp only [Set.mem_iUnion, hierarchyFiber, Set.mem_setOf_eq] at hcQ
        obtain ⟨j, hj⟩ := hcQ
        have hpChild : ChildOfParent p i (K.partition n c).pose := by
          rw [hi]
          exact hpChildren i
        have hqChild : ChildOfParent q j (K'.partition n c).pose := by
          rw [hj]
          exact hqChildren j
        have hqChild' : ChildOfParent q j (K.partition n c).pose := by
          rw [ih]
          exact hqChild
        have hpMem := parent_mem_of_level_pose (K.partition (n + 1) c) p hpPose
        have hqMem := parent_mem_of_level_pose (K'.partition (n + 1) c) q hqPose
        have hpq :=
          (uniqueParentPartition H (coarseningIterate H n T)).disjoint
            hpMem hqMem hpChild hqChild'
        apply LevelSupertilePose.ext
        calc
          (K.partition (n + 1) c).pose = halfPose p := hpPose.symm
          _ = halfPose q := congrArg halfPose hpq.1
          _ = (K'.partition (n + 1) c).pose := hqPose
  cases K
  cases K'
  simp_all

/-- Equip a raw geometric hierarchy with the canonical-membership proofs
forced by `geometric_hierarchy_canonical`. -/
noncomputable def GeometricHierarchy.toCarrier {H : Hypotheses} {T : Tiling Q}
    (K : GeometricHierarchy H T) : CarrierHierarchy H T where
  partition := fun n c => ⟨K.partition n c,
    geometric_hierarchy_canonical H T K n c⟩
  level_zero := K.level_zero
  nested := by
    intro n c
    have hNested := K.nested
    unfold GeometricHierarchyNested at hNested
    obtain ⟨p, hpPose, childPoses, hpChildren, hpOccurs, hpFibers⟩ :=
      hNested n c
    have hchildMem : ∀ i : Fin 8,
        childPoses i ∈ (coarseningIterate H n T).placements := by
      intro i
      obtain ⟨d, hd⟩ := hpOccurs i
      rw [← hd]
      exact geometric_hierarchy_canonical H T K n d
    refine ⟨p, hpPose, fun i => ⟨childPoses i, hchildMem i⟩,
      hpChildren, ?_, ?_⟩
    · intro i
      obtain ⟨d, hd⟩ := hpOccurs i
      refine ⟨d, ?_⟩
      apply LevelSupertilePose.ext
      exact hd
    · simpa [geometricHierarchyFiber, hierarchyFiber] using hpFibers

/-- Arbitrary geometrically nested registered hierarchies are unique.  The
proof first applies the canonical-membership induction and then invokes the
canonical hierarchy uniqueness theorem. -/
theorem geometric_hierarchy_unique (H : Hypotheses) (T : Tiling Q)
    (K K' : GeometricHierarchy H T) : K = K' := by
  apply GeometricHierarchy.ext
  funext n c
  exact congrArg (fun L : CarrierHierarchy H T => (L.partition n c).pose)
    (carrier_hierarchy_unique H T K.toCarrier K'.toCarrier)

/-- Forgetting and then restoring the canonical membership proofs changes no
`CarrierHierarchy` data. -/
@[simp] theorem CarrierHierarchy.toGeometric_toCarrier
    {H : Hypotheses} {T : Tiling Q} (K : CarrierHierarchy H T) :
    K.toGeometric.toCarrier = K :=
  carrier_hierarchy_unique H T _ _

/-- Canonicalizing and then forgetting a geometric hierarchy returns the raw
geometric hierarchy itself. -/
@[simp] theorem GeometricHierarchy.toCarrier_toGeometric
    {H : Hypotheses} {T : Tiling Q} (K : GeometricHierarchy H T) :
    K.toCarrier.toGeometric = K := by
  apply GeometricHierarchy.ext
  rfl

/-- **Ruling R7 / carrier hierarchy.**  Every tiling by `Q` has the literal
coarsening hierarchy: level zero is its registered carrier cells; every level
pose is registered and represents a `2^n`-scaled chair; every next-level fiber
is intrinsically the union of eight geometric child-pose fibers; and any two
canonical hierarchy objects are equal.  The separate
`geometric_hierarchy_canonical` and `geometric_hierarchy_unique` theorems extend
this to arbitrary raw-pose geometric hierarchies.  No exhaustion or
local-derivability claim is made. -/
theorem carrier_hierarchy (H : Hypotheses) (T : Tiling Q) :
    (∀ c : CarrierCell T, (carrierHierarchy H T).partition 0 c =
      @LevelSupertilePose.ofCell H T 0 c) ∧
    (∀ (n : Nat) (c : CarrierCell T),
      Nonempty (RegisteredPose ((carrierLevelRegistration H T n).ambient *
        ((carrierHierarchy H T).partition n c).pose))) ∧
    CarrierHierarchyNested (carrierHierarchy H T) ∧
    ∀ K K' : CarrierHierarchy H T, K = K' := by
  refine ⟨?_, ?_, (carrierHierarchy H T).nested, ?_⟩
  · intro c
    rfl
  · intro n c
    exact ((carrierHierarchy H T).partition n c).registered
  · exact carrier_hierarchy_unique H T

def dyadicScale (n : Nat) (p : E3) : E3 := ((2 : ℝ) ^ n)⁻¹ • p

theorem period_iterate (H : Hypotheses) (T : Tiling Q) {p : E3}
    (hp : p ∈ Per T) : ∀ n, dyadicScale n p ∈ Per (coarseningIterate H n T) := by
  intro n
  induction n with
  | zero => simpa [coarseningIterate, dyadicScale] using hp
  | succ n ih =>
      simpa [coarseningIterate, dyadicScale, pow_succ, mul_smul] using
        period_halving H (coarseningIterate H n T) ih

theorem gridVector_norm_separated {v : E3} (hv : GridVector v) (hne : v ≠ 0) :
    1 ≤ ‖v‖ := by
  obtain ⟨A, hA⟩ := hv
  have hAv : A v ≠ 0 := fun h => hne (A.injective (by simpa using h))
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, (A v) i ≠ 0 := by
    by_contra h
    apply hAv
    ext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨z, hz⟩ := hA i
  have hz0 : z ≠ 0 := by
    intro hz0
    apply hi
    simpa [hz0] using hz
  have hone : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast Int.one_le_abs hz0
  have hcoord : |(A v) i| ≤ ‖A v‖ := by
    simpa [Real.norm_eq_abs] using
      PiLp.norm_apply_le (A v) i
  calc
    (1 : ℝ) ≤ |(z : ℝ)| := hone
    _ = |(A v) i| := by rw [hz]
    _ ≤ ‖A v‖ := hcoord
    _ = ‖v‖ := A.norm_map v

private theorem nat_le_two_pow : ∀ n : Nat, n ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

/-- If every dyadic rescaling of `p` is an integer-grid vector in some
    orthonormal frame, then `p=0`.  This is the R§10 period-exclusion tower. -/
theorem no_period (p : E3) (hgrid : ∀ n, GridVector (dyadicScale n p)) : p = 0 := by
  by_contra hp
  obtain ⟨n, hn⟩ := exists_nat_gt ‖p‖
  have hscaled_ne : dyadicScale n p ≠ 0 := by
    simp [dyadicScale, hp]
  have hsep := gridVector_norm_separated (hgrid n) hscaled_ne
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hnorm : ‖dyadicScale n p‖ = ‖p‖ / (2 : ℝ) ^ n := by
    simp only [dyadicScale, norm_smul, norm_inv, Real.norm_ofNat, norm_pow]
    rw [div_eq_inv_mul]
  rw [hnorm] at hsep
  have hpow_le : (2 : ℝ) ^ n ≤ ‖p‖ := by
    simpa using (le_div_iff₀ hpow_pos).mp hsep
  have hn_le : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast nat_le_two_pow n
  exact (not_lt_of_ge (hn_le.trans hpow_le)) hn

private theorem symmetry_code_injective (T : Tiling Q) (R : Registration T)
    (hnative : NativeAsymmetric Q) (hper : Per T = {0}) :
    ∃ code : Sym T → Fin 24, Function.Injective code := by
  obtain ⟨code, hcode⟩ := symmetry_code_from_registered_poses T R hnative
  refine ⟨code, ?_⟩
  intro a b hab
  obtain ⟨v, hv, heq⟩ := hcode a b hab
  have hv0 : v = 0 := by simpa [hper] using hv
  exact Subtype.ext (by simpa [hv0] using heq)

/-- Native asymmetry and the 24 proper registered frames bound the full
    tiling-symmetry group.  `encard` is used because it states finiteness and
    the bound simultaneously, before a `Fintype` instance has been installed. -/
theorem sym_card_le_24 (T : Tiling Q) (R : Registration T)
    (hnative : NativeAsymmetric Q) (hper : Per T = {0}) :
    (Set.univ : Set (Sym T)).encard ≤ 24 := by
  obtain ⟨code, hcode⟩ := symmetry_code_injective T R hnative hper
  rw [Set.encard_univ]
  exact (ENat.card_le_card_of_injective hcode).trans_eq (by simp)

/-- Section 9 reconstructed from the exact nested pose union: the all-n
    baseline exhaustion and contact-language induction feed the same
    small-collar realization used by coarsening. -/
theorem nested_exhaustion (H : Hypotheses)
    (hchildren : childrenPartitionCheck = true)
    (hcontacts : contactClosureCheck = true)
    (hnested : nestedPatchControlsCheck = true) : Nonempty (Tiling Q) := by
  let C := Classical.choice
    (nested_atlas_baseline_assembly hchildren hcontacts hnested)
  obtain ⟨T, hT⟩ := small_collar_realization_holds (tube_homeomorphism H)
    hierarchyPlacements C
  exact ⟨T⟩

/-- Section 9: the nested all-scale construction gives a nonempty tiling
    space; the finite same-frame grandchild and `n≤2` controls are phase 1. -/
theorem existence (H : Hypotheses) : Nonempty (Tiling Q) :=
  nested_exhaustion H children_partition_2P contact_closure_30
    nested_substitution_controls

private theorem all_periods_grid (H : Hypotheses) (T : Tiling Q)
    {p : E3} (hp : p ∈ Per T) :
    ∀ n, GridVector (dyadicScale n p) := by
  intro n
  let R := Classical.choice
    (registration_of_tiling H (coarseningIterate H n T))
  exact period_grid_from_registered_poses (coarseningIterate H n T) R
    (native_asymmetry_reduction (native_asymmetry_planar_reduction H) no_native_symmetry)
    (period_iterate H T hp n)

/-- The determinant of the linear part of a rigid motion is `1` or `-1`. -/
theorem handedness_eq_one_or_neg_one (g : RigidMotion) :
    handedness g = 1 ∨ handedness g = -1 := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let M := LinearMap.toMatrix b.toBasis b.toBasis
    g.linearIsometryEquiv.toLinearEquiv.toLinearMap
  have hM : M ∈ Matrix.unitaryGroup (Fin 3) ℝ :=
    LinearIsometryEquiv.toMatrix_mem_unitaryGroup
      g.linearIsometryEquiv b b
  have hunit := Matrix.det_of_mem_unitary hM
  have hsq : M.det ^ 2 = 1 := by
    simpa [unitary, sq, mul_comm] using hunit.2
  have hor : M.det = 1 ∨ M.det = -1 := sq_eq_one_iff.mp hsq
  simpa [handedness, M, LinearMap.det_toMatrix] using hor

/-- Handedness is multiplicative under composition of rigid motions. -/
theorem handedness_mul (a b : RigidMotion) :
    handedness (a * b) = handedness a * handedness b := by
  change LinearMap.det
      (a.linearIsometryEquiv.toLinearEquiv.toLinearMap.comp
        b.linearIsometryEquiv.toLinearEquiv.toLinearMap) = _
  exact LinearMap.det_comp _ _

/-- Every literal registered frame is one of the 24 proper cubic frames and
    therefore has determinant `1`. -/
private theorem RegisteredPose.handedness_eq_one
    {g : RigidMotion} (r : RegisteredPose g) : handedness g = 1 := by
  let b := PiLp.basisFun 2 ℝ (Fin 3)
  rw [handedness, ← LinearMap.det_toMatrix b]
  rw [Matrix.det_fin_three]
  have hentry (i j : Fin 3) :
      LinearMap.toMatrix b b g.linearIsometryEquiv.toLinearEquiv.toLinearMap i j =
        frameActReal (getD orientationGroup r.frameIndex identityFrame)
          (b j) i := by
    rw [LinearMap.toMatrix_apply]
    exact r.linear_eq (b j) i
  simp_rw [hentry]
  generalize hk : r.frameIndex = k at *
  fin_cases k <;>
    norm_num [b, PiLp.basisFun_apply, frameActReal, frameCoordinate,
      orientationGroup, getD, identityFrame, fr, n3, v, N3.get, V3.get,
      PiLp.single_apply, Fin.ext_iff]

/-- A single registration witnesses that every two placements have the same
    handedness: the common ambient determinant cancels from the two proper
    registered frames. -/
theorem Registration.handedness_eq {S : Set E3} {T : Tiling S}
    (R : Registration T) (g h : RigidMotion)
    (hg : g ∈ T.placements) (hh : h ∈ T.placements) :
    handedness g = handedness h := by
  have hg_one := (R.pose g hg).handedness_eq_one
  have hh_one := (R.pose h hh).handedness_eq_one
  rw [handedness_mul] at hg_one hh_one
  have hambient_ne : handedness R.ambient ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hg_one
    norm_num at hg_one
  apply mul_left_cancel₀ hambient_ne
  exact hg_one.trans hh_one.symm

/-- Every tiling by `Q` is homochiral: reflections of a whole tiling are
    allowed, but its two handedness sectors cannot mix. -/
theorem tiling_homochiral (H : Hypotheses) (T : Tiling Q) :
    ∀ g h : RigidMotion, g ∈ T.placements → h ∈ T.placements →
      handedness g = handedness h := by
  exact (Classical.choice (registration_of_tiling H T)).handedness_eq

/-- Relative to one ambient isometry, every placement in a tiling by `Q` is
    orientation-preserving. -/
theorem tiling_orientation_normalization (H : Hypotheses) (T : Tiling Q) :
    ∃ A : RigidMotion, ∀ g : RigidMotion, g ∈ T.placements →
      handedness (A * g) = 1 := by
  let R := Classical.choice (registration_of_tiling H T)
  exact ⟨R.ambient, fun g hg => (R.pose g hg).handedness_eq_one⟩

/-- In a fixed ambient orientation, every tiling by `Q` consists either only
    of orientation-preserving copies or only of orientation-reversing copies. -/
theorem tiling_handedness_dichotomy (H : Hypotheses) (T : Tiling Q) :
    (∀ g : RigidMotion, g ∈ T.placements → handedness g = 1) ∨
      (∀ g : RigidMotion, g ∈ T.placements → handedness g = -1) := by
  obtain ⟨g, hg, _⟩ := T.covers (0 : E3)
  rcases handedness_eq_one_or_neg_one g with hg_one | hg_neg_one
  · left
    intro h hh
    rw [tiling_homochiral H T h g hh hg, hg_one]
  · right
    intro h hh
    rw [tiling_homochiral H T h g hh hg, hg_neg_one]

/-- No two placements in a tiling by `Q` have opposite handedness. -/
theorem no_mixed_handedness (H : Hypotheses) (T : Tiling Q) :
    ¬ ∃ g : RigidMotion, g ∈ T.placements ∧
        ∃ h : RigidMotion, h ∈ T.placements ∧ handedness g ≠ handedness h := by
  rintro ⟨g, hg, h, hh, hne⟩
  exact hne (tiling_homochiral H T g h hg hh)

/-- Paper-facing two-sided chirality corollary: the tiling lies wholly in one
    determinant sector, and an unreflected (`+1`) and reflected (`-1`) copy
    never occur together. -/
theorem tiling_chirality_corollary (H : Hypotheses) (T : Tiling Q) :
    ((∀ g : RigidMotion, g ∈ T.placements → handedness g = 1) ∨
      (∀ g : RigidMotion, g ∈ T.placements → handedness g = -1)) ∧
    ¬ ∃ g : RigidMotion, g ∈ T.placements ∧ handedness g = 1 ∧
        ∃ h : RigidMotion, h ∈ T.placements ∧ handedness h = -1 := by
  refine ⟨tiling_handedness_dichotomy H T, ?_⟩
  rintro ⟨g, hg, hg_one, h, hh, hh_neg_one⟩
  have heq := tiling_homochiral H T g h hg hh
  rw [hg_one, hh_neg_one] at heq
  norm_num at heq

/-- Historical conditional form of the R44 conclusion. All 19 hypothesis
    fields were discharged in exchanges 1–7; the empty argument is retained
    so earlier review receipts naming this theorem continue to resolve. -/
theorem r44_einstein_of_hypotheses (H : Hypotheses) :
    Nonempty (Tiling Q) ∧
      ∀ T : Tiling Q, Per T = {0} ∧ (Set.univ : Set (Sym T)).encard ≤ 24 := by
  refine ⟨existence H, ?_⟩
  intro T
  have hper : Per T = {0} := by
    apply Set.Subset.antisymm
    · intro p hp
      have hp0 : p = 0 := no_period p (all_periods_grid H T hp)
      simp [hp0]
    · intro p hp
      have hp0 : p = 0 := by simpa using hp
      subst p
      change translation 0 • tileFamily T = tileFamily T
      rw [translation_zero]
      exact one_smul RigidMotion (tileFamily T)
  refine ⟨hper, ?_⟩
  let R := Classical.choice (registration_of_tiling H T)
  exact sym_card_le_24 T R
    (native_asymmetry_reduction (native_asymmetry_planar_reduction H) no_native_symmetry) hper

/-- The unconditional R44 conclusion. The `encard` inequality is equivalent
    to finiteness of `Sym T` together with finite cardinal at most 24. -/
theorem r44_einstein : Nonempty (Tiling Q) ∧ ∀ T : Tiling Q,
    Per T = {0} ∧ (Set.univ : Set (Sym T)).encard ≤ 24 :=
  r44_einstein_of_hypotheses ⟨⟩

end

end R44
