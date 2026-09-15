import Mathlib
import R44.Theorems

/-!
# Geometric foundation for the R44 logical spine

The geometric object and its feature strata are definitions from the phase-1
literal tables. The endpoint proposition types needed by the promoted Phase F
proofs are defined here, before the residual-hypothesis record. The finite
premises are the phase-1 theorems imported from `R44.Theorems`.
-/

namespace R44

open scoped Pointwise
open Set
open Generated

noncomputable section

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev RigidMotion := E3 ≃ᵃⁱ[ℝ] E3
abbrev Role := Fin 192

/-- The canonical handedness of an affine Euclidean isometry: the determinant
    of its linear part.  This is basis-independent and is `1` for an
    orientation-preserving motion and `-1` for an orientation-reversing one. -/
noncomputable def handedness (g : RigidMotion) : ℝ :=
  LinearMap.det g.linearIsometryEquiv.toLinearEquiv.toLinearMap

/-- Affine isometries act on Euclidean space by evaluation. -/
noncomputable instance rigidMotionAction : MulAction RigidMotion E3 where
  smul g x := g x
  one_smul x := by rfl
  mul_smul g h x := by rfl

/-- Embed a literal integer cell corner in Euclidean three-space. -/
def cellCorner (a : V3) : E3 :=
  WithLp.toLp 2 fun i : Fin 3 => (a.get i : ℝ)

/-- Embed a literal integer vector after division by `d`. -/
def scaledV3 (d : ℝ) (a : V3) : E3 :=
  WithLp.toLp 2 fun i : Fin 3 => (a.get i : ℝ) / d

/-- The `i`th ambient coordinate unit vector (out-of-range indices give zero). -/
def coordinateVector (i : Nat) : E3 :=
  WithLp.toLp 2 fun j : Fin 3 => if j.val = i then 1 else 0

def frameCoordinate (x : E3) (i : Nat) : ℝ :=
  if h : i < 3 then x ⟨i, h⟩ else 0

/-- The closed unit cube whose lower corner is `a`. -/
def unitCube (a : V3) : Set E3 :=
  {x | ∀ i : Fin 3, (a.get i : ℝ) ≤ x i ∧ x i ≤ (a.get i : ℝ) + 1}

/-- The closed seven-cube chair carrier underlying `Q`, defined from the
    phase-1 integer cell model rather than introduced as new geometric data. -/
def P : Set E3 := {x | ∃ a ∈ chairCells, x ∈ unitCube a}

/-! The carrier's elementary topology is proved once for the literal list of
seven closed cubes.  Working through the finite product homeomorphism keeps
these proofs independent of the feature deformation. -/

def coordinateBox (a : V3) : Set (Fin 3 → ℝ) :=
  Set.univ.pi fun i => Set.Icc (a.get i : ℝ) ((a.get i : ℝ) + 1)

theorem unitCube_eq_preimage (a : V3) :
    unitCube a = (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)) ⁻¹' coordinateBox a := by
  ext x
  simp [unitCube, coordinateBox, Pi.le_def, PiLp.homeomorph, WithLp.equiv]
  aesop

private theorem coordinateBox_compact (a : V3) : IsCompact (coordinateBox a) := by
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-- Every literal unit cube is compact. -/
theorem unitCube_compact (a : V3) : IsCompact (unitCube a) := by
  rw [unitCube_eq_preimage]
  exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr
    (coordinateBox_compact a)

def coordinateOpenBox (a : V3) : Set (Fin 3 → ℝ) :=
  Set.univ.pi fun i => Set.Ioo (a.get i : ℝ) ((a.get i : ℝ) + 1)

theorem coordinateBox_interior (a : V3) :
    interior (coordinateBox a) = coordinateOpenBox a := by
  rw [coordinateBox, interior_pi_set Set.finite_univ]
  simp [coordinateOpenBox]

private theorem coordinateOpenBox_closure (a : V3) :
    closure (coordinateOpenBox a) = coordinateBox a := by
  rw [coordinateOpenBox, closure_pi_set]
  apply Set.pi_congr rfl
  intro i _
  exact closure_Ioo (by norm_num)

private theorem coordinateBox_regularClosed (a : V3) :
    closure (interior (coordinateBox a)) = coordinateBox a := by
  rw [coordinateBox_interior, coordinateOpenBox_closure]

/-- Every literal unit cube is the closure of its interior. -/
theorem unitCube_regularClosed (a : V3) :
    closure (interior (unitCube a)) = unitCube a := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  have hpre : unitCube a = e ⁻¹' coordinateBox a := unitCube_eq_preimage a
  rw [hpre, ← e.preimage_interior, ← e.preimage_closure,
    coordinateBox_regularClosed]

/-- Every literal unit cube has nonempty interior. -/
theorem unitCube_interior_nonempty (a : V3) :
    (interior (unitCube a)).Nonempty := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  have hpre : unitCube a = e ⁻¹' coordinateBox a := unitCube_eq_preimage a
  rw [hpre, ← e.preimage_interior, coordinateBox_interior]
  refine ⟨e.symm (fun i => (a.get i : ℝ) + 1 / 2), ?_⟩
  simp [coordinateOpenBox]
  norm_num [div_eq_mul_inv]

def cubesOf (xs : List V3) : Set E3 :=
  {x | ∃ a ∈ xs, x ∈ unitCube a}

theorem cubesOf_nil : cubesOf [] = (∅ : Set E3) := by
  ext x
  simp [cubesOf]

theorem cubesOf_cons (a : V3) (xs : List V3) :
    cubesOf (a :: xs) = unitCube a ∪ cubesOf xs := by
  ext x
  simp [cubesOf]

private theorem cubesOf_compact (xs : List V3) : IsCompact (cubesOf xs) := by
  induction xs with
  | nil => rw [cubesOf_nil]; exact isCompact_empty
  | cons a xs ih => rw [cubesOf_cons]; exact (unitCube_compact a).union ih

private theorem regularClosed_union {A B : Set E3}
    (hA : closure (interior A) = A) (hB : closure (interior B) = B) :
    closure (interior (A ∪ B)) = A ∪ B := by
  apply Set.Subset.antisymm
  · apply closure_minimal interior_subset
    have hAc : IsClosed A := by rw [← hA]; exact isClosed_closure
    have hBc : IsClosed B := by rw [← hB]; exact isClosed_closure
    exact hAc.union hBc
  · rintro x (hx | hx)
    · rw [← hA] at hx
      exact closure_mono
        (interior_mono (show A ⊆ A ∪ B from subset_union_left)) hx
    · rw [← hB] at hx
      exact closure_mono
        (interior_mono (show B ⊆ A ∪ B from subset_union_right)) hx

private theorem cubesOf_regularClosed (xs : List V3) :
    closure (interior (cubesOf xs)) = cubesOf xs := by
  induction xs with
  | nil => rw [cubesOf_nil]; simp
  | cons a xs ih =>
      rw [cubesOf_cons]
      exact regularClosed_union (unitCube_regularClosed a) ih

/-- The literal seven-cube chair carrier is compact. -/
theorem P_compact : IsCompact P := by
  exact cubesOf_compact chairCells

/-- The literal seven-cube chair carrier is regular closed. -/
theorem P_regularClosed : closure (interior P) = P := by
  exact cubesOf_regularClosed chairCells

/-- The interior of the literal carrier contains the centre of its first cube. -/
theorem P_interior_nonempty : (interior P).Nonempty := by
  apply (unitCube_interior_nonempty (v 0 0 0)).mono
  apply interior_mono
  intro x hx
  refine ⟨v 0 0 0, ?_, hx⟩
  simp [chairCells, bits]
  rfl

/-- The Euclidean centre of the literal unit cell with lower corner `a`. -/
def cellCenter (a : V3) : E3 :=
  WithLp.toLp 2 fun i : Fin 3 => (a.get i : ℝ) + 1 / 2

/-- A literal cell centre lies in the (ordinary Euclidean) interior of its
    closed unit cube. -/
theorem cellCenter_mem_interior_unitCube (a : V3) :
    cellCenter a ∈ interior (unitCube a) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  rw [unitCube_eq_preimage, ← e.preimage_interior, coordinateBox_interior]
  simp [coordinateOpenBox, cellCenter, e, PiLp.homeomorph, WithLp.equiv]
  norm_num

/-- The role record reconstructed from the literal 24-panel table. -/
def nativeFeatureData (r : Role) : Feature :=
  getD nativeFeatures r.val fallbackFeature

/-- The canonical signed coefficient attached to a native feature role. -/
def profileCoefficient (r : Role) : Int := (nativeFeatureData r).coefficient

/-- The exact constants in `PROOFS_registered.md` Section 1.1. -/
def eta : ℝ := 1 / 100

def featureCenter (r : Role) : E3 := scaledV3 8 (nativeFeatureData r).center8

def featureNormal (r : Role) : E3 := scaledV3 1 (nativeFeatureData r).normal

def featureAxis (r : Role) : Nat :=
  featureAxisOf (nativeFeatureData r)

/-- The two native tangent axes, in increasing coordinate order. -/
def featureTangentAxes (r : Role) : Nat × Nat :=
  match featureAxis r with
  | 0 => (1, 2)
  | 1 => (0, 2)
  | _ => (0, 1)

def featureTangent₁ (r : Role) : E3 := coordinateVector (featureTangentAxes r).1
def featureTangent₂ (r : Role) : E3 := coordinateVector (featureTangentAxes r).2

/-- Cyclic square corners `(--),(-+),(++),(+-)`. -/
def featureCorner (r : Role) (k : Fin 4) : E3 :=
  let su : ℝ := if k.val = 0 ∨ k.val = 1 then -1 else 1
  let sv : ℝ := if k.val = 0 ∨ k.val = 3 then -1 else 1
  featureCenter r + (su * eta) • featureTangent₁ r +
    (sv * eta) • featureTangent₂ r

def nextCorner (k : Fin 4) : Fin 4 :=
  ⟨(k.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Apex at signed height `a/10000` in the outward normal direction. -/
def featureApex (r : Role) : E3 :=
  featureCenter r + ((profileCoefficient r : ℝ) / 10000) • featureNormal r

/-- The four closed base edges of a native square tent. -/
def nativeFeatureBaseEdges (r : Role) : Set E3 :=
  ⋃ k : Fin 4, segment ℝ (featureCorner r k) (featureCorner r (nextCorner k))

/-- The four closed apex ridges of a native square tent. -/
def nativeFeatureRidgeEdges (r : Role) : Set E3 :=
  ⋃ k : Fin 4, segment ℝ (featureCorner r k) (featureApex r)

/-- Closed native feature-edge graph: four base edges and four ridges. -/
def nativeFeatureGraph (r : Role) : Set E3 :=
  nativeFeatureBaseEdges r ∪ nativeFeatureRidgeEdges r

/-- The four closed triangular faces of a native square tent. -/
def nativeFeatureSurface (r : Role) : Set E3 :=
  ⋃ k : Fin 4,
    convexHull ℝ ({featureCorner r k, featureCorner r (nextCorner k),
      featureApex r} : Set E3)

/-- Relative interiors of the four square-base edges. -/
def nativeGenericFeatureBaseEdges (r : Role) : Set E3 :=
  ⋃ k : Fin 4, openSegment ℝ (featureCorner r k) (featureCorner r (nextCorner k))

/-- Relative interiors of the four apex ridges. -/
def nativeGenericFeatureRidgeEdges (r : Role) : Set E3 :=
  ⋃ k : Fin 4, openSegment ℝ (featureCorner r k) (featureApex r)

/-- The generic relative-interior edge stratum of a native feature. -/
def nativeGenericFeatureEdge (r : Role) : Set E3 :=
  nativeGenericFeatureBaseEdges r ∪ nativeGenericFeatureRidgeEdges r

def featureRadius (r : Role) (x : E3) : ℝ :=
  max |frameCoordinate (x - featureCenter r) (featureTangentAxes r).1|
      |frameCoordinate (x - featureCenter r) (featureTangentAxes r).2|

def featureNormalCoordinate (r : Role) (x : E3) : ℝ :=
  ((nativeFeatureData r).normal.get (featureAxis r) : ℝ) *
    frameCoordinate (x - featureCenter r) (featureAxis r)

def featureTubeSupport (r : Role) (x : E3) : Prop :=
  featureRadius r x ≤ eta ∧ |featureNormalCoordinate r x| ≤ eta

set_option maxRecDepth 100000 in
private theorem nativeFeatureData_eq_get (r : Role) :
    nativeFeatureData r = nativeFeatures[r.val] := by
  have hrlt : r.val < nativeFeatures.length := by
    rw [native_features_length]
    exact r.isLt
  simp [nativeFeatureData, R44.getD, hrlt]

set_option maxRecDepth 100000 in
private theorem nativeFeatureCenters_ne {r s : Role} (hrs : r ≠ s) :
    (nativeFeatureData r).center8 ≠ (nativeFeatureData s).center8 := by
  intro heq
  have hrlt : r.val < nativeFeatures.length := by
    rw [native_features_length]
    exact r.isLt
  have hslt : s.val < nativeFeatures.length := by
    rw [native_features_length]
    exact s.isLt
  have hget : (nativeFeatures.map Feature.center8).get
      ⟨r.val, by simpa using hrlt⟩ =
      (nativeFeatures.map Feature.center8).get ⟨s.val, by simpa using hslt⟩ := by
    rw [nativeFeatureData_eq_get r, nativeFeatureData_eq_get s] at heq
    simpa using heq
  have hindex := native_feature_centers_nodup.injective_get hget
  apply hrs
  apply Fin.ext
  exact congrArg Fin.val hindex

private theorem nativeFeatureCenters_separated {r s : Role} (hrs : r ≠ s) :
    ∃ i : Fin 3,
      |(nativeFeatureData r).center8.get i -
        (nativeFeatureData s).center8.get i| ≥ 1 := by
  have hne := nativeFeatureCenters_ne hrs
  rcases hrc : (nativeFeatureData r).center8 with ⟨rx, ry, rz⟩
  rcases hsc : (nativeFeatureData s).center8 with ⟨sx, sy, sz⟩
  by_cases hx : rx = sx
  · by_cases hy : ry = sy
    · have hz : rz ≠ sz := by
        intro hz
        apply hne
        rw [hrc, hsc, hx, hy, hz]
      refine ⟨2, ?_⟩
      change |rz - sz| ≥ 1
      have hp : 0 < |rz - sz| := abs_pos.mpr (sub_ne_zero.mpr hz)
      omega
    · refine ⟨1, ?_⟩
      change |ry - sy| ≥ 1
      have hp : 0 < |ry - sy| := abs_pos.mpr (sub_ne_zero.mpr hy)
      omega
  · refine ⟨0, ?_⟩
    change |rx - sx| ≥ 1
    have hp : 0 < |rx - sx| := abs_pos.mpr (sub_ne_zero.mpr hx)
    omega

private theorem nativeFeature_normal_axis (r : Role) :
    |(nativeFeatureData r).normal.get (featureAxis r)| = 1 := by
  have hrlt : r.val < nativeFeatures.length := by
    rw [native_features_length]
    exact r.isLt
  have h := native_feature_normal_axis ⟨r.val, hrlt⟩
  have hrdata : nativeFeatureData r = nativeFeatures.get ⟨r.val, hrlt⟩ := by
    exact nativeFeatureData_eq_get r
  change (nativeFeatures.get ⟨r.val, hrlt⟩).normal.get
      (featureAxisOf (nativeFeatures.get ⟨r.val, hrlt⟩)) = 1 ∨
    (nativeFeatures.get ⟨r.val, hrlt⟩).normal.get
      (featureAxisOf (nativeFeatures.get ⟨r.val, hrlt⟩)) = -1 at h
  rw [← hrdata] at h
  change (nativeFeatureData r).normal.get (featureAxis r) = 1 ∨
    (nativeFeatureData r).normal.get (featureAxis r) = -1 at h
  rcases h with h | h <;> simp [h]

/-- Every point of a literal normal tube is within `eta` of its centre in
    each ambient coordinate. -/
theorem featureTubeSupport_coordinate_bound {r : Role} {x : E3}
    (hx : featureTubeSupport r x) :
    ∀ i : Fin 3, |x i - featureCenter r i| ≤ eta := by
  rcases hx with ⟨hrad, hnormal⟩
  have ht1 :
      |frameCoordinate (x - featureCenter r) (featureTangentAxes r).1| ≤ eta :=
    (le_max_left _ _).trans hrad
  have ht2 :
      |frameCoordinate (x - featureCenter r) (featureTangentAxes r).2| ≤ eta :=
    (le_max_right _ _).trans hrad
  have hnormalAxis :
      |frameCoordinate (x - featureCenter r) (featureAxis r)| ≤ eta := by
    have hcast : |((nativeFeatureData r).normal.get (featureAxis r) : ℝ)| = 1 := by
      exact_mod_cast nativeFeature_normal_axis r
    rw [featureNormalCoordinate, abs_mul, hcast, one_mul] at hnormal
    exact hnormal
  have haxis : featureAxis r = 0 ∨ featureAxis r = 1 ∨ featureAxis r = 2 := by
    unfold featureAxis featureAxisOf
    split
    · simp
    · split <;> simp
  rcases haxis with h0 | h1 | h2
  · intro i
    fin_cases i
    · simpa [frameCoordinate, h0] using hnormalAxis
    · simpa [frameCoordinate, featureTangentAxes, h0] using ht1
    · simpa [frameCoordinate, featureTangentAxes, h0] using ht2
  · intro i
    fin_cases i
    · simpa [frameCoordinate, featureTangentAxes, h1] using ht1
    · simpa [frameCoordinate, h1] using hnormalAxis
    · simpa [frameCoordinate, featureTangentAxes, h1] using ht2
  · intro i
    fin_cases i
    · simpa [frameCoordinate, featureTangentAxes, h2] using ht1
    · simpa [frameCoordinate, featureTangentAxes, h2] using ht2
    · simpa [frameCoordinate, h2] using hnormalAxis

private theorem featureCenters_separated_real {r s : Role} (hrs : r ≠ s) :
    ∃ i : Fin 3, 2 * eta < |featureCenter r i - featureCenter s i| := by
  obtain ⟨i, hi⟩ := nativeFeatureCenters_separated hrs
  refine ⟨i, ?_⟩
  have hi' : (1 : ℝ) ≤
      |((nativeFeatureData r).center8.get i : ℝ) -
        ((nativeFeatureData s).center8.get i : ℝ)| := by
    exact_mod_cast hi
  have hscale : |featureCenter r i - featureCenter s i| =
      |((nativeFeatureData r).center8.get i : ℝ) -
        ((nativeFeatureData s).center8.get i : ℝ)| / 8 := by
    change |((nativeFeatureData r).center8.get i : ℝ) / 8 -
        ((nativeFeatureData s).center8.get i : ℝ) / 8| = _
    rw [show ((nativeFeatureData r).center8.get i : ℝ) / 8 -
        ((nativeFeatureData s).center8.get i : ℝ) / 8 =
        (((nativeFeatureData r).center8.get i : ℝ) -
          ((nativeFeatureData s).center8.get i : ℝ)) / 8 by ring]
    rw [abs_div]
    norm_num
  rw [hscale]
  unfold eta
  linarith

/-- Pairwise disjointness statement for the 192 closed normal supports. -/
def FeatureTubeSupportsPairwiseDisjoint : Prop :=
  ∀ (r s : Role), r ≠ s →
    Disjoint {x : E3 | featureTubeSupport r x}
      {x : E3 | featureTubeSupport s x}

/-- The 192 closed normal-tube supports are pairwise disjoint.  The finite
    input is the kernel-checked distinctness of the literal eighth-grid
    centres; the geometric margin is `2/100 < 1/8`. -/
theorem featureTubeSupports_pairwiseDisjoint :
    FeatureTubeSupportsPairwiseDisjoint := by
  intro r s hrs
  rw [Set.disjoint_left]
  intro x hxr hxs
  obtain ⟨i, hsep⟩ := featureCenters_separated_real hrs
  have hr := featureTubeSupport_coordinate_bound hxr i
  have hs := featureTubeSupport_coordinate_bound hxs i
  have hle : |featureCenter r i - featureCenter s i| ≤ eta + eta := by
    calc
      |featureCenter r i - featureCenter s i| =
          |(x i - featureCenter s i) - (x i - featureCenter r i)| := by ring_nf
      _ ≤ |x i - featureCenter s i| + |x i - featureCenter r i| := abs_sub _ _
      _ ≤ eta + eta := add_le_add hs hr
  linarith

/-- Signed square-tent graph `h max(0,1-||u||∞/eta)`. -/
def featureHeight (r : Role) (x : E3) : ℝ :=
  ((profileCoefficient r : ℝ) / 10000) * max 0 (1 - featureRadius r x / eta)

/-- The collar cutoff `χ(z)=max(0,1-|z|/ρ)` of A§1, with `ρ=eta`. -/
def tubeCutoff (z : ℝ) : ℝ := max 0 (1 - |z| / eta)

/-- The ambient formula `(u,z) ↦ (u,z+χ(z)f(u))` for one literal
    normal tube, written in native coordinates. -/
def featureTubeMap (r : Role) (x : E3) : E3 :=
  x + (tubeCutoff (featureNormalCoordinate r x) * featureHeight r x) •
    featureNormal r

/-- The four sides and two normal faces of a closed feature tube. -/
def featureTubeBoundary (r : Role) (x : E3) : Prop :=
  featureRadius r x = eta ∨ |featureNormalCoordinate r x| = eta

/-- Boundary-compatibility statement for all 192 explicit tube maps. -/
def FeatureTubeMapsFixBoundary : Prop :=
  ∀ (r : Role) (x : E3),
    featureTubeBoundary r x → featureTubeMap r x = x

/-- Each literal tube formula is the identity on its boundary, the gluing
    compatibility asserted in A§1. -/
theorem featureTubeMap_fixed_on_boundary : FeatureTubeMapsFixBoundary := by
  intro r x hx
  rcases hx with hradius | hnormal
  · simp [featureTubeMap, featureHeight, hradius, eta]
  · simp [featureTubeMap, tubeCutoff, hnormal, eta]

/-- The concrete R44 solid: the seven-cube carrier with, on every exposed
    panel, the square under the signed tent graph replacing its planar patch.
    All centers, normals, and coefficients come from `Generated.panels` via
    the phase-1 `nativeFeatures` construction. -/
def Q : Set E3 :=
  {x |
    (x ∈ P ∧ ∀ r : Role, profileCoefficient r < 0 → featureTubeSupport r x →
      featureNormalCoordinate r x ≤ featureHeight r x) ∨
    ∃ r : Role, 0 < profileCoefficient r ∧ featureTubeSupport r x ∧
      0 ≤ featureNormalCoordinate r x ∧
      featureNormalCoordinate r x ≤ featureHeight r x}

/-- A packing is a family of isometric placements of `Q` with pairwise
    disjoint interiors. -/
structure Packing (Q : Set E3) where
  placements : Set RigidMotion
  disjoint_interiors :
    ∀ ⦃g h : RigidMotion⦄, g ∈ placements → h ∈ placements → g ≠ h →
      Disjoint (interior (g '' Q)) (interior (h '' Q))

/-- A tiling of `E3` by isometric copies of the closed set `Q`: interiors are
    pairwise disjoint and the copies cover every point. -/
structure Tiling (Q : Set E3) extends Packing Q where
  covers : ∀ x : E3, ∃ g : RigidMotion, g ∈ placements ∧ x ∈ g '' Q

/-- Translation by `v`, as an element of Mathlib's affine-isometry group. -/
def translation (v : E3) : RigidMotion :=
  AffineIsometryEquiv.constVAdd ℝ E3 v

@[ext] theorem Packing.ext {S : Set E3} {A B : Packing S}
    (h : A.placements = B.placements) : A = B := by
  cases A
  cases B
  cases h
  rfl

@[ext] theorem Tiling.ext {S : Set E3} {T U : Tiling S}
    (h : T.placements = U.placements) : T = U := by
  rcases T with ⟨A, hA⟩
  rcases U with ⟨B, hB⟩
  have hp : A = B := Packing.ext h
  cases hp
  rfl

theorem mul_image (S : Set E3) (a g : RigidMotion) :
    (a * g) '' S = a '' (g '' S) := by
  ext x
  simp only [Set.mem_image, AffineIsometryEquiv.coe_mul, Function.comp_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨g z, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- Translate every placed copy by `v`.  This is the tiling action denoted
    `T + v` in `PROOFS_registered.md` Section 8. -/
def translateTiling {S : Set E3} (v : E3) (T : Tiling S) : Tiling S where
  placements := translation v • T.placements
  disjoint_interiors := by
    intro g h hg hh hne
    rw [Set.mem_smul_set] at hg hh
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    obtain ⟨h₀, hh₀, rfl⟩ := hh
    have hne₀ : g₀ ≠ h₀ := by
      intro heq
      apply hne
      rw [heq]
    have hd := T.disjoint_interiors hg₀ hh₀ hne₀
    change Disjoint (interior ((translation v * g₀) '' S))
      (interior ((translation v * h₀) '' S))
    rw [mul_image, mul_image]
    have hig : interior ((translation v) '' (g₀ '' S)) =
        (translation v) '' interior (g₀ '' S) :=
      ((translation v).toHomeomorph.image_interior (g₀ '' S)).symm
    have hih : interior ((translation v) '' (h₀ '' S)) =
        (translation v) '' interior (h₀ '' S) :=
      ((translation v).toHomeomorph.image_interior (h₀ '' S)).symm
    rw [hig, hih]
    exact Set.disjoint_image_of_injective (translation v).injective hd
  covers := by
    intro x
    obtain ⟨g, hg, z, hz, heq⟩ := T.covers ((translation v)⁻¹ x)
    refine ⟨translation v * g, Set.mem_smul_set.mpr ⟨g, hg, rfl⟩,
      z, hz, ?_⟩
    simp only [AffineIsometryEquiv.coe_mul, Function.comp_apply]
    rw [heq]
    have ht : translation v * (translation v)⁻¹ = (1 : RigidMotion) := by group
    exact congrArg (fun k : RigidMotion => k x) ht

noncomputable instance {S : Set E3} : VAdd E3 (Tiling S) where
  vadd := translateTiling

/-- Document-order notation: `T + v` is the translated tiling. -/
noncomputable instance {S : Set E3} : HAdd (Tiling S) E3 (Tiling S) where
  hAdd T v := translateTiling v T

@[simp] theorem translation_zero : translation 0 = (1 : RigidMotion) := by
  apply AffineIsometryEquiv.ext
  intro x
  simp [translation]

/-- The unlabelled family of closed tile subsets represented by a tiling. -/
def tileFamily {S : Set E3} (T : Tiling S) : Set (Set E3) :=
  {A | ∃ g : RigidMotion, g ∈ T.placements ∧ A = g '' S}

/-- The full geometric symmetry group of a tiling: ambient isometries which
    permute its unlabelled family of closed tile subsets. -/
def Sym {S : Set E3} (T : Tiling S) : Subgroup RigidMotion :=
  MulAction.stabilizer RigidMotion (tileFamily T)

/-- Translation periods of a tiling. -/
def Per {S : Set E3} (T : Tiling S) : Set E3 :=
  {v | translation v ∈ Sym T}

/-- A Euclidean vector whose coordinates are integral in some orthonormal
    coordinate frame.  This is the ambient-frame invariant form of membership
    in `ℤ³` used after registration. -/
def GridVector (v : E3) : Prop :=
  ∃ A : E3 ≃ₗᵢ[ℝ] E3, ∀ i : Fin 3, ∃ z : ℤ, (A v) i = (z : ℝ)

def frameActReal (f : Frame) (x : E3) (i : Fin 3) : ℝ :=
  (f.sign.get i : ℝ) * frameCoordinate x (f.perm.get i)

/-- A normalized affine isometry is represented by one of the 24 phase-1
    proper cubic frames and an integer translation. -/
structure RegisteredPose (g : RigidMotion) where
  frameIndex : Fin 24
  shift : V3
  linear_eq : ∀ x i,
    (g.linearIsometryEquiv x) i =
      frameActReal (getD orientationGroup frameIndex identityFrame) x i
  origin_eq : ∀ i, (g (0 : E3)) i = (shift.get i : ℝ)

/-- `Q` has no nonidentity affine self-isometry. -/
def NativeAsymmetric (Q : Set E3) : Prop :=
  ∀ g : RigidMotion, g '' Q = Q → g = 1

theorem rigid_smul_image (S : Set E3) (a g : RigidMotion) :
    a • (g '' S) = (a * g) '' S := by
  ext x
  simp only [Set.mem_smul_set, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨g z, ⟨z, hz, rfl⟩, rfl⟩

private theorem placement_eq_of_same_tile {S : Set E3}
    (hnative : NativeAsymmetric S) (g h : RigidMotion)
    (heq : g '' S = h '' S) : g = h := by
  have hself : (g⁻¹ * h) '' S = S := by
    rw [← rigid_smul_image]
    rw [← heq, rigid_smul_image]
    simp
  have hone := hnative (g⁻¹ * h) hself
  apply_fun fun k : RigidMotion => g * k at hone
  have hhg : h = g := by simpa [mul_assoc] using hone
  exact hhg.symm

theorem symmetry_sends_placement {S : Set E3} (T : Tiling S)
    (hnative : NativeAsymmetric S) (a : Sym T) (g : RigidMotion)
    (hg : g ∈ T.placements) : a.1 * g ∈ T.placements := by
  have hstab : a.1 • tileFamily T = tileFamily T :=
    MulAction.mem_stabilizer_iff.mp a.2
  have htile : g '' S ∈ tileFamily T := ⟨g, hg, rfl⟩
  have himage : a.1 • (g '' S) ∈ a.1 • tileFamily T :=
    Set.mem_smul_set.mpr ⟨g '' S, htile, rfl⟩
  rw [hstab] at himage
  obtain ⟨h, hh, heq⟩ := himage
  have heq' : h '' S = (a.1 * g) '' S := by
    rw [← rigid_smul_image]
    exact heq.symm
  rwa [← placement_eq_of_same_tile hnative h (a.1 * g) heq']

/-- Data witnessing that all placements are integer/proper-cubic after one
    ambient isometry.  Period integrality and the 24-frame symmetry code are
    derived below from these poses, rather than included in the definition. -/
structure Registration {S : Set E3} (T : Tiling S) where
  ambient : RigidMotion
  pose : ∀ g : RigidMotion, g ∈ T.placements → RegisteredPose (ambient * g)

theorem period_grid_from_registered_poses {S : Set E3} (T : Tiling S)
    (R : Registration T) (hnative : NativeAsymmetric S) ⦃v : E3⦄
    (hv : v ∈ Per T) : GridVector v := by
  obtain ⟨g, hg, _⟩ := T.covers (0 : E3)
  have hvg : translation v * g ∈ T.placements := by
    exact symmetry_sends_placement T hnative ⟨translation v, hv⟩ g hg
  let rg := R.pose g hg
  let rvg := R.pose (translation v * g) hvg
  refine ⟨R.ambient.linearIsometryEquiv, ?_⟩
  intro i
  refine ⟨rvg.shift.get i - rg.shift.get i, ?_⟩
  have hmap := congrArg (fun x : E3 => x i) (R.ambient.map_vadd (g 0) v)
  have horigin :
      (R.ambient.linearIsometryEquiv v) i + (R.ambient (g 0)) i =
        (R.ambient (v + g 0)) i := by
    simpa [vadd_eq_add, add_comm] using hmap.symm
  have hleft := rg.origin_eq i
  have hright := rvg.origin_eq i
  simp only [AffineIsometryEquiv.coe_mul, Function.comp_apply] at hleft hright
  have hright' : (R.ambient (v + g 0)) i = (rvg.shift.get i : ℝ) := by
    simpa [translation] using hright
  rw [hleft, hright'] at horigin
  rw [Int.cast_sub]
  exact eq_sub_iff_add_eq.mpr horigin

private theorem affine_eq_translation_mul_of_linear_eq (a b : RigidMotion)
    (h : a.linearIsometryEquiv = b.linearIsometryEquiv) :
    a = translation (a 0 - b 0) * b := by
  apply AffineIsometryEquiv.ext
  intro x
  have ha := a.map_vadd (0 : E3) x
  have hb := b.map_vadd (0 : E3) x
  simp only [vadd_eq_add, add_zero] at ha hb
  simp [AffineIsometryEquiv.coe_mul, translation, ha, hb, h]
  ac_rfl

theorem symmetry_code_from_registered_poses {S : Set E3} (T : Tiling S)
    (R : Registration T) (hnative : NativeAsymmetric S) :
    ∃ code : Sym T → Fin 24,
      ∀ a b, code a = code b →
        ∃ v ∈ Per T, a.1 = translation v * b.1 := by
  obtain ⟨g, hg, _⟩ := T.covers (0 : E3)
  have hmem (a : Sym T) : a.1 * g ∈ T.placements := by
    exact symmetry_sends_placement T hnative a g hg
  let ra (a : Sym T) : RegisteredPose (R.ambient * (a.1 * g)) :=
    R.pose (a.1 * g) (hmem a)
  let code (a : Sym T) : Fin 24 := (ra a).frameIndex
  refine ⟨code, ?_⟩
  intro a b hab
  change (ra a).frameIndex = (ra b).frameIndex at hab
  have hcomp :
      (R.ambient * (a.1 * g)).linearIsometryEquiv =
        (R.ambient * (b.1 * g)).linearIsometryEquiv := by
    apply LinearIsometryEquiv.ext
    intro x
    ext i
    rw [(ra a).linear_eq x i, (ra b).linear_eq x i, hab]
  change R.ambient.linearIsometryEquiv *
      (a.1.linearIsometryEquiv * g.linearIsometryEquiv) =
    R.ambient.linearIsometryEquiv *
      (b.1.linearIsometryEquiv * g.linearIsometryEquiv) at hcomp
  have hcanceled := congrArg
    (fun L : E3 ≃ₗᵢ[ℝ] E3 =>
      R.ambient.linearIsometryEquiv⁻¹ * L * g.linearIsometryEquiv⁻¹) hcomp
  have hlinear : a.1.linearIsometryEquiv = b.1.linearIsometryEquiv := by
    simpa [mul_assoc] using hcanceled
  let v : E3 := a.1 0 - b.1 0
  have heq : a.1 = translation v * b.1 :=
    affine_eq_translation_mul_of_linear_eq a.1 b.1 hlinear
  refine ⟨v, ?_, heq⟩
  have habmem : a.1 * b.1⁻¹ ∈ Sym T :=
    (Sym T).mul_mem a.2 ((Sym T).inv_mem b.2)
  have htrans : translation v = a.1 * b.1⁻¹ := by
    rw [heq]
    group
  change translation v ∈ Sym T
  rw [htrans]
  exact habmem

def Registered {S : Set E3} (T : Tiling S) : Prop := Nonempty (Registration T)

def featureGraphAt (g : RigidMotion) (r : Role) : Set E3 :=
  g '' nativeFeatureGraph r

def featureSurfaceAt (g : RigidMotion) (r : Role) : Set E3 :=
  g '' nativeFeatureSurface r

def genericFeatureEdgeAt (g : RigidMotion) (r : Role) : Set E3 :=
  g '' nativeGenericFeatureEdge r

inductive FeatureEdgeKind where
  | base
  | ridge
deriving DecidableEq

def nativeFeatureEdgesOfKind (r : Role) : FeatureEdgeKind → Set E3
  | .base => nativeFeatureBaseEdges r
  | .ridge => nativeFeatureRidgeEdges r

def nativeGenericEdgesOfKind (r : Role) : FeatureEdgeKind → Set E3
  | .base => nativeGenericFeatureBaseEdges r
  | .ridge => nativeGenericFeatureRidgeEdges r

def featureEdgesOfKindAt (g : RigidMotion) (r : Role)
    (kind : FeatureEdgeKind) : Set E3 :=
  g '' nativeFeatureEdgesOfKind r kind

def genericEdgesOfKindAt (g : RigidMotion) (r : Role)
    (kind : FeatureEdgeKind) : Set E3 :=
  g '' nativeGenericEdgesOfKind r kind

/-- A whole feature graph of `g` is contained in a feature graph of `h`. -/
def FeatureContained (g : RigidMotion) (r : Role) (h : RigidMotion) : Prop :=
  ∃ s : Role, featureGraphAt g r ⊆ featureGraphAt h s

/-- Two complete features have equal graphs and surfaces and opposite profile
    coefficients. -/
def CompleteFeatureMate (g : RigidMotion) (r : Role)
    (h : RigidMotion) (s : Role) : Prop :=
  featureGraphAt g r = featureGraphAt h s ∧
  featureSurfaceAt g r = featureSurfaceAt h s ∧
  profileCoefficient r = -profileCoefficient s

/-- A feature with nonzero signed height cannot be its own opposite-polarity
    mate.  This semantic regression guards the diagonal of the companion
    interface independently of the later continuous hypotheses; its proof is
    kernel arithmetic over the definition of `CompleteFeatureMate`. -/
theorem no_self_mate (g : RigidMotion) (r : Role)
    (hne : profileCoefficient r ≠ 0) :
    ¬ CompleteFeatureMate g r g r := by
  intro hm
  have heq : profileCoefficient r = -profileCoefficient r := hm.2.2
  omega

def relativeMotion (g h : RigidMotion) : RigidMotion := g⁻¹ * h

/-- An affine motion realizes a literal phase-1 pose in coordinates. -/
def RealizesPose (g : RigidMotion) (p : Pose) : Prop :=
  (∀ x i, (g.linearIsometryEquiv x) i = frameActReal p.frame x i) ∧
  (∀ i, (g (0 : E3)) i = (p.shift.get i : ℝ))

/-- A literal pose determines at most one affine isometry. -/
theorem realizesPose_unique {g h : RigidMotion} {p : Pose}
    (hg : RealizesPose g p) (hh : RealizesPose h p) : g = h := by
  apply AffineIsometryEquiv.ext
  intro x
  apply PiLp.ext
  intro i
  have hgx := congrArg (fun y : E3 => y i) (g.map_vadd (0 : E3) x)
  have hhx := congrArg (fun y : E3 => y i) (h.map_vadd (0 : E3) x)
  simp only [vadd_eq_add, add_zero] at hgx hhx
  rw [hgx, hhx]
  change (g.linearIsometryEquiv x) i + (g 0) i =
    (h.linearIsometryEquiv x) i + (h 0) i
  rw [hg.1 x i, hh.1 x i, hg.2 i, hh.2 i]

/-- First geometric sub-lemma of the planar-area argument in R§6: the nine
    coordinate-plane boundary regions of area greater than `9/10`, separated
    from the non-axis facets of total area below `1/4`, recover the bare
    seven-cube carrier. -/
def PlanarAreaCarrierRecovery : Prop :=
  ∀ g : RigidMotion, g '' Q = Q → g '' P = P

/-- Remainder after carrier recovery: a self-isometry which preserves both
    `Q` and its recovered carrier fixes the native origin, is a signed cubic
    frame, and its action on the concrete feature data preserves the literal
    192-row table. -/
def CarrierFeatureFrameReduction : Prop :=
  ∀ g : RigidMotion, g '' Q = Q → g '' P = P →
    ∃ f : Frame,
      (allFrames.filter preservesFeatureTableFrame).contains f = true ∧
        RealizesPose g (po f (v 0 0 0))

/-- The assembled geometric content of the planar-area reduction in R§6. -/
def PlanarAreaNativeReduction : Prop :=
  ∀ g : RigidMotion, g '' Q = Q →
    ∃ f : Frame,
      (allFrames.filter preservesFeatureTableFrame).contains f = true ∧
        RealizesPose g (po f (v 0 0 0))

/-- Carrier recovery followed by the native frame/feature readout gives the
    endpoint consumed by the finite 48-frame comparison. -/
theorem planar_area_native_reduction
    (hcarrier : PlanarAreaCarrierRecovery)
    (hframe : CarrierFeatureFrameReduction) : PlanarAreaNativeReduction := by
  intro g hg
  exact hframe g hg (hcarrier g hg)

theorem frame_eq_of_beq {a b : Frame} (h : (a == b) = true) : a = b := by
  rcases a with ⟨⟨ax, ay, az⟩, ⟨sx, sy, sz⟩⟩
  rcases b with ⟨⟨bx, by', bz⟩, ⟨tx, ty, tz⟩⟩
  unfold instBEqFrame instBEqFrame.beq at h
  unfold instBEqN3 instBEqN3.beq instBEqV3 instBEqV3.beq at h
  simp at h
  simp_all

private theorem frame_list_eq_of_beq {as bs : List Frame}
    (h : (as == bs) = true) : as = bs := by
  induction as generalizing bs with
  | nil =>
      cases bs <;> simp_all
  | cons a as ih =>
      cases bs with
      | nil => simp_all
      | cons b bs =>
          change ((a == b) && (as == bs)) = true at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨hab, htail⟩ := h
          rw [frame_eq_of_beq hab, ih htail]

private theorem realized_identity_frame_is_identity {g : RigidMotion}
    (hg : RealizesPose g (po identityFrame (v 0 0 0))) : g = 1 := by
  have hg0 : g (0 : E3) = 0 := by
    apply PiLp.ext
    intro i
    have hi := hg.2 i
    fin_cases i <;> simpa [po, v, V3.get] using hi
  have hlinear : ∀ x : E3, g.linearIsometryEquiv x = x := by
    intro x
    apply PiLp.ext
    intro i
    have hi := hg.1 x i
    fin_cases i <;>
      simpa [po, identityFrame, fr, n3, v, V3.get, N3.get,
        frameActReal, frameCoordinate] using hi
  apply AffineIsometryEquiv.ext
  intro x
  have hmap := g.map_vadd (0 : E3) x
  simpa [vadd_eq_add, hg0, hlinear] using hmap

/-- The 48-frame phase-1 comparison completes native asymmetry once the
    planar-area reconstruction has reduced an arbitrary self-isometry to a
    feature-table-preserving signed frame. -/
theorem native_asymmetry_reduction (hplanar : PlanarAreaNativeReduction)
    (hfinite : noNativeSymmetryCheck = true) : NativeAsymmetric Q := by
  have hfilter : allFrames.filter preservesFeatureTableFrame = [identityFrame] := by
    unfold noNativeSymmetryCheck at hfinite
    simp only [Bool.and_eq_true] at hfinite
    exact frame_list_eq_of_beq hfinite.2
  intro g hg
  obtain ⟨f, hf, hreal⟩ := hplanar g hg
  rw [hfilter] at hf
  have hfid : f = identityFrame := by
    simp only [List.contains_cons, List.contains_nil, Bool.or_false] at hf
    exact frame_eq_of_beq hf
  subst f
  exact realized_identity_frame_is_identity hreal

def EighthGridMotion (g : RigidMotion) : Prop :=
  ∃ f ∈ allFrames, (∀ x i, (g.linearIsometryEquiv x) i = frameActReal f x i) ∧
    ∀ i, ∃ z : ℤ, (g (0 : E3)) i = (z : ℝ) / 8

/-- A motion realizes a literal eighth-grid pose. -/
def RealizesEighthPose (g : RigidMotion) (p : Pose) : Prop :=
  (∀ x i, (g.linearIsometryEquiv x) i = frameActReal p.frame x i) ∧
  ∀ i, (g (0 : E3)) i = (p.shift.get i : ℝ) / 8

/-- The exact center, normal, and polarity equations of Corollary 4.4. -/
def FeatureMateFormula (m : RigidMotion) (u v : Role) : Prop :=
  EighthGridMotion m ∧ profileCoefficient u = -profileCoefficient v ∧
  featureNormal u = -(m.linearIsometryEquiv (featureNormal v)) ∧
  m 0 = featureCenter u - m.linearIsometryEquiv (featureCenter v)

/-- Membership in the literal 6,862-pose complete-feature census. -/
def CensusMatePose (m : RigidMotion) : Prop :=
  ∃ p ∈ matePoses, RealizesEighthPose m p

def AtlasRelated (g h : RigidMotion) : Prop :=
  ∃ p ∈ legalContacts, RealizesPose (relativeMotion g h) p

/-- `Q` is compact, regular closed, has nonempty interior, and is the image of
    the literal seven-cube carrier under the disjoint tube homeomorphism. -/
def CompactRegularClosedBall (Q : Set E3) : Prop :=
  IsCompact Q ∧ closure (interior Q) = Q ∧
    (interior Q).Nonempty ∧ ∃ F : E3 ≃ₜ E3, F '' P = Q

/-- A global map agrees with every local tube formula, and is the identity
    away from the union of the 192 closed supports.  Pairwise disjointness
    makes the first clause unambiguous. -/
def AgreesWithFeatureTubeMaps (F : E3 → E3) : Prop :=
  (∀ (r : Role) (x : E3), featureTubeSupport r x → F x = featureTubeMap r x) ∧
  (∀ x : E3, (∀ r : Role, ¬ featureTubeSupport r x) → F x = x)

/-- First remaining analytic sub-lemma of the Object construction: on every
    tube the explicit fibre map is an ambient homeomorphism.  Its boundary
    identity is already the theorem `featureTubeMap_fixed_on_boundary`. -/
def PerTubeHomeomorphisms : Prop :=
  ∀ r : Role, ∃ F : E3 ≃ₜ E3, ∀ x : E3, F x = featureTubeMap r x

/-- Second remaining Object sub-lemma: the finitely many local
    homeomorphisms, whose supports are pairwise disjoint and whose boundary
    values are the identity, glue to one ambient homeomorphism. -/
def FeatureTubeMapsGlue : Prop :=
  FeatureTubeSupportsPairwiseDisjoint → FeatureTubeMapsFixBoundary →
    PerTubeHomeomorphisms →
    ∃ F : E3 ≃ₜ E3, AgreesWithFeatureTubeMaps F

/-- Final remaining Object sub-lemma: the glued explicit formula takes the
    planar carrier interface to the signed square tents, hence carries `P`
    exactly onto the concrete set `Q`. -/
def FeatureTubeMapCarriesCarrier : Prop :=
  ∀ F : E3 ≃ₜ E3, AgreesWithFeatureTubeMaps F → F '' P = Q

/-- The Object endpoint used by the spine. -/
def HasTubeHomeomorphism : Prop :=
  ∃ F : E3 ≃ₜ E3, F '' P = Q

/-- Assemble the three exact residual tube-map sub-lemmas. -/
theorem hasTubeHomeomorphism_of_tube_construction
    (hlocal : PerTubeHomeomorphisms)
    (hglue : FeatureTubeMapsGlue)
    (himage : FeatureTubeMapCarriesCarrier) : HasTubeHomeomorphism := by
  obtain ⟨F, hF⟩ := hglue featureTubeSupports_pairwiseDisjoint
    featureTubeMap_fixed_on_boundary hlocal
  exact ⟨F, himage F hF⟩

/-- The ambient tube homeomorphism restricts to the subspace homeomorphism
    requested in the Object statement. -/
theorem P_homeomorphic_Q_of_tube_homeomorphism
    (h : HasTubeHomeomorphism) : Nonempty (P ≃ₜ Q) := by
  obtain ⟨F, hF⟩ := h
  refine ⟨F.subtype ?_⟩
  intro x
  constructor
  · intro hx
    rw [← hF]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hF] at hx
    obtain ⟨y, hy, heq⟩ := hx
    exact F.injective heq ▸ hy

/-- Compactness of `Q` is a theorem once the documented ambient tube map is
    supplied; compactness of `P` is proved above from the literal cubes. -/
theorem Q_compact_of_tube_homeomorphism (h : HasTubeHomeomorphism) : IsCompact Q := by
  obtain ⟨F, hF⟩ := h
  rw [← hF]
  exact P_compact.image F.continuous

/-- Regular closure is transported from the proved carrier fact by the
    documented ambient tube homeomorphism. -/
theorem Q_regularClosed_of_tube_homeomorphism (h : HasTubeHomeomorphism) :
    closure (interior Q) = Q := by
  obtain ⟨F, hF⟩ := h
  rw [← hF, ← F.image_interior, ← F.image_closure, P_regularClosed]

/-- Nonempty interior is transported from the first literal carrier cube. -/
theorem Q_interior_nonempty_of_tube_homeomorphism (h : HasTubeHomeomorphism) :
    (interior Q).Nonempty := by
  obtain ⟨F, hF⟩ := h
  rw [← hF, ← F.image_interior]
  exact P_interior_nonempty.image F

/-- The Object conclusion reconstructed from the sole remaining normal-tube
    gluing sub-hypothesis. -/
theorem compactRegularClosedBall_of_tube_homeomorphism
    (h : HasTubeHomeomorphism) : CompactRegularClosedBall Q := by
  exact ⟨Q_compact_of_tube_homeomorphism h,
    Q_regularClosed_of_tube_homeomorphism h,
    Q_interior_nonempty_of_tube_homeomorphism h, h⟩

/-- Every packing by congruent copies of `Q` is locally finite. -/
def EveryPackingLocallyFinite (Q : Set E3) : Prop :=
  ∀ (S : Packing Q) (K : Set E3), IsCompact K →
    {g | g ∈ S.placements ∧ (g '' Q ∩ K).Nonempty}.Finite

private theorem finite_of_subset_compact_of_pairwise_dist
    {A C : Set E3} {r : ℝ} (hC : IsCompact C) (hr : 0 < r)
    (hAC : A ⊆ C)
    (hsep : ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → dist x y < r → x = y) :
    A.Finite := by
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hC.totallyBounded
    (r / 2) (half_pos hr)
  have hpick : ∀ x : A, ∃ y ∈ t, (x : E3) ∈ Metric.ball y (r / 2) := by
    intro x
    have hx := hcover (hAC x.property)
    simpa only [Set.mem_iUnion, exists_prop] using hx
  choose pick hpick_mem hpick_ball using hpick
  letI : Fintype t := ht.fintype
  let pickT : A → t := fun x => ⟨pick x, hpick_mem x⟩
  have hinj : Function.Injective pickT := by
    intro x y hxy
    apply Subtype.ext
    apply hsep x.property y.property
    have hpick_eq : pick x = pick y := congrArg Subtype.val hxy
    have hx : dist (x : E3) (pick x) < r / 2 := Metric.mem_ball.mp (hpick_ball x)
    have hy : dist (pick x) (y : E3) < r / 2 := by
      rw [hpick_eq]
      exact Metric.mem_ball'.mp (hpick_ball y)
    calc
      dist (x : E3) y ≤ dist (x : E3) (pick x) + dist (pick x) y := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hx hy
      _ = r := by ring
  haveI : Finite A := Finite.of_injective pickT hinj
  exact Set.toFinite A

private theorem packing_local_finiteness_of_compact_interior
    {S₀ : Set E3} (hcompact : IsCompact S₀) (hinterior : (interior S₀).Nonempty) :
    EveryPackingLocallyFinite S₀ := by
  intro S K hK
  obtain ⟨x₀, hx₀⟩ := hinterior
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx₀)
  let A : Set RigidMotion :=
    {g | g ∈ S.placements ∧ (g '' S₀ ∩ K).Nonempty}
  let centers : Set E3 := (fun g : RigidMotion => g x₀) '' A
  let C : Set E3 := Metric.cthickening (Metric.diam S₀) K
  have hC : IsCompact C := hK.cthickening
  have hcentersC : centers ⊆ C := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨y, hyS, hyK⟩ := hg.2
    obtain ⟨q, hq, rfl⟩ := hyS
    apply Metric.mem_cthickening_of_dist_le (g x₀) (g q) (Metric.diam S₀) K hyK
    rw [g.isometry.dist_eq]
    exact Metric.dist_le_diam_of_mem hcompact.isBounded (interior_subset hx₀) hq
  have hball_at (g : RigidMotion) :
      Metric.ball (g x₀) r ⊆ interior (g '' S₀) := by
    intro y hy
    have hy' : y ∈ g.toIsometryEquiv '' Metric.ball x₀ r := by
      rw [g.toIsometryEquiv.image_ball]
      exact hy
    have hi : y ∈ g '' interior S₀ := by
      simpa only [AffineIsometryEquiv.coe_toIsometryEquiv] using
        Set.image_mono hball hy'
    have himage : g '' interior S₀ = interior (g '' S₀) := by
      simpa only [AffineIsometryEquiv.coe_toHomeomorph] using
        g.toHomeomorph.image_interior S₀
    rwa [← himage]
  have hsep : ∀ ⦃x⦄, x ∈ centers → ∀ ⦃y⦄, y ∈ centers →
      dist x y < r → x = y := by
    rintro x ⟨g, hg, rfl⟩ y ⟨k, hk, rfl⟩ hdist
    by_contra hne
    have hgk : g ≠ k := by
      intro heq
      apply hne
      rw [heq]
    have hd := S.disjoint_interiors hg.1 hk.1 hgk
    exact Set.disjoint_left.mp hd
      (hball_at g (Metric.mem_ball_self hr))
      (hball_at k (Metric.mem_ball.mpr hdist))
  have hcenters : centers.Finite :=
    finite_of_subset_compact_of_pairwise_dist hC hr hcentersC hsep
  apply Set.Finite.of_finite_image hcenters
  intro g hg k hk heq
  by_contra hne
  have hd := S.disjoint_interiors hg.1 hk.1 hne
  exact Set.disjoint_left.mp hd
    (hball_at g (Metric.mem_ball_self hr))
    (hball_at k (by simpa [heq] using Metric.mem_ball_self (x := g x₀) hr))

/-- A-L2.1.  An interior ball supplies one equal ball per placement.  For
    placements meeting a compact set their centers lie in a compact
    `diam(Q)`-thickening, and disjoint interiors make those centers uniformly
    separated. -/
theorem local_finiteness (h : CompactRegularClosedBall Q) :
    EveryPackingLocallyFinite Q :=
  packing_local_finiteness_of_compact_interior h.1 h.2.2.1

/-- Radial directions which remain in `S` for a sufficiently short positive
    segment based at `x`. For the polyhedral sets here this is the local
    tangent cone used in `ALIGNMENT_PROOF.md` §2. The definition is generic so
    the hypograph calculation can be proved before choosing an orthonormal
    chart into `E3`. -/
def tangentCone {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : Set V) (x : V) : Set V :=
  {v | ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → x + t • v ∈ S}

/-- The hypograph of a real-valued function. -/
def hypograph {V : Type*} (f : V → ℝ) : Set (V × ℝ) :=
  {p | p.2 ≤ f p.1}

/-- The strict downward circular cone associated with a Lipschitz constant.
    It is written in tangent/normal product coordinates. -/
def strictDownwardCone {V : Type*} [Norm V] (K : NNReal) : Set (V × ℝ) :=
  {d | d.2 < -(K : ℝ) * ‖d.1‖}

theorem strictDownwardCone_isOpen
    {V : Type*} [NormedAddCommGroup V] (K : NNReal) :
    IsOpen (strictDownwardCone (V := V) K) := by
  apply isOpen_lt
  · fun_prop
  · fun_prop

/-- Analytic part of A-L4.1: at every graph point of a `K`-Lipschitz
    function, the tangent cone of its hypograph contains all directions
    `w < -K ‖v‖`. -/
theorem strictDownwardCone_subset_tangentCone_hypograph
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : NNReal} {f : V → ℝ} (hf : LipschitzWith K f) (u : V) :
    strictDownwardCone K ⊆ interior (tangentCone (hypograph f) (u, f u)) := by
  apply interior_maximal
  · intro d hd
    refine ⟨1, zero_lt_one, ?_⟩
    intro t ht _
    change f u + t * d.2 ≤ f (u + t • d.1)
    have hLip := hf.dist_le_mul (u + t • d.1) u
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht] at hLip
    have hlower : f u - (K : ℝ) * (t * ‖d.1‖) ≤ f (u + t • d.1) := by
      have habs := neg_le_of_abs_le hLip
      linarith
    have hslope : t * d.2 < -(K : ℝ) * (t * ‖d.1‖) := by
      calc
        t * d.2 < t * (-(K : ℝ) * ‖d.1‖) := mul_lt_mul_of_pos_left hd ht
        _ = -(K : ℝ) * (t * ‖d.1‖) := by ring
    linarith
  · exact strictDownwardCone_isOpen K

/-- Solid angle of a polyhedral cone, as three times the volume it cuts from
    the Euclidean unit ball. -/
def solidAngle (C : Set E3) : ENNReal :=
  3 * MeasureTheory.volume (C ∩ Metric.closedBall (0 : E3) 1)

/-- The closed-form real value claimed for the circular cone's solid angle. -/
def coneAngle (L : ℝ) : ℝ :=
  2 * Real.pi * (1 - L / Real.sqrt (1 + L ^ 2))

/-- Standard downward circular cone in the ambient coordinate chart, with
    coordinate 2 normal and coordinates 0,1 tangent. -/
def circularCone (L : ℝ) : Set E3 :=
  {x | x 2 < -L * Real.sqrt (x 0 ^ 2 + x 1 ^ 2)}

theorem circularCone_isOpen (L : ℝ) : IsOpen (circularCone L) := by
  apply isOpen_lt
  · fun_prop
  · fun_prop

/-- The elementary threshold calculation in A-L4.1. -/
theorem coneAngle_gt_four_pi_div_three_iff {L : ℝ} (hL : 0 ≤ L) :
    coneAngle L > 4 * Real.pi / 3 ↔ 8 * L ^ 2 < 1 := by
  let s := Real.sqrt (1 + L ^ 2)
  have hs2 : s ^ 2 = 1 + L ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by positivity)
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor
  · intro hangle
    have hratio : 3 * L < s := by
      dsimp [coneAngle] at hangle
      field_simp [hs.ne'] at hangle
      nlinarith
    nlinarith [sq_lt_sq₀ (mul_nonneg (by norm_num) hL) hs.le |>.mpr hratio]
  · intro hsq
    have hsq' : (3 * L) ^ 2 < s ^ 2 := by
      nlinarith
    have hratio : 3 * L < s :=
      (sq_lt_sq₀ (mul_nonneg (by norm_num) hL) hs.le).mp hsq'
    dsimp [coneAngle]
    field_simp [hs.ne']
    nlinarith

/-- Orthogonal changes of coordinates preserve the solid angle of the
    standard circular cone. -/
theorem solidAngle_linearIsometry_image (A : E3 ≃ₗᵢ[ℝ] E3) (L : ℝ) :
    solidAngle (A '' circularCone L) = solidAngle (circularCone L) := by
  unfold solidAngle
  congr 1
  have himage :
      A '' (circularCone L ∩ Metric.closedBall (0 : E3) 1) =
        A '' circularCone L ∩ Metric.closedBall (0 : E3) 1 := by
    rw [Set.image_inter A.injective, A.image_closedBall]
    simp
  rw [← himage]
  have hmeas : MeasurableSet
      (circularCone L ∩ Metric.closedBall (0 : E3) 1) :=
    (circularCone_isOpen L).measurableSet.inter measurableSet_closedBall
  have hpre : A '' (circularCone L ∩ Metric.closedBall (0 : E3) 1) =
      A.symm ⁻¹' (circularCone L ∩ Metric.closedBall (0 : E3) 1) :=
    A.toEquiv.image_eq_preimage_symm _
  rw [hpre, ← MeasureTheory.Measure.map_apply_of_aemeasurable
    A.symm.continuous.aemeasurable hmeas, A.symm.measurePreserving.map_eq]

/-- Solid angle is monotone under cone containment. -/
theorem solidAngle_mono {C D : Set E3} (h : C ⊆ D) :
    solidAngle C ≤ solidAngle D := by
  unfold solidAngle
  gcongr

/-- The exact volume identity still missing from the analytic core, minimized
    to the single value used by R44. -/
def R44ConeSolidAngleFormula : Prop :=
  solidAngle (circularCone (3 / 25)) = ENNReal.ofReal (coneAngle (3 / 25))

/-- The remaining concrete local-chart step: at every point of every moved
    feature graph, an orthogonal image of the `L=3/25` model cone lies inside
    the tile's tangent cone. The abstract Lipschitz-to-tangent implication is
    proved above. -/
def FeatureCircularConeContainment (S : Set E3) : Prop :=
  ∀ (T : Tiling S) (g : RigidMotion), g ∈ T.placements →
    ∀ (r : Role) (x : E3), x ∈ featureGraphAt g r →
      ∃ A : E3 ≃ₗᵢ[ℝ] E3,
        A '' circularCone (3 / 25) ⊆ interior (tangentCone (g '' S) x)

/-- The local tangent cones of the finitely many incident tiles have disjoint
    interiors and cover every direction.  This is the cone/sector budget used
    at generic perpendicular edge sections. -/
def ConeSectorBudgets (Q : Set E3) : Prop :=
  ∀ (T : Tiling Q) (x : E3),
    {g | g ∈ T.placements ∧ x ∈ g '' Q}.Finite ∧
    (∀ ⦃g h : RigidMotion⦄, g ∈ T.placements → h ∈ T.placements →
      x ∈ g '' Q → x ∈ h '' Q → g ≠ h →
        Disjoint (interior (tangentCone (g '' Q) x))
          (interior (tangentCone (h '' Q) x))) ∧
    ∀ v : E3, ∃ g : RigidMotion,
      g ∈ T.placements ∧ x ∈ g '' Q ∧ v ∈ tangentCone (g '' Q) x

def baseDeviation (j : Fin 12) : ℝ :=
  Real.arctan (((j : Nat) + 1 : ℝ) / 100)

def ridgeDeviation (j : Fin 12) : ℝ :=
  Real.arccos (1 / (1 + (((j : Nat) + 1 : ℝ) / 100) ^ 2))

def featureDeviation : Fin 24 → ℝ
  | ⟨j, hj⟩ =>
      if h : j < 12 then baseDeviation ⟨j, h⟩
      else ridgeDeviation ⟨j - 12, by omega⟩

def featureSlope (r : Role) : ℝ :=
  ((profileCoefficient r).natAbs : ℝ) / 100

def featureInteriorAngle (r : Role) : FeatureEdgeKind → ℝ
  | .base =>
      if 0 < profileCoefficient r then Real.pi + Real.arctan (featureSlope r)
      else Real.pi - Real.arctan (featureSlope r)
  | .ridge =>
      if 0 < profileCoefficient r then
        Real.pi - Real.arccos (1 / (1 + featureSlope r ^ 2))
      else Real.pi + Real.arccos (1 / (1 + featureSlope r ^ 2))

/-- The tangent-cone solid angle at a generic point of an edge with internal
    dihedral angle `theta` is `2 theta`. -/
def HasFeatureDihedral (Q : Set E3) (r : Role)
    (kind : FeatureEdgeKind) : Prop :=
  ∀ x ∈ nativeGenericEdgesOfKind r kind,
    solidAngle (tangentCone Q x) =
      ENNReal.ofReal (2 * featureInteriorAngle r kind)

/-- A geometric edge from the literal mesh, whose integer endpoints are in
    units of `1/10000`. -/
def nativeMeshEdge (key : V3 × V3) : Set E3 :=
  segment ℝ (scaledV3 10000 key.1) (scaledV3 10000 key.2)

def nativeGenericMeshEdge (key : V3 × V3) : Set E3 :=
  openSegment ℝ (scaledV3 10000 key.1) (scaledV3 10000 key.2)

/-- Continuous meaning of the four exact classes returned by
    `classifyMeshEdge`: base feature, ridge feature, flat subdivision, and
    ordinary right/reentrant carrier edge. -/
def HasMeshDihedralClass (Q : Set E3) (key : V3 × V3)
    (c : Nat × Nat × Int) : Prop :=
  ∀ x ∈ nativeGenericMeshEdge key,
    if c.1 = 0 then
      solidAngle (tangentCone Q x) =
          ENNReal.ofReal (2 * (Real.pi + Real.arctan ((c.2.1 : ℝ) / 100))) ∨
        solidAngle (tangentCone Q x) =
          ENNReal.ofReal (2 * (Real.pi - Real.arctan ((c.2.1 : ℝ) / 100)))
    else if c.1 = 1 then
      solidAngle (tangentCone Q x) = ENNReal.ofReal
          (2 * (Real.pi + Real.arccos (1 / (1 + ((c.2.1 : ℝ) / 100) ^ 2)))) ∨
        solidAngle (tangentCone Q x) = ENNReal.ofReal
          (2 * (Real.pi - Real.arccos (1 / (1 + ((c.2.1 : ℝ) / 100) ^ 2))))
    else if c.1 = 2 then
      solidAngle (tangentCone Q x) = ENNReal.ofReal (2 * Real.pi)
    else
      solidAngle (tangentCone Q x) = ENNReal.ofReal Real.pi ∨
        solidAngle (tangentCone Q x) = ENNReal.ofReal (3 * Real.pi)

/-- The continuous interpretation of the complete phase-1 dihedral audit.
    Every feature's base and ridge edges carry their signed angle class, in
    addition to the finite distinctness and range audit. -/
def CompleteDihedralList (Q : Set E3) : Prop :=
  (∀ r : Role, nativeFeatureGraph r ⊆ frontier Q ∧
    nativeFeatureSurface r ⊆ frontier Q) ∧
  (∀ r : Role, profileCoefficient r ≠ 0 ∧
    (profileCoefficient r).natAbs ≤ 12 ∧
    HasFeatureDihedral Q r .base ∧ HasFeatureDihedral Q r .ridge) ∧
  (∀ key ∈ meshGeometricEdgeKeys, ∃ c : Nat × Nat × Int,
    classifyMeshEdge key = some c ∧ HasMeshDihedralClass Q key c) ∧
  Function.Injective featureDeviation ∧
  ∀ k : Fin 24, 0 < featureDeviation k ∧ featureDeviation k < Real.pi / 4

/-- A point of a root edge has exactly one other incident feature edge of the
    same base/ridge kind and opposite coefficient. -/
def HasUniqueGenericPartner (Q : Set E3) (T : Tiling Q)
    (g : RigidMotion) (r : Role) (kind : FeatureEdgeKind) (x : E3) : Prop :=
  ∃! hs : RigidMotion × Role,
    hs.1 ∈ T.placements ∧ hs.1 ≠ g ∧
      x ∈ genericEdgesOfKindAt hs.1 hs.2 kind ∧
      profileCoefficient r = -profileCoefficient hs.2 ∧
      ∀ k : RigidMotion, k ∈ T.placements → x ∈ k '' Q →
        k = g ∨ k = hs.1

/-- Lemma 3.2, including base/ridge type preservation and a dense generic
    subset of each closed feature graph. -/
def GenericFeaturePartners (Q : Set E3) : Prop :=
  ∀ (T : Tiling Q) (g : RigidMotion), g ∈ T.placements → ∀ r : Role,
    ∃ D : FeatureEdgeKind → Set E3,
      (∀ kind, D kind ⊆ genericEdgesOfKindAt g r kind) ∧
      closure (D .base ∪ D .ridge) = featureGraphAt g r ∧
      ∀ kind x, x ∈ D kind → HasUniqueGenericPartner Q T g r kind x

/-- At every point of every feature graph, the tile's interior tangent cone
    has solid angle strictly greater than `4π/3`. -/
def UniformFeatureSolidAngle (Q : Set E3) : Prop :=
  ∀ (T : Tiling Q) (g : RigidMotion), g ∈ T.placements →
    ∀ (r : Role) (x : E3), x ∈ featureGraphAt g r →
      ENNReal.ofReal (4 * Real.pi / 3) < solidAngle (tangentCone (g '' Q) x)

/-- A root feature graph is covered by the union of all feature graphs of a
    second tile. -/
def FeatureCoveredByTile (g : RigidMotion) (r : Role) (h : RigidMotion) : Prop :=
  featureGraphAt g r ⊆ ⋃ s : Role, featureGraphAt h s

/-- Every root feature has one unique companion tile whose union of feature
    graphs covers the entire connected root graph; one feature of that tile
    in fact contains it. -/
def WholeFeatureCompanions (Q : Set E3) : Prop :=
  ∀ (T : Tiling Q) (g : RigidMotion), g ∈ T.placements → ∀ r : Role,
    ∃ h : RigidMotion,
      h ∈ T.placements ∧ h ≠ g ∧ FeatureCoveredByTile g r h ∧
        FeatureContained g r h ∧
        ∀ k : RigidMotion, k ∈ T.placements → k ≠ g →
          FeatureCoveredByTile g r k → k = h

/-- Containment of a feature graph forces equality of the complete feature
    graph and triangular surface, with opposite polarity. -/
def FeatureContainmentRigidity (Q : Set E3) : Prop :=
  ∀ (T : Tiling Q) (g h : RigidMotion), g ∈ T.placements → h ∈ T.placements →
    g ≠ h →
    ∀ r s, featureGraphAt g r ⊆ featureGraphAt h s → CompleteFeatureMate g r h s

/-- Corollary 4.4 together with the extensional identification of its center /
    normal formula with the phase-1 6,862-pose census. -/
def CompanionPoseDiscrete (Q : Set E3) : Prop :=
  ({m : RigidMotion | ∃ u v : Role, FeatureMateFormula m u v} =
      {m : RigidMotion | CensusMatePose m}) ∧
  ∀ (T : Tiling Q) (g h : RigidMotion), g ∈ T.placements → h ∈ T.placements →
    g ≠ h →
    ∀ r s, CompleteFeatureMate g r h s →
      FeatureMateFormula (relativeMotion g h) r s

/-- Positive-volume overlap of eighth-grid baseline chairs penetrates the
    interiors of the corresponding physical copies of `Q`. -/
def RetainedCoreOverlap (Q : Set E3) : Prop :=
  ∀ (g h : RigidMotion), EighthGridMotion (relativeMotion g h) →
    (interior (g '' P) ∩ interior (h '' P)).Nonempty →
    (interior (g '' Q) ∩ interior (h '' Q)).Nonempty

/-! Structural coordinate helpers used both by the retained-core proof and
the later registered-hierarchy spine. -/

structure FrameData (g : Frame) : Prop where
  px : g.perm.x < 3
  py : g.perm.y < 3
  pz : g.perm.z < 3
  sx : g.sign.x = 1 ∨ g.sign.x = -1
  sy : g.sign.y = 1 ∨ g.sign.y = -1
  sz : g.sign.z = 1 ∨ g.sign.z = -1

theorem allFrames_data {g : Frame} (hg : g ∈ allFrames) : FrameData g := by
  unfold allFrames at hg
  obtain ⟨p, hp, hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hg
  simp [coordinatePermutations] at hp
  simp [signTriples] at hs
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Every coordinate selected by a literal signed frame is a valid coordinate
of three-space. -/
theorem perm_lt_three {f : Frame} (hf : f ∈ allFrames) (i : Fin 3) :
    f.perm.get i < 3 := by
  fin_cases i
  · exact (allFrames_data hf).px
  · exact (allFrames_data hf).py
  · exact (allFrames_data hf).pz

/-- In-range lookup by a natural coordinate is ordinary `Fin 3` evaluation. -/
theorem frameCoordinate_of_lt (x : E3) {j : Nat} (hj : j < 3) :
    frameCoordinate x j = x ⟨j, hj⟩ := by
  simp [frameCoordinate, hj]


end

end R44
