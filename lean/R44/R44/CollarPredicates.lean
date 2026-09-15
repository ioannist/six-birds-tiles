import R44.GlobalPredicates
-- [compile-fix: factor frozen collar predicates to break promoted import cycles]

namespace R44

open Set

noncomputable section

/-! Foundational registered-baseline and collar predicates, factored from the
logical spine so that discharged collar proofs do not import their consumers. -/

/-- Poses which become integer/proper-cubic after one common ambient isometry,
    and whose copies of the literal chair `P` tile space. -/
structure RegisteredBaselineTiling (A : Set RigidMotion) where
  tiling : Tiling P
  placements_eq : tiling.placements = A
  registered : Registered tiling

/-- Two closed sets meet on a relatively open two-dimensional planar patch.
    This excludes contacts consisting only of an edge or vertex. -/
def SharesPlanarPatch (A B : Set E3) : Prop :=
  ∃ x n : E3, ∃ ε : ℝ, n ≠ 0 ∧ 0 < ε ∧
    ∀ y : E3, dist y x < ε → inner ℝ (y - x) n = 0 → y ∈ A ∩ B

/-- Cell-wise face adjacency of two integer registered chair bodies. -/
def LatticeFaceAdjacent (g h : RigidMotion) : Prop :=
  ∃ p : Pose,
    p.frame ∈ allFrames ∧ RealizesPose (relativeMotion g h) p ∧
      touch rootPose p = true

/-- A registered baseline chair tiling whose genuine face adjacencies are
    exactly licensed by the literal 44-contact language. -/
structure AtlasBaselineTiling (A : Set RigidMotion)
    extends RegisteredBaselineTiling A where
  atlas_faces : ∀ ⦃g h : RigidMotion⦄, g ∈ A → h ∈ A → g ≠ h →
    LatticeFaceAdjacent g h → AtlasRelated g h

/-- The single geometric small-collar statement shared by coarsening and the
    explicit nested construction. -/
def SmallCollarRealization : Prop :=
  ∀ (A : Set RigidMotion), AtlasBaselineTiling A →
    ∃ T : Tiling Q, T.placements = A

end
end R44
