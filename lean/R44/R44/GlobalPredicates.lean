import R44.LogicalSpineFoundation
-- [compile-fix: factor frozen alignment predicates to break promoted import cycles]

namespace R44

open Set

noncomputable section

/-- Every complete feature companion occurring in a tiling has relative pose
    in the literal 44-contact atlas. -/
def OnlyRegisteredMates (Q : Set E3) : Prop :=
  ∀ (T : Tiling Q) (g h : RigidMotion), g ∈ T.placements → h ∈ T.placements →
    g ≠ h →
    (∃ r s, CompleteFeatureMate g r h s) → AtlasRelated g h

/-- Two placed tiles are adjacent in the undirected complete-feature graph. -/
def FeatureAdjacent {Q : Set E3} (T : Tiling Q) (g h : RigidMotion) : Prop :=
  g ∈ T.placements ∧ h ∈ T.placements ∧ g ≠ h ∧
    ((∃ r s, CompleteFeatureMate g r h s) ∨
      ∃ r s, CompleteFeatureMate h r g s)

/-- Membership in the same connected component of the feature graph. -/
def SameFeatureComponent {Q : Set E3} (T : Tiling Q)
    (g h : RigidMotion) : Prop :=
  Relation.ReflTransGen (FeatureAdjacent T) g h

/-- After normalizing the root, its feature component has registered poses and
    its closed baseline chairs cover space with pairwise disjoint interiors;
    equivalently, their seven-cell bodies tile the complete unit-cube grid. -/
def BaselineComponentCoversGrid (Q : Set E3) : Prop :=
  ∀ (T : Tiling Q) (g : RigidMotion), g ∈ T.placements →
    ∃ A : RigidMotion, A * g = 1 ∧
      (∀ h : RigidMotion, h ∈ T.placements → SameFeatureComponent T g h →
        Nonempty (RegisteredPose (A * h))) ∧
      (∀ x : E3, ∃ h : RigidMotion, h ∈ T.placements ∧
        SameFeatureComponent T g h ∧ x ∈ (A * h) '' P) ∧
      ∀ ⦃h k : RigidMotion⦄, h ∈ T.placements → k ∈ T.placements →
        SameFeatureComponent T g h → SameFeatureComponent T g k → h ≠ k →
        Disjoint (interior ((A * h) '' P)) (interior ((A * k) '' P))

/-- The physical `Q` copies in that feature-component cover all of `E3`. -/
def ComponentSolidsCover (Q : Set E3) : Prop :=
  ∀ (T : Tiling Q) (g : RigidMotion), g ∈ T.placements →
    ∀ x : E3, ∃ h : RigidMotion, h ∈ T.placements ∧
      SameFeatureComponent T g h ∧ x ∈ h '' Q

/-- Every tiling is globally registered after one ambient isometry. -/
def UnrestrictedAlignment (Q : Set E3) : Prop :=
  ∀ T : Tiling Q, Registered T

end
end R44
