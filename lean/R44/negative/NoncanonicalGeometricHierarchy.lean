-- EXPECT: geometric_hierarchy_canonical
import R44.LogicalSpine

/-!
Packet P2/M2 negative control.  It deliberately claims that a raw geometric
hierarchy has a noncanonical level-one pose, then supplies the canonicality
theorem.  Elaboration must reject the positive membership proof at the claimed
negated type.

This file is intentionally outside the imported R44 library roots.
-/
namespace R44NegativeControl
open R44

theorem geometric_level_one_pose_is_not_canonical
    (H : Hypotheses) (T : Tiling Q) (K : GeometricHierarchy H T)
    (c : CarrierCell T) :
    K.partition 1 c ∉ (coarseningIterate H 1 T).placements := by
  exact geometric_hierarchy_canonical H T K 1 c

end R44NegativeControl
