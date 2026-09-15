-- EXPECT: has type
import R44.LogicalSpine

/-!
Packet C2 negative control.  It deliberately tries to derive the existence of
a tiling with two placements of unequal handedness from `Hypotheses`.  The
actual registered-tiling theorem has the opposite type, so this application
must fail to elaborate.

This file is intentionally outside the imported R44 library roots.
-/
namespace R44NegativeControl
open R44

theorem mixed_handedness_tiling_exists (H : Hypotheses) :
    ∃ T : Tiling Q, ∃ g : RigidMotion, g ∈ T.placements ∧
      ∃ h : RigidMotion, h ∈ T.placements ∧ handedness g ≠ handedness h := by
  exact tiling_homochiral H

end R44NegativeControl
