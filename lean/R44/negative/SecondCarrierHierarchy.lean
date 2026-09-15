-- EXPECT: carrier_hierarchy_unique
import R44.LogicalSpine

/-!
Packet C3/R7 negative control.  It deliberately claims that two copies of the
intrinsic hierarchy differ at level one, then offers the mathematical
uniqueness theorem as the required inequality.  Elaboration must reject the
equality supplied by `carrier_hierarchy_unique`.

This file is intentionally outside the imported R44 library roots.
-/
namespace R44NegativeControl
open R44

theorem second_carrier_hierarchy_differs_at_level_one
    (H : Hypotheses) (T : Tiling Q) :
    ∃ K K' : CarrierHierarchy H T, K.partition 1 ≠ K'.partition 1 := by
  refine ⟨carrierHierarchy H T, carrierHierarchy H T, ?_⟩
  exact congrArg (fun K : CarrierHierarchy H T => K.partition 1)
    (carrier_hierarchy_unique H T (carrierHierarchy H T) (carrierHierarchy H T))

end R44NegativeControl
