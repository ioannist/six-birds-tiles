/-!
# R44 modular coincidence: the closed form of the rate

Standalone, library-free Lean 4 (no Mathlib, no `native_decide`, no `sorry`); not part of the
`lean/R44` lake project or its ledger.  `simulations/coincidence_rate.py` counts the digit words
of length M whose label is not yet determined: 176, 400, 848, ... from M = 3, each term twice
the previous plus 48.  This file proves the closed form 28 * 2^M - 48 from that recurrence.
The counts are computation; the kernel certifies only the arithmetic.

    lean simulations/explore/lean/CoincidenceRate.lean
-/

namespace CoincidenceRate

/-- Non-coincident words, indexed from depth 3. -/
def cc : Nat → Nat
  | 0     => 176
  | n + 1 => 2 * cc n + 48

theorem closed_form : ∀ n : Nat, cc n + 48 = 224 * 2 ^ n := by
  intro n
  induction n with
  | zero => decide
  | succ k ih =>
    have e : cc (k + 1) = 2 * cc k + 48 := rfl
    rw [e, Nat.pow_succ]
    omega

theorem first_terms : cc 0 = 176 ∧ cc 1 = 400 ∧ cc 2 = 848 := by decide

end CoincidenceRate
