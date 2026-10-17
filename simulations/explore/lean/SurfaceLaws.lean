/-!
# R44 surface and interface laws: the counting identities

Standalone, library-free Lean 4 (no Mathlib, no `native_decide`, no `sorry`).
It is NOT part of the `lean/R44` lake project or of its trust ledger.  It proves
only the arithmetic that `simulations/surface_laws.py` counts for N <= 4:

  * a depth-N patch has 8^N copies, each with 24 boundary faces; each shared
    face removes two, and there are 12 (8^N - 4^N) of them, leaving 24 * 4^N;
  * the interface count B_c = (T(c) P(N-c) - P(N)) / 2 with T(c) = 8^c and
    P(k) = 24 * 4^k equals 12 * 4^N * (2^c - 1).

The counts themselves (24 faces per tile, 12 (8^N - 4^N) shared faces) are
facts about the geometry, established by the script, not by this file.

    lean simulations/explore/lean/SurfaceLaws.lean
-/

namespace SurfaceLaws

/-- Boundary faces: 24 per tile on 8^N tiles, less two per shared face. -/
theorem boundary_faces (N : Nat) :
    (24 : Int) * 8 ^ N - 2 * (12 * (8 ^ N - 4 ^ N)) = 24 * 4 ^ N := by omega

/-- 8^c * 24 * 4^m = 24 * 2^c * 4^(c+m), with N = c + m. -/
theorem interface_form (c m : Nat) :
    (8 ^ c * 24 * 4 ^ m : Nat) = 24 * 2 ^ c * 4 ^ (c + m) := by
  rw [Nat.pow_add]
  have h : (8 : Nat) ^ c = 2 ^ c * 4 ^ c := by
    rw [← Nat.mul_pow]
  rw [h]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- With a = 2^c and b = 4^N: 24 a b - 24 b = 2 (12 b (a - 1)), the algebra
behind B_c = (T(c) P(N-c) - P(N)) / 2 = 12 * 4^N * (2^c - 1). -/
theorem interface_algebra (a b : Int) :
    24 * (a * b) - 24 * b = 2 * (12 * (b * (a - 1))) := by
  rw [Int.mul_sub, Int.mul_one, Int.mul_comm b a]
  omega

/-- B_c = (T(c) P(N-c) - P(N)) / 2 = 12 * 4^N * (2^c - 1), for N = c + m,
T(c) = 8^c and P(k) = 24 * 4^k. -/
theorem interface_law (c m : Nat) :
    ((8 : Int) ^ c * (24 * 4 ^ m) - 24 * 4 ^ (c + m)) =
      2 * (12 * 4 ^ (c + m) * (2 ^ c - 1)) := by
  have h := interface_form c m
  have h' : ((8 : Int) ^ c * 24 * 4 ^ m) = 24 * 2 ^ c * 4 ^ (c + m) := by
    exact_mod_cast h
  have e : (8 : Int) ^ c * (24 * 4 ^ m) = 8 ^ c * 24 * 4 ^ m := by
    rw [Int.mul_assoc]
  rw [e, h']
  have := interface_algebra ((2 : Int) ^ c) ((4 : Int) ^ (c + m))
  simpa [Int.mul_assoc] using this

/-- The exponent: the boundary grows by 4 = 2^2 per level against a linear
inflation of 2, so log 4 / log 2 = 2 = d - 1 (ordinary surface). -/
theorem growth_is_square : (4 : Nat) = 2 ^ 2 := by decide

end SurfaceLaws
