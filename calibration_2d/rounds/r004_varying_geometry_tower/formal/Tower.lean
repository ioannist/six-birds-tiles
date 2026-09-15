import Lean.Elab.Tactic.Omega

/-!
SBT anti-symmetry extension across varying geometric layers.
No common tile alphabet or stationary deflation map is assumed.
Physical geometry must independently supply the minimum-period bound.
-/
namespace EinsteinCalibration

structure CoarseningTower (P : Type) (zero : P) where
  Level : Nat → Type
  shift : (n : Nat) → P → Level n → Level n
  up : (n : Nat) → Level n → Level (n + 1)
  covariant : ∀ n p x, up n (shift n p x) = shift (n + 1) p (up n x)
  height : P → Nat
  spacing : Nat → Nat
  cofinal : ∀ h : Nat, ∃ n, h < spacing n
  period_lower_bound : ∀ n p x, p ≠ zero → shift n p x = x → spacing n ≤ height p

def CoarseningTower.lift {P : Type} {zero : P} (T : CoarseningTower P zero) :
    (n : Nat) → T.Level 0 → T.Level n
  | 0, x => x
  | n+1, x => T.up n (T.lift n x)

theorem period_lifts {P : Type} {zero : P} (T : CoarseningTower P zero)
    (x : T.Level 0) (p : P) (h : T.shift 0 p x = x) :
    ∀ n, T.shift n p (T.lift n x) = T.lift n x := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih =>
    change T.shift (n+1) p (T.up n (T.lift n x)) = T.up n (T.lift n x)
    rw [← T.covariant, ih]

theorem tower_forces_trivial_stabilizers {P : Type} {zero : P}
    (T : CoarseningTower P zero) (x : T.Level 0) (p : P)
    (h : T.shift 0 p x = x) : p = zero := by
  classical
  by_cases hp : p = zero
  · exact hp
  · obtain ⟨n, hn⟩ := T.cofinal (T.height p)
    have bound := T.period_lower_bound n p (T.lift n x) hp (period_lifts T x p h n)
    omega

theorem nonempty_tower_landing {P : Type} {zero : P}
    (T : CoarseningTower P zero) (hne : Nonempty (T.Level 0)) :
    Nonempty (T.Level 0) ∧ ∀ x p, T.shift 0 p x = x → p = zero := by
  exact ⟨hne, fun x p h => tower_forces_trivial_stabilizers T x p h⟩

#print axioms period_lifts
#print axioms tower_forces_trivial_stabilizers
#print axioms nonempty_tower_landing
end EinsteinCalibration
