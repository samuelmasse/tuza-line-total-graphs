import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Parity

/-! # The balanced-clique cover cost and its parity identities

This file proves arithmetic only. It does not assume or supply clique packings.
-/

namespace Tuza

/-- Number of edges inside the two parts of a balanced bipartition of `K_d`. -/
def cliqueCoverCost (d : ℕ) : ℕ := (d / 2) * ((d - 1) / 2)

@[simp] theorem cliqueCoverCost_even (r : ℕ) :
    cliqueCoverCost (2 * r) = r * (r - 1) := by
  unfold cliqueCoverCost
  have : (2 * r - 1) / 2 = r - 1 := by omega
  simp [this]

@[simp] theorem cliqueCoverCost_odd (r : ℕ) :
    cliqueCoverCost (2 * r + 1) = r * r := by
  unfold cliqueCoverCost
  have : (2 * r + 1) / 2 = r := by omega
  simp [this]

theorem cliqueCoverCost_succ (d : ℕ) :
    cliqueCoverCost (d + 1) = cliqueCoverCost d + d / 2 := by
  rcases Nat.even_or_odd d with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [← two_mul, cliqueCoverCost_odd, cliqueCoverCost_even]
    simp only [Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    cases r with
    | zero => simp
    | succ r => simp; ring
  · rw [show 2 * r + 1 + 1 = 2 * (r + 1) by omega]
    rw [cliqueCoverCost_even, cliqueCoverCost_odd]
    have : (2 * r + 1) / 2 = r := by omega
    simp [this]
    ring

end Tuza
