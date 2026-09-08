import Tuza.CliqueArithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-! # The arithmetic lift for the three-part clique construction -/

namespace Tuza

theorem cliqueCoverCost_mono {a b : ℕ} (hab : a ≤ b) :
    cliqueCoverCost a ≤ cliqueCoverCost b := by
  unfold cliqueCoverCost
  exact Nat.mul_le_mul (Nat.div_le_div_right hab)
    (Nat.div_le_div_right (Nat.sub_le_sub_right hab 1))

theorem clique_recurrence_arithmetic (q s : ℕ) (hq : 7 ≤ q) (hs : s < 3) :
    cliqueCoverCost (3 * q + s) + 2 ≤ 2 * (q * q) + 3 * cliqueCoverCost q := by
  have hm := cliqueCoverCost_mono (show 3 * q + s ≤ 3 * q + 2 by omega)
  suffices cliqueCoverCost (3 * q + 2) + 2 ≤ 2 * (q * q) + 3 * cliqueCoverCost q by omega
  rcases Nat.even_or_odd q with ⟨r, hr⟩ | ⟨r, rfl⟩
  · rw [← two_mul] at hr
    subst q
    have hr : 4 ≤ r := by omega
    have hform : 3 * (2 * r) + 2 = 2 * (3 * r + 1) := by omega
    rw [hform, cliqueCoverCost_even, cliqueCoverCost_even]
    have hsub : r - 1 + 1 = r := by omega
    have hsub' : 3 * r + 1 - 1 = 3 * r := by omega
    rw [hsub']
    nlinarith [Nat.mul_le_mul_left r hr]
  · have hr : 3 ≤ r := by omega
    have hform : 3 * (2 * r + 1) + 2 = 2 * (3 * r + 2) + 1 := by omega
    rw [hform, cliqueCoverCost_odd, cliqueCoverCost_odd]
    nlinarith [Nat.mul_le_mul_left r hr]

end Tuza
