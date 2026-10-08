module

public import Tuza.CliqueArithmetic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Tuza

theorem twice_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_sub_cancel]
    cases n with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel] at ih; nlinarith

theorem balanced_choose_cost (a b : ℕ) (hab : a ≤ b + 1) (hba : b ≤ a + 1) :
    a.choose 2 + b.choose 2 = cliqueCoverCost (a + b) := by
  wlog h : b ≤ a generalizing a b
  · simpa [Nat.add_comm] using this b a hba hab (by omega)
  have hh : a = b ∨ a = b + 1 := by omega
  rcases hh with rfl | rfl
  · rw [← two_mul, ← two_mul, cliqueCoverCost_even, twice_choose_two]
  · rw [show b + 1 + b = 2 * b + 1 by omega, cliqueCoverCost_odd]
    simp only [Nat.choose_succ_succ, Nat.choose_one_right]
    have hh := twice_choose_two b
    cases b with
    | zero => simp
    | succ b => simp only [Nat.add_sub_cancel] at hh; nlinarith

theorem seam_choose_cost (a b : ℕ) (hab : a ≤ b + 2) (hba : b ≤ a + 2) :
    a.choose 2 + b.choose 2 ≤ cliqueCoverCost (a + b) + 1 := by
  by_cases h1 : a ≤ b + 1 ∧ b ≤ a + 1
  · rw [balanced_choose_cost a b h1.1 h1.2]; omega
  wlog h : b ≤ a generalizing a b
  · simpa [Nat.add_comm] using this b a hba hab (by omega) (by omega)
  have hh : a = b + 2 := by omega
  subst a
  rw [show b + 2 + b = 2 * (b + 1) by omega, cliqueCoverCost_even]
  simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right,
    Nat.succ_eq_add_one, Nat.reduceAdd, Nat.add_sub_cancel]
  have hh := twice_choose_two b
  cases b with
  | zero => simp
  | succ b => simp only [Nat.add_sub_cancel] at hh; nlinarith

theorem balanced_partition_cost (n : ℕ) :
    (n / 2).choose 2 + (n - n / 2).choose 2 = cliqueCoverCost n := by
  simpa [Nat.add_sub_of_le (Nat.div_le_self n 2)] using
    balanced_choose_cost (n / 2) (n - n / 2) (by omega) (by omega)

end Tuza
