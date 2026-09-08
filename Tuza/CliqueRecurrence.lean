import Tuza.CliqueConstruction
import Tuza.CliqueRecurrenceArithmetic


/-! # Uniform complete-graph packing bounds

The Latin construction with internal packings proves the recurrence
`D(3q) ≥ q² + 3D(q)`. Strong induction, with explicit kernel-checked
bases below 21, gives the balanced cover bound and the extra two units
at even orders at least six. No exact formula for `D` is assumed.
-/

namespace Tuza

open SimpleGraph

theorem complete_fin_packing_mono {a b : ℕ} (hab : a ≤ b) :
    trianglePackingNumber (completeGraph (Fin a)) ≤
      trianglePackingNumber (completeGraph (Fin b)) :=
  packing_number_mono_of_embedding (Fin.castLEEmb hab)
    (fun h => (Fin.castLEEmb hab).injective.ne h)

theorem complete_fin_packing_recurrence (q : ℕ) (hq : 0 < q) :
    q * q + 3 * trianglePackingNumber (completeGraph (Fin q)) ≤
      trianglePackingNumber (completeGraph (Fin (3 * q))) := by
  let : NeZero q := ⟨by omega⟩
  let e : ZMod q ≃ Fin q := Fintype.equivOfCardEq (by simp)
  let e3 : (ZMod q ⊕ ZMod q ⊕ ZMod q) ≃ Fin (3 * q) :=
    Fintype.equivOfCardEq (by simp; omega)
  have h := latin_internal_lower_bound (ZMod q)
  rw [ZMod.card, complete_packing_number_eq e, complete_packing_number_eq e3] at h
  exact h

theorem clique_packing_with_slack_of_small
    (hbase : ∀ n : ℕ, n < 21 →
      cliqueCoverCost n + (if Even n ∧ 6 ≤ n then 2 else 0) ≤
        2 * trianglePackingNumber (completeGraph (Fin n))) (n : ℕ) :
    cliqueCoverCost n + (if Even n ∧ 6 ≤ n then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 21
    · exact hbase n hn
    · let q := n / 3
      let s := n % 3
      have hq : 7 ≤ q := by dsimp [q]; omega
      have hs : s < 3 := Nat.mod_lt _ (by omega)
      have hsplit : n = 3 * q + s := by dsimp [q, s]; omega
      have hqn : q < n := by dsimp [q]; omega
      have hcost : cliqueCoverCost q ≤
          2 * trianglePackingNumber (completeGraph (Fin q)) := by
        have h := ih q hqn
        omega
      have harith := clique_recurrence_arithmetic q s hq hs
      have hrec := complete_fin_packing_recurrence q (by omega)
      have hmono := complete_fin_packing_mono (show 3 * q ≤ n by omega)
      have hslack : (if Even n ∧ 6 ≤ n then 2 else 0) ≤ 2 := by split <;> omega
      rw [← hsplit] at harith
      omega


end Tuza
