import Tuza.CliqueRecurrence
import Tuza.CliqueFiniteCertificates

/-! # The uniform clique packing bounds used by the paper -/

namespace Tuza

open SimpleGraph

theorem clique_packing_with_slack (n : ℕ) :
    cliqueCoverCost n + (if Even n ∧ 6 ≤ n then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin n)) :=
  clique_packing_with_slack_of_small clique_packing_small n
/-- The basic local clique inequality from the paper. -/
theorem cliqueCoverCost_le_twice_packing (n : ℕ) :
    cliqueCoverCost n ≤ 2 * trianglePackingNumber (completeGraph (Fin n)) := by
  have h := clique_packing_with_slack n
  omega

/-- The even-order slack used to absorb the Euler seam. -/
theorem cliqueCoverCost_add_two_le_twice_packing (n : ℕ) (heven : Even n) (hn : 6 ≤ n) :
    cliqueCoverCost n + 2 ≤ 2 * trianglePackingNumber (completeGraph (Fin n)) := by
  simpa [heven, hn] using clique_packing_with_slack n

theorem cliqueCoverCost_card_le_twice_packing (V : Type*) [Fintype V] [DecidableEq V] :
    cliqueCoverCost (Fintype.card V) ≤ 2 * trianglePackingNumber (completeGraph V) := by
  rw [complete_packing_number_eq (Fintype.equivFin V)]
  exact cliqueCoverCost_le_twice_packing _

theorem cliqueCoverCost_card_add_two_le_twice_packing
    (V : Type*) [Fintype V] [DecidableEq V]
    (heven : Even (Fintype.card V)) (hn : 6 ≤ Fintype.card V) :
    cliqueCoverCost (Fintype.card V) + 2 ≤ 2 * trianglePackingNumber (completeGraph V) := by
  rw [complete_packing_number_eq (Fintype.equivFin V)]
  exact cliqueCoverCost_add_two_le_twice_packing _ heven hn

end Tuza
