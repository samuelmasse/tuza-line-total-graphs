import Tuza.PackingTools
import Tuza.SmallGraphs

/-! # Maximum local packings avoiding a prescribed edge at orders two and four -/

namespace Tuza

open Finset SimpleGraph

theorem complete_fin_two_packing_number :
    trianglePackingNumber (completeGraph (Fin 2)) = 0 := by decide

/-- Deleting either endpoint of a prescribed edge leaves a maximum K4 packing. -/
theorem complete_four_packing_avoiding_edge (V : Type*) [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 4) (a b : V) :
    ∃ P : Finset (Finset V), IsTrianglePacking (completeGraph V) P ∧
      P.card = trianglePackingNumber (completeGraph V) ∧
      ∀ t ∈ P, ¬(a ∈ t ∧ b ∈ t) := by
  have hnu : trianglePackingNumber (completeGraph V) = 1 := by
    rw [complete_packing_number_eq (Fintype.equivFin V), hcard]
    exact completeGraph_fin_four_parameters.1
  let t : Finset V := Finset.univ.erase a
  have ht : t ∈ triangles (completeGraph V) := by
    apply mem_cliqueFinset_iff.mpr
    constructor
    · intro x hx y hy hxy
      exact hxy
    · simp [t, hcard]
  refine ⟨{t}, ?_, by simp [hnu], ?_⟩
  · refine ⟨by simpa using ht, ?_⟩
    intro x hx y hy hxy
    simp only [Finset.mem_singleton] at hx hy
    exact (hxy (hx.trans hy.symm)).elim
  · intro u hu
    have hu' : u = t := Finset.mem_singleton.mp hu
    subst u
    simp [t]

theorem complete_two_packing_avoiding_edge (V : Type*) [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 2) (a b : V) :
    ∃ P : Finset (Finset V), IsTrianglePacking (completeGraph V) P ∧
      P.card = trianglePackingNumber (completeGraph V) ∧
      ∀ t ∈ P, ¬(a ∈ t ∧ b ∈ t) := by
  have hnu : trianglePackingNumber (completeGraph V) = 0 := by
    rw [complete_packing_number_eq (Fintype.equivFin V), hcard]
    exact complete_fin_two_packing_number
  exact ⟨∅, empty_isTrianglePacking _, by simp [hnu], by simp⟩

/-- At orders two and four, a maximum packing can avoid using two vertices
of any prescribed set of size at most two. -/
theorem complete_two_or_four_packing_avoiding_set
    (V : Type*) [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 2 ∨ Fintype.card V = 4)
    (S : Finset V) (hS : S.card ≤ 2) :
    ∃ P : Finset (Finset V), IsTrianglePacking (completeGraph V) P ∧
      P.card = trianglePackingNumber (completeGraph V) ∧
      ∀ t ∈ P, (t ∩ S).card ≤ 1 := by
  rcases hcard with hcard | hcard
  · have hnu : trianglePackingNumber (completeGraph V) = 0 := by
      rw [complete_packing_number_eq (Fintype.equivFin V), hcard]
      exact complete_fin_two_packing_number
    exact ⟨∅, empty_isTrianglePacking _, by simp [hnu], by simp⟩
  · by_cases hempty : S = ∅
    · obtain ⟨P, hP, hp⟩ := exists_maximum_packing (completeGraph V)
      exact ⟨P, hP, hp, by simp [hempty]⟩
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨P, hP, hp, hav⟩ := complete_four_packing_avoiding_edge V hcard a a
      refine ⟨P, hP, hp, ?_⟩
      intro t ht
      have hsub : t ∩ S ⊆ S.erase a := by
        intro x hx
        obtain ⟨hxt, hxS⟩ := Finset.mem_inter.mp hx
        apply Finset.mem_erase.mpr
        refine ⟨?_, hxS⟩
        intro hxa
        subst x
        exact hav t ht ⟨hxt, hxt⟩
      have hcount : (S.erase a).card ≤ 1 := by
        rw [Finset.card_erase_of_mem ha]
        omega
      exact (Finset.card_le_card hsub).trans hcount

end Tuza
