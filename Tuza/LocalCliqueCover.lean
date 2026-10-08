module

public import Tuza.CliqueEdges
public import Tuza.LineArithmetic

@[expose] public section

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A balanced cut gives a small cover of all triples in a finite clique. -/
theorem exists_clique_cut (s : Finset V) :
    ∃ C : Finset (Sym2 V), C ⊆ cliqueEdges s ∧ C.card ≤ cliqueCoverCost s.card ∧
      ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c →
        s(a, b) ∈ C ∨ s(a, c) ∈ C ∨ s(b, c) ∈ C := by
  classical
  obtain ⟨A, hAs, hA⟩ := exists_subset_card_eq (Nat.div_le_self s.card 2)
  let C := cliqueEdges A ∪ cliqueEdges (s \ A)
  have hsub : C ⊆ cliqueEdges s := by
    intro e
    refine Sym2.inductionOn e ?_
    intro a b he
    rcases mem_union.mp he with he | he
    · obtain ⟨hne, ha, hb⟩ := mk_mem_cliqueEdges.mp he
      exact mk_mem_cliqueEdges.mpr ⟨hne, hAs ha, hAs hb⟩
    · obtain ⟨hne, ha, hb⟩ := mk_mem_cliqueEdges.mp he
      exact mk_mem_cliqueEdges.mpr ⟨hne, (mem_sdiff.mp ha).1, (mem_sdiff.mp hb).1⟩
  refine ⟨C, hsub, ?_, ?_⟩
  · calc
      C.card ≤ (cliqueEdges A).card + (cliqueEdges (s \ A)).card := card_union_le _ _
      _ = cliqueCoverCost s.card := by
        rw [cliqueEdges_card, cliqueEdges_card, card_sdiff_of_subset hAs, hA,
          balanced_partition_cost]
  · intro a ha b hb c hc hab hac hbc
    have hp : (a ∈ A ∧ b ∈ A ∨ a ∉ A ∧ b ∉ A) ∨
        (a ∈ A ∧ c ∈ A ∨ a ∉ A ∧ c ∉ A) ∨
        (b ∈ A ∧ c ∈ A ∨ b ∉ A ∧ c ∉ A) := by tauto
    have hit {x y : V} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y)
        (h : x ∈ A ∧ y ∈ A ∨ x ∉ A ∧ y ∉ A) : s(x, y) ∈ C := by
      rcases h with h | h
      · exact mem_union_left _ (mk_mem_cliqueEdges.mpr ⟨hne, h.1, h.2⟩)
      · exact mem_union_right _ (mk_mem_cliqueEdges.mpr
          ⟨hne, mem_sdiff.mpr ⟨hx, h.1⟩, mem_sdiff.mpr ⟨hy, h.2⟩⟩)
    exact hp.elim (fun h => Or.inl (hit ha hb hab h))
      (fun h => h.elim (fun h => Or.inr (Or.inl (hit ha hc hac h)))
        (fun h => Or.inr (Or.inr (hit hb hc hbc h))))

end Tuza
