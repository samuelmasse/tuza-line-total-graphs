import Tuza.PackingTools

/-! # Edges of a complete graph on a specified finite vertex subset -/

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def cliqueEdges (s : Finset V) : Finset (Sym2 V) :=
  (completeGraph s).edgeFinset.map (Function.Embedding.subtype (· ∈ s)).sym2Map

theorem cliqueEdges_card (s : Finset V) : (cliqueEdges s).card = s.card.choose 2 := by
  simp only [cliqueEdges, Finset.card_map]
  simpa using (card_edgeFinset_top_eq_card_choose_two (V := s))

@[simp] theorem mk_mem_cliqueEdges {s : Finset V} {a b : V} :
    s(a, b) ∈ cliqueEdges s ↔ a ≠ b ∧ a ∈ s ∧ b ∈ s := by
  rw [cliqueEdges, ← SimpleGraph.edgeFinset_map, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet, SimpleGraph.map_adj]
  constructor
  · rintro ⟨a0, b0, hab, rfl, rfl⟩
    exact ⟨fun h => hab (Subtype.ext h), a0.property, b0.property⟩
  · rintro ⟨hab, ha, hb⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h), rfl, rfl⟩

end Tuza
