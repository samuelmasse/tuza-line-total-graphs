import Tuza.Definitions

/-! # Total graphs and the exact finite-root target statements

Line graphs use Mathlib's `SimpleGraph.lineGraph` without changing its meaning.
The total graph has one vertex for each root vertex and one for each root edge.
-/

namespace Tuza

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Original vertices and edge-vertices form a disjoint sum. -/
abbrev TotalVertex := V ⊕ G.edgeSet

/-- Total-graph adjacency: original adjacency, incidence, or adjacent edges. -/
def totalAdj : TotalVertex G → TotalVertex G → Prop
  | .inl u, .inl v => G.Adj u v
  | .inl u, .inr e => u ∈ (e.val : Sym2 V)
  | .inr e, .inl v => v ∈ (e.val : Sym2 V)
  | .inr e, .inr f => G.lineGraph.Adj e f

/-- The ordinary total graph of a simple graph. -/
def totalGraph : SimpleGraph (TotalVertex G) where
  Adj := totalAdj G
  symm.symm := by
    intro a b h
    cases a <;> cases b
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact G.lineGraph.adj_symm h
  loopless.irrefl := by
    intro a h
    cases a
    · exact G.loopless.irrefl _ h
    · exact G.lineGraph.loopless.irrefl _ h

instance lineGraphDecidableAdj [Fintype V] [DecidableEq V] : DecidableRel G.lineGraph.Adj :=
  fun _ _ => decidable_of_iff' _ SimpleGraph.lineGraph_adj_iff_exists

instance totalGraphDecidableAdj [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (totalGraph G).Adj := by
  intro a b
  change Decidable (totalAdj G a b)
  cases a <;> cases b <;> dsimp [totalAdj] <;> infer_instance

@[simp] theorem totalGraph_adj_inl_inl (u v : V) :
    (totalGraph G).Adj (.inl u) (.inl v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem totalGraph_adj_inl_inr (u : V) (e : G.edgeSet) :
    (totalGraph G).Adj (.inl u) (.inr e) ↔ u ∈ (e.val : Sym2 V) := Iff.rfl

@[simp] theorem totalGraph_adj_inr_inl (e : G.edgeSet) (v : V) :
    (totalGraph G).Adj (.inr e) (.inl v) ↔ v ∈ (e.val : Sym2 V) := Iff.rfl

@[simp] theorem totalGraph_adj_inr_inr (e f : G.edgeSet) :
    (totalGraph G).Adj (.inr e) (.inr f) ↔ G.lineGraph.Adj e f := Iff.rfl

end Tuza
