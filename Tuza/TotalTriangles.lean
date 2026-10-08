module

public import Tuza.Operators

@[expose] public section

/-! # Bridge triangles and the incidence cliques in a total graph -/

namespace Tuza

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A total-graph triangle with two original vertices must use their joining edge. -/
theorem two_original_vertices_force_bridge {u v : V} {e : G.edgeSet}
    (huv : (totalGraph G).Adj (.inl u) (.inl v))
    (hue : (totalGraph G).Adj (.inl u) (.inr e))
    (hve : (totalGraph G).Adj (.inl v) (.inr e)) : e.val = s(u, v) :=
  (Sym2.mem_and_mem_iff (show G.Adj u v from huv).ne).mp ⟨hue, hve⟩

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Every root edge supplies an actual bridge triangle. -/
theorem bridge_is_triangle {u v : V} (huv : G.Adj u v) :
    let e : G.edgeSet := ⟨s(u, v), by simpa using huv⟩
    ({Sum.inl u, Sum.inr e, Sum.inl v} : Finset (TotalVertex G)) ∈
      triangles (totalGraph G) := by
  dsimp only
  rw [mem_cliqueFinset_iff, is3Clique_iff]
  refine ⟨.inl u, .inr ⟨s(u, v), by simpa using huv⟩, .inl v, ?_, ?_, ?_, rfl⟩
  · simp
  · exact huv
  · simp

/-- Two distinct edges at a root vertex form a triangle with that vertex. -/
theorem incidence_is_triangle {v : V} {e f : G.edgeSet}
    (hne : e ≠ f) (hve : v ∈ e.val) (hvf : v ∈ f.val) :
    ({Sum.inl v, Sum.inr e, Sum.inr f} : Finset (TotalVertex G)) ∈
      triangles (totalGraph G) := by
  rw [mem_cliqueFinset_iff, is3Clique_iff]
  refine ⟨.inl v, .inr e, .inr f, hve, hvf, ?_, rfl⟩
  exact SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne, v, hve, hvf⟩

end Tuza
