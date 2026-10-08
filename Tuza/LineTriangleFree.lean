module

public import Tuza.LocalCliqueCover
public import Tuza.LinePackets
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def lineIncidence (v : V) : Finset G.edgeSet :=
  univ.map (incidenceToEdge G v)

@[simp] theorem lineIncidence_card (v : V) : (lineIncidence G v).card = G.degree v := by
  simp only [lineIncidence, card_map, card_univ, G.card_incidenceSet_eq_degree]

@[simp] theorem mem_lineIncidence (v : V) (e : G.edgeSet) :
    e ∈ lineIncidence G v ↔ v ∈ e.val := by
  constructor
  · intro he
    obtain ⟨e0, _, rfl⟩ := mem_map.mp he
    exact incidenceToEdge_mem G v e0
  · intro he
    refine mem_map.mpr ⟨⟨e.val, G.edge_mem_incidenceSet_iff.mpr he⟩, mem_univ _, ?_⟩
    rfl

/-- A triangle-free root has only star triangles, so independent local cuts suffice. -/
theorem line_triangleFree_cover_bound (hfree : G.CliqueFree 3) :
    triangleCoverNumber G.lineGraph ≤ ∑ v, cliqueCoverCost (G.degree v) := by
  classical
  have hex (v : V) := exists_clique_cut (lineIncidence G v)
  choose C hsub hcard hhit using hex
  have hC : IsTriangleCover G.lineGraph (univ.biUnion C) := by
    constructor
    · intro x hx
      obtain ⟨v, _, hx⟩ := mem_biUnion.mp hx
      have hs := hsub v hx
      revert hs
      refine Sym2.inductionOn x ?_
      intro e f hs
      obtain ⟨hne, he, hf⟩ := mk_mem_cliqueEdges.mp hs
      exact mem_edgeFinset.mpr (lineGraph_adj_iff_exists.mpr
        ⟨hne, v, mem_lineIncidence G v e |>.mp he, mem_lineIncidence G v f |>.mp hf⟩)
    · intro t ht
      obtain ⟨e, f, g, hef, heg, hfg, rfl⟩ := is3Clique_iff.mp (mem_cliqueFinset_iff.mp ht)
      have hs : ∃ v, v ∈ e.val ∧ v ∈ f.val ∧ v ∈ g.val := by
        rcases lineGraph_triangle_classification hef heg hfg with h | h
        · exact h
        · obtain ⟨a, b, c, _, _, _, hab, hac, hbc, _⟩ := h
          exact False.elim ((is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩).not_cliqueFree hfree)
      obtain ⟨v, he, hf, hg⟩ := hs
      have hh := hhit v e ((mem_lineIncidence G v e).mpr he)
        f ((mem_lineIncidence G v f).mpr hf) g ((mem_lineIncidence G v g).mpr hg)
        hef.ne heg.ne hfg.ne
      have hit {a b : G.edgeSet} (hab : G.lineGraph.Adj a b)
          (ha : a ∈ ({e, f, g} : Finset G.edgeSet)) (hb : b ∈ ({e, f, g} : Finset G.edgeSet))
          (h : s(a,b) ∈ C v) :
          ¬Disjoint (univ.biUnion C) (triangleEdges G.lineGraph {e, f, g}) := by
        exact not_disjoint_iff.mpr ⟨s(a,b), mem_biUnion.mpr ⟨v, mem_univ _, h⟩,
          mk_mem_triangleEdges.mpr ⟨hab, ha, hb⟩⟩
      exact hh.elim (hit hef (by simp) (by simp))
        (fun h => h.elim (hit heg (by simp) (by simp)) (hit hfg (by simp) (by simp)))
  apply (cover_number_le hC).trans
  apply (card_biUnion_le).trans
  exact sum_le_sum fun v _ => by simpa only [lineIncidence_card] using hcard v

end Tuza
