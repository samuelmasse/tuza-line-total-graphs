module

public import Tuza.PackingTools
public import Tuza.TotalTriangles
public import Tuza.LineTriangles

@[expose] public section

/-! # The bridge packing and disjoint total-graph packet assembly -/

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def totalInl : V ↪ TotalVertex G := ⟨Sum.inl, Sum.inl_injective⟩
def totalInr : G.edgeSet ↪ TotalVertex G := ⟨Sum.inr, Sum.inr_injective⟩

/-- The bridge uses an edge-vertex and the two endpoints of its root edge. -/
def totalBridge (e : G.edgeSet) : Finset (TotalVertex G) :=
  insert (.inr e) (e.val.toFinset.map (totalInl G))

@[simp] theorem inl_mem_totalBridge (u : V) (e : G.edgeSet) :
    Sum.inl u ∈ totalBridge G e ↔ u ∈ e.val := by
  simp [totalBridge, totalInl]

@[simp] theorem inr_mem_totalBridge (e f : G.edgeSet) :
    Sum.inr e ∈ totalBridge G f ↔ e = f := by
  simp [totalBridge, totalInl]

theorem totalBridge_injective : Function.Injective (totalBridge G) := by
  intro e f h
  have : Sum.inr e ∈ totalBridge G f := h ▸ (by simp)
  simpa using this

theorem totalBridge_triangle (e : G.edgeSet) :
    totalBridge G e ∈ triangles (totalGraph G) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hadj : G.Adj a b := he
    convert bridge_is_triangle hadj using 1
    ext x
    cases x <;> simp [totalBridge, totalInl]

def totalBridges : Finset (Finset (TotalVertex G)) :=
  univ.map ⟨totalBridge G, totalBridge_injective G⟩

theorem totalBridges_packing : IsTrianglePacking (totalGraph G) (totalBridges G) := by
  rw [isTrianglePacking_iff_shared_vertices]
  constructor
  · intro t ht
    obtain ⟨e, _, rfl⟩ := mem_map.mp ht
    exact totalBridge_triangle G e
  · intro t ht u hu hne a hat hau b hbt hbu
    obtain ⟨e, _, rfl⟩ := mem_map.mp ht
    obtain ⟨f, _, rfl⟩ := mem_map.mp hu
    have hef : e ≠ f := fun h => hne (congrArg (totalBridge G) h)
    cases a with
    | inr a =>
      have hae := (inr_mem_totalBridge G a e).mp hat
      have haf := (inr_mem_totalBridge G a f).mp hau
      exact False.elim (hef (hae.symm.trans haf))
    | inl a =>
      cases b with
      | inr b =>
        have hbe := (inr_mem_totalBridge G b e).mp hbt
        have hbf := (inr_mem_totalBridge G b f).mp hbu
        exact False.elim (hef (hbe.symm.trans hbf))
      | inl b =>
        exact congrArg Sum.inl (common_endpoint_unique hef
          ((inl_mem_totalBridge G a e).mp hat) ((inl_mem_totalBridge G a f).mp hau)
          ((inl_mem_totalBridge G b e).mp hbt) ((inl_mem_totalBridge G b f).mp hbu))

@[simp] theorem totalBridges_card : (totalBridges G).card = G.edgeFinset.card := by
  simp [totalBridges, SimpleGraph.edgeFinset_card]

theorem totalBridge_disjoint_line_triangle (e : G.edgeSet) (t : Finset G.edgeSet) :
    Disjoint (triangleEdges (totalGraph G) (totalBridge G e))
      (triangleEdges (totalGraph G) (t.map (totalInr G))) := by
  apply (triangleEdges_disjoint_iff
    (mem_cliqueFinset_iff.mp (totalBridge_triangle G e)).isClique).mpr
  intro a hae hat b hbe hbt
  obtain ⟨a, _, rfl⟩ := mem_map.mp hat
  obtain ⟨b, _, rfl⟩ := mem_map.mp hbt
  have ha : a = e := (inr_mem_totalBridge G a e).mp hae
  have hb : b = e := (inr_mem_totalBridge G b e).mp hbe
  exact congrArg Sum.inr (ha.trans hb.symm)

/-- All bridges can be added to any line-graph packing after its natural inclusion. -/
theorem total_packing_from_line {P : Finset (Finset G.edgeSet)}
    (hP : IsTrianglePacking G.lineGraph P) :
    ∃ Q, IsTrianglePacking (totalGraph G) Q ∧ Q.card = G.edgeFinset.card + P.card := by
  let R := P.map ⟨Finset.map (totalInr G), Finset.map_injective (totalInr G)⟩
  have hR : IsTrianglePacking (totalGraph G) R :=
    packing_map (totalInr G) (fun h => h) hP
  have hcross : ∀ t ∈ totalBridges G, ∀ u ∈ R,
      Disjoint (triangleEdges (totalGraph G) t) (triangleEdges (totalGraph G) u) := by
    intro t ht u hu
    obtain ⟨e, _, rfl⟩ := mem_map.mp ht
    obtain ⟨u, _, rfl⟩ := mem_map.mp hu
    exact totalBridge_disjoint_line_triangle G e u
  refine ⟨totalBridges G ∪ R, packing_union (totalBridges_packing G) hR hcross, ?_⟩
  rw [packing_union_card (totalBridges_packing G) hcross, totalBridges_card]
  simp [R]

theorem total_packing_number_ge_edges_add_line :
    G.edgeFinset.card + trianglePackingNumber G.lineGraph ≤
      trianglePackingNumber (totalGraph G) := by
  obtain ⟨P, hP, hcard⟩ := exists_maximum_packing G.lineGraph
  obtain ⟨Q, hQ, hQcard⟩ := total_packing_from_line G hP
  simpa [hQcard, hcard] using packing_card_le hQ

end Tuza
