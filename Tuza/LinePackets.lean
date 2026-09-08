import Tuza.PackingTools
import Tuza.LineTriangles

/-! # Combining the incidence-clique packings in a line graph -/

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The incidence clique at a root vertex embeds in the line graph. -/
def incidenceToEdge (v : V) : G.incidenceSet v ↪ G.edgeSet where
  toFun e := ⟨e.val, G.incidenceSet_subset v e.property⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun e : G.edgeSet => e.val) h)

@[simp] theorem incidenceToEdge_val (v : V) (e : G.incidenceSet v) :
    (incidenceToEdge G v e).val = e.val := rfl

theorem incidenceToEdge_mem (v : V) (e : G.incidenceSet v) :
    v ∈ (incidenceToEdge G v e).val :=
  (G.edge_mem_incidenceSet_iff).mp e.property

theorem incidenceToEdge_adj (v : V) {a b : G.incidenceSet v}
    (h : (completeGraph (G.incidenceSet v)).Adj a b) :
    G.lineGraph.Adj (incidenceToEdge G v a) (incidenceToEdge G v b) := by
  refine SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨?_, v,
    incidenceToEdge_mem G v a, incidenceToEdge_mem G v b⟩
  exact (incidenceToEdge G v).injective.ne h

theorem incidence_clique_packing_number (v : V) :
    trianglePackingNumber (completeGraph (G.incidenceSet v)) =
      trianglePackingNumber (completeGraph (Fin (G.degree v))) := by
  classical
  exact complete_packing_number_eq (Fintype.equivOfCardEq
    (by simpa using G.card_incidenceSet_eq_degree v))

/-- Packings supported at different root vertices have disjoint line edges. -/
theorem line_packet_cross_disjoint {v w : V} (hvw : v ≠ w)
    {t u : Finset G.edgeSet}
    (ht : t ∈ triangles G.lineGraph)
    (hvt : ∀ e ∈ t, v ∈ e.val) (hwu : ∀ e ∈ u, w ∈ e.val) :
    Disjoint (triangleEdges G.lineGraph t) (triangleEdges G.lineGraph u) := by
  rw [triangleEdges_disjoint_iff (mem_cliqueFinset_iff.mp ht).isClique]
  intro a hat hau b hbt hbu
  by_contra hab
  exact hvw (common_endpoint_unique hab (hvt a hat) (hvt b hbt)
    (hwu a hau) (hwu b hbu))

/-- Actual maximal local clique packings can be simultaneously selected and united. -/
theorem exists_line_packet_packing :
    ∃ P, IsTrianglePacking G.lineGraph P ∧
      P.card = ∑ v, trianglePackingNumber (completeGraph (Fin (G.degree v))) := by
  classical
  have hex (v : V) := exists_maximum_packing (completeGraph (G.incidenceSet v))
  choose Q hQ hcard using hex
  let P (v : V) := (Q v).map
    ⟨Finset.map (incidenceToEdge G v), Finset.map_injective _⟩
  have hP (v : V) : IsTrianglePacking G.lineGraph (P v) :=
    packing_map (incidenceToEdge G v) (incidenceToEdge_adj G v) (hQ v)
  have hsupport (v : V) (t : Finset G.edgeSet) (ht : t ∈ P v) :
      ∀ e ∈ t, v ∈ e.val := by
    obtain ⟨t0, _, rfl⟩ := Finset.mem_map.mp ht
    intro e he
    obtain ⟨e0, _, rfl⟩ := Finset.mem_map.mp he
    exact incidenceToEdge_mem G v e0
  have hcross (v : V) (_ : v ∈ (univ : Finset V))
      (w : V) (_ : w ∈ (univ : Finset V)) (hvw : v ≠ w)
      (t : Finset G.edgeSet) (ht : t ∈ P v)
      (u : Finset G.edgeSet) (hu : u ∈ P w) :
      Disjoint (triangleEdges G.lineGraph t) (triangleEdges G.lineGraph u) :=
    line_packet_cross_disjoint G hvw ((hP v).1 ht)
      (hsupport v t ht) (hsupport w u hu)
  refine ⟨univ.biUnion P, packing_biUnion P (fun v _ => hP v) hcross, ?_⟩
  rw [packing_biUnion_card P (fun v _ => hP v) hcross]
  apply Finset.sum_congr rfl
  intro v _
  simpa only [P, card_map, hcard] using incidence_clique_packing_number G v

theorem linePacking_lower_bound :
    (∑ v, trianglePackingNumber (completeGraph (Fin (G.degree v)))) ≤
      trianglePackingNumber G.lineGraph := by
  obtain ⟨P, hP, hcard⟩ := exists_line_packet_packing G
  simpa only [hcard] using packing_card_le hP

end Tuza
