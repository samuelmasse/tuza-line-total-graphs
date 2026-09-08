import Tuza.LinePackets
import Tuza.CliqueEdgeAvoidance

/-! # Adding a root triangle to maximum degree-two/four incidence packings -/

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A non-star line triangle can be reserved while choosing all degree-two/four
maximum local packings, then added as one extra packed triangle. -/
theorem line_packing_augment_nonstar_triangle
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 4)
    (T : Finset G.edgeSet) (hT : T ∈ triangles G.lineGraph)
    (hnostar : ¬∃ v, ∀ e ∈ T, v ∈ e.val) :
    (∑ v, trianglePackingNumber (completeGraph (Fin (G.degree v)))) + 1 ≤
      trianglePackingNumber G.lineGraph := by
  classical
  let S (v : V) : Finset (G.incidenceSet v) :=
    univ.filter (fun e => incidenceToEdge G v e ∈ T)
  have hTcard : T.card = 3 := (mem_cliqueFinset_iff.mp hT).card_eq
  have hS (v : V) : (S v).card ≤ 2 := by
    by_contra h
    have hlarge : 3 ≤ (S v).card := by omega
    let E := (S v).map (incidenceToEdge G v)
    have hE : E ⊆ T := by
      intro e he
      obtain ⟨e0, he0, rfl⟩ := Finset.mem_map.mp he
      exact (Finset.mem_filter.mp he0).2
    have hEq : E = T := Finset.eq_of_subset_of_card_le hE (by
      simpa only [E, Finset.card_map, hTcard] using hlarge)
    apply hnostar
    refine ⟨v, ?_⟩
    intro e he
    rw [← hEq] at he
    obtain ⟨e0, _, rfl⟩ := Finset.mem_map.mp he
    exact incidenceToEdge_mem G v e0
  have hex (v : V) := complete_two_or_four_packing_avoiding_set
    (G.incidenceSet v) (by
      have hc : Fintype.card (G.incidenceSet v) = G.degree v := by
        simpa using G.card_incidenceSet_eq_degree v
      rw [hc]
      exact hdeg v) (S v) (hS v)
  choose Q hQ hcard havoid using hex
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
  have hPT (v : V) (t : Finset G.edgeSet) (ht : t ∈ P v) :
      Disjoint (triangleEdges G.lineGraph t) (triangleEdges G.lineGraph T) := by
    have httri := (hP v).1 ht
    obtain ⟨t0, ht0, rfl⟩ := Finset.mem_map.mp ht
    apply (triangleEdges_disjoint_iff (mem_cliqueFinset_iff.mp httri).isClique).mpr
    intro a hat haT b hbt hbT
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_map.mp hat
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_map.mp hbt
    apply congrArg (incidenceToEdge G v)
    apply Finset.card_le_one.mp (havoid v t0 ht0) a0
    · exact Finset.mem_inter.mpr ⟨ha0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haT⟩⟩
    · exact Finset.mem_inter.mpr ⟨hb0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbT⟩⟩
  have hwhole := packing_biUnion P (fun v _ => hP v) hcross
  have hwholecard : (univ.biUnion P).card =
      ∑ v, trianglePackingNumber (completeGraph (Fin (G.degree v))) := by
    rw [packing_biUnion_card P (fun v _ => hP v) hcross]
    apply Finset.sum_congr rfl
    intro v _
    simpa only [P, Finset.card_map, hcard] using incidence_clique_packing_number G v
  have hsingle : IsTrianglePacking G.lineGraph {T} := by
    refine ⟨by simpa using hT, ?_⟩
    intro t ht u hu htu
    simp only [Finset.mem_singleton] at ht hu
    exact (htu (ht.trans hu.symm)).elim
  have hc : ∀ t ∈ univ.biUnion P, ∀ u ∈ ({T} : Finset (Finset G.edgeSet)),
      Disjoint (triangleEdges G.lineGraph t) (triangleEdges G.lineGraph u) := by
    intro t ht u hu
    obtain ⟨v, _, ht⟩ := Finset.mem_biUnion.mp ht
    have hu' : u = T := Finset.mem_singleton.mp hu
    subst u
    exact hPT v t ht
  have hbound := packing_card_le (packing_union hwhole hsingle hc)
  rw [packing_union_card hwhole hc, hwholecard, Finset.card_singleton] at hbound
  exact hbound

/-- A root triangle supplies a line triangle with no common root endpoint. -/
theorem exists_nonstar_line_triangle (htri : ¬G.CliqueFree 3) :
    ∃ T : Finset G.edgeSet, T ∈ triangles G.lineGraph ∧
      ¬∃ v, ∀ e ∈ T, v ∈ e.val := by
  classical
  obtain ⟨t, ht⟩ := not_forall.mp htri
  have ht' : G.IsNClique 3 t := Classical.not_not.mp ht
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp ht'
  let e : G.edgeSet := ⟨s(a, b), hab⟩
  let f : G.edgeSet := ⟨s(a, c), hac⟩
  let g : G.edgeSet := ⟨s(b, c), hbc⟩
  have hef : e ≠ f := by
    intro h
    have heq := congrArg Subtype.val h
    simp only [e, f, Sym2.eq_iff] at heq
    rcases heq with ⟨_, h⟩ | ⟨h, _⟩
    · exact hbc.ne h
    · exact hac.ne h
  have heg : e ≠ g := by
    intro h
    have heq := congrArg Subtype.val h
    simp only [e, g, Sym2.eq_iff] at heq
    rcases heq with ⟨h, _⟩ | ⟨h, _⟩
    · exact hab.ne h
    · exact hac.ne h
  have hfg : f ≠ g := by
    intro h
    have heq := congrArg Subtype.val h
    simp only [f, g, Sym2.eq_iff] at heq
    rcases heq with ⟨h, _⟩ | ⟨h, _⟩
    · exact hab.ne h
    · exact hac.ne h
  have hadjef : G.lineGraph.Adj e f :=
    SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hef, a, by simp [e], by simp [f]⟩
  have hadjeg : G.lineGraph.Adj e g :=
    SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨heg, b, by simp [e], by simp [g]⟩
  have hadjfg : G.lineGraph.Adj f g :=
    SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hfg, c, by simp [f], by simp [g]⟩
  refine ⟨{e, f, g}, ?_, ?_⟩
  · exact mem_cliqueFinset_iff.mpr
      (SimpleGraph.is3Clique_iff.mpr ⟨e, f, g, hadjef, hadjeg, hadjfg, rfl⟩)
  · rintro ⟨v, hv⟩
    apply triangle_edges_no_common_endpoint hab.ne hac.ne hbc.ne
    exact ⟨v, hv e (by simp), hv f (by simp), hv g (by simp)⟩

/-- The root-triangle branch of the odd Euler seam repair. -/
theorem line_packing_augment_root_triangle
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 4)
    (htri : ¬G.CliqueFree 3) :
    (∑ v, trianglePackingNumber (completeGraph (Fin (G.degree v)))) + 1 ≤
      trianglePackingNumber G.lineGraph := by
  obtain ⟨T, hT, hnostar⟩ := exists_nonstar_line_triangle G htri
  exact line_packing_augment_nonstar_triangle G hdeg T hT hnostar

end Tuza
