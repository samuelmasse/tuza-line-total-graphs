module

public import Tuza.Certificates

@[expose] public section

/-! # Structural tools for transporting and combining triangle packings -/

namespace Tuza

open Finset SimpleGraph

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H : SimpleGraph W} [DecidableRel H.Adj]

@[simp] theorem mk_mem_triangleEdges {a b : V} {t : Finset V} :
    s(a, b) ∈ triangleEdges G t ↔ G.Adj a b ∧ a ∈ t ∧ b ∈ t := by
  simp only [triangleEdges, Finset.mem_filter]
  constructor
  · rintro ⟨he, ht⟩
    exact ⟨by simpa using he, ht (by simp), ht (by simp)⟩
  · rintro ⟨hab, ha, hb⟩
    refine ⟨by simpa using hab, ?_⟩
    intro v hv
    simp only [Sym2.mem_toFinset, Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact ha
    · exact hb

/-- In a clique, sharing two vertices is exactly sharing a graph edge. -/
theorem triangleEdges_disjoint_iff {t u : Finset V} (ht : G.IsClique t) :
    Disjoint (triangleEdges G t) (triangleEdges G u) ↔
      ∀ a ∈ t, a ∈ u → ∀ b ∈ t, b ∈ u → a = b := by
  constructor
  · intro h a hat hau b hbt hbu
    by_contra hab
    have hadj := ht hat hbt hab
    exact Finset.disjoint_left.mp h
      (mk_mem_triangleEdges.mpr ⟨hadj, hat, hbt⟩)
      (mk_mem_triangleEdges.mpr ⟨hadj, hau, hbu⟩)
  · intro h
    apply Finset.disjoint_left.mpr
    intro e
    refine Sym2.inductionOn e ?_
    intro a b het heu
    obtain ⟨hab, hat, hbt⟩ := mk_mem_triangleEdges.mp het
    obtain ⟨_, hau, hbu⟩ := mk_mem_triangleEdges.mp heu
    exact hab.ne (h a hat hau b hbt hbu)

/-- A packing consists of triangles whose distinct members share at most one vertex. -/
theorem isTrianglePacking_iff_shared_vertices {P : Finset (Finset V)} :
    IsTrianglePacking G P ↔ P ⊆ triangles G ∧
      ∀ t ∈ P, ∀ u ∈ P, t ≠ u →
        ∀ a ∈ t, a ∈ u → ∀ b ∈ t, b ∈ u → a = b := by
  constructor
  · rintro ⟨hP, hdisj⟩
    refine ⟨hP, ?_⟩
    intro t ht u hu hne
    exact (triangleEdges_disjoint_iff (mem_cliqueFinset_iff.mp (hP ht)).isClique).mp
      (hdisj ht hu hne)
  · rintro ⟨hP, hshared⟩
    refine ⟨hP, ?_⟩
    intro t ht u hu hne
    exact (triangleEdges_disjoint_iff (mem_cliqueFinset_iff.mp (hP ht)).isClique).mpr
      (hshared t ht u hu hne)

theorem triangle_map (f : V ↪ W)
    (hf : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b))
    {t : Finset V} (ht : t ∈ triangles G) : t.map f ∈ triangles H := by
  rw [mem_cliqueFinset_iff, is3Clique_iff] at ht ⊢
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  exact ⟨f a, f b, f c, hf hab, hf hac, hf hbc, by simp⟩

/-- Injective graph homomorphisms transport an actual packing without changing its size. -/
theorem packing_map (f : V ↪ W)
    (hf : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b))
    {P : Finset (Finset V)} (hP : IsTrianglePacking G P) :
    IsTrianglePacking H (P.map ⟨Finset.map f, Finset.map_injective f⟩) := by
  rw [isTrianglePacking_iff_shared_vertices] at hP ⊢
  constructor
  · intro t ht
    obtain ⟨t0, ht0, rfl⟩ := Finset.mem_map.mp ht
    exact triangle_map f hf (hP.1 ht0)
  · intro t ht u hu hne a hat hau b hbt hbu
    obtain ⟨t0, ht0, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨u0, hu0, rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨a0, hat0, rfl⟩ := Finset.mem_map.mp hat
    obtain ⟨b0, hbt0, rfl⟩ := Finset.mem_map.mp hbt
    have hau' : a0 ∈ u0 := by simpa using hau
    have hbu' : b0 ∈ u0 := by simpa using hbu
    have htu : t0 ≠ u0 := by intro h; exact hne (congrArg (Finset.map f) h)
    exact congrArg f (hP.2 t0 ht0 u0 hu0 htu a0 hat0 hau' b0 hbt0 hbu')

theorem packing_number_mono_of_embedding (f : V ↪ W)
    (hf : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b)) :
    trianglePackingNumber G ≤ trianglePackingNumber H := by
  obtain ⟨P, hP, hcard⟩ := exists_maximum_packing G
  have h := packing_card_le (packing_map f hf hP)
  simpa [hcard] using h

/-- Isomorphic finite graphs have the same edge-packing number. -/
theorem packing_number_eq_of_iso (f : G ≃g H) :
    trianglePackingNumber G = trianglePackingNumber H := by
  apply Nat.le_antisymm
  · exact packing_number_mono_of_embedding f.toEquiv.toEmbedding
      (fun h => f.map_adj_iff.mpr h)
  · exact packing_number_mono_of_embedding f.symm.toEquiv.toEmbedding
      (fun h => f.symm.map_adj_iff.mpr h)

/-- Complete-graph packing numbers depend only on vertex cardinality. -/
theorem complete_packing_number_eq (e : V ≃ W) :
    trianglePackingNumber (completeGraph V) = trianglePackingNumber (completeGraph W) := by
  apply Nat.le_antisymm
  · exact packing_number_mono_of_embedding e.toEmbedding (fun h => by simpa using e.injective.ne h)
  · exact packing_number_mono_of_embedding e.symm.toEmbedding
      (fun h => by simpa using e.symm.injective.ne h)

/-- Edge-disjoint nonempty triangles from different packets cannot be identical. -/
theorem packings_disjoint_of_cross {P Q : Finset (Finset V)}
    (hP : IsTrianglePacking G P)
    (hcross : ∀ t ∈ P, ∀ u ∈ Q, Disjoint (triangleEdges G t) (triangleEdges G u)) :
    Disjoint P Q := by
  apply Finset.disjoint_left.mpr
  intro t htP htQ
  obtain ⟨e, he⟩ := triangleEdges_nonempty G (hP.1 htP)
  exact Finset.disjoint_left.mp (hcross t htP t htQ) he he

theorem packing_union {P Q : Finset (Finset V)}
    (hP : IsTrianglePacking G P) (hQ : IsTrianglePacking G Q)
    (hcross : ∀ t ∈ P, ∀ u ∈ Q, Disjoint (triangleEdges G t) (triangleEdges G u)) :
    IsTrianglePacking G (P ∪ Q) := by
  constructor
  · exact Finset.union_subset hP.1 hQ.1
  · intro t ht u hu hne
    rcases Finset.mem_union.mp ht with ht | ht <;>
      rcases Finset.mem_union.mp hu with hu | hu
    · exact hP.2 ht hu hne
    · exact hcross t ht u hu
    · exact (hcross u hu t ht).symm
    · exact hQ.2 ht hu hne

theorem packing_union_card {P Q : Finset (Finset V)}
    (hP : IsTrianglePacking G P)
    (hcross : ∀ t ∈ P, ∀ u ∈ Q, Disjoint (triangleEdges G t) (triangleEdges G u)) :
    (P ∪ Q).card = P.card + Q.card :=
  Finset.card_union_of_disjoint (packings_disjoint_of_cross hP hcross)

theorem packing_biUnion {I : Type*} {s : Finset I} (P : I → Finset (Finset V))
    (hP : ∀ i ∈ s, IsTrianglePacking G (P i))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ t ∈ P i, ∀ u ∈ P j, Disjoint (triangleEdges G t) (triangleEdges G u)) :
    IsTrianglePacking G (s.biUnion P) := by
  classical
  constructor
  · intro t ht
    obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.mp ht
    exact (hP i hi).1 hti
  · intro t ht u hu hne
    obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨j, hj, huj⟩ := Finset.mem_biUnion.mp hu
    by_cases hij : i = j
    · subst j
      exact (hP i hi).2 hti huj hne
    · exact hcross i hi j hj hij t hti u huj

theorem packing_biUnion_card {I : Type*} {s : Finset I} (P : I → Finset (Finset V))
    (hP : ∀ i ∈ s, IsTrianglePacking G (P i))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ t ∈ P i, ∀ u ∈ P j, Disjoint (triangleEdges G t) (triangleEdges G u)) :
    (s.biUnion P).card = ∑ i ∈ s, (P i).card := by
  classical
  apply Finset.card_biUnion
  intro i hi j hj hij
  exact packings_disjoint_of_cross (hP i hi) (hcross i hi j hj hij)

end Tuza
