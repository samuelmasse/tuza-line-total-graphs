module

public import Tuza.PackingTools

@[expose] public section

/-! # A small independent checker for literal lists of clique triangles

Three vertices per entry and intersection size at most one for each pair
imply both an edge-disjoint triangle packing and absence of duplicate entries.
The list length therefore supplies an exact, checked lower bound.
-/

namespace Tuza

open Finset SimpleGraph

theorem completePacking_of_cards_inter {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset (Finset V)) (hc : ∀ t ∈ P, t.card = 3)
    (hi : ∀ t ∈ P, ∀ u ∈ P, t ≠ u → (t ∩ u).card ≤ 1) :
    IsTrianglePacking (completeGraph V) P := by
  rw [isTrianglePacking_iff_shared_vertices]
  refine ⟨?_, ?_⟩
  · intro t ht
    apply mem_cliqueFinset_iff.mpr
    exact ⟨fun _ _ _ _ h => h, hc t ht⟩
  · intro t ht u hu hne a hat hau b hbt hbu
    exact Finset.card_le_one.mp (hi t ht u hu hne) a (Finset.mem_inter.mpr ⟨hat, hau⟩)
      b (Finset.mem_inter.mpr ⟨hbt, hbu⟩)

/-- A list certificate avoids repeated normalization of a large outer finset. -/
theorem completePacking_list_length_le {V : Type*} [Fintype V] [DecidableEq V]
    (l : List (Finset V)) (hc : ∀ t ∈ l, t.card = 3)
    (hi : l.Pairwise fun t u => (t ∩ u).card ≤ 1) :
    l.length ≤ trianglePackingNumber (completeGraph V) := by
  have hn : l.Nodup := hi.imp_of_mem (fun {t u} ht _ hi htu => by
    subst u
    simp only [Finset.inter_self, hc t ht] at hi
    omega)
  have hpair : l.Pairwise (fun t u => t = u ∨ (t ∩ u).card ≤ 1) :=
    hi.imp (fun h => Or.inr h)
  have hflip : l.Pairwise (flip (fun t u => t = u ∨ (t ∩ u).card ≤ 1)) :=
    hi.imp (fun h => Or.inr (by simpa [Finset.inter_comm] using h))
  have hall := List.Pairwise.forall_of_forall_of_flip
    (R := fun t u : Finset V => t = u ∨ (t ∩ u).card ≤ 1)
    (fun t _ => Or.inl rfl) hpair hflip
  have hP : IsTrianglePacking (completeGraph V) l.toFinset := by
    apply completePacking_of_cards_inter
    · intro t ht
      exact hc t (List.mem_toFinset.mp ht)
    · intro t ht u hu hne
      exact (hall (List.mem_toFinset.mp ht) (List.mem_toFinset.mp hu)).resolve_left hne
  simpa [List.toFinset_card_of_nodup hn] using packing_card_le hP

end Tuza
