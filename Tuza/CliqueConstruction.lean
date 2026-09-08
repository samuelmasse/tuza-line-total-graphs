import Tuza.LatinPacking
import Mathlib.Data.ZMod.Basic

/-! # Adding three internal clique packings to a Latin packing -/

namespace Tuza

open Finset SimpleGraph
open SimpleGraph.TripartiteFromTriangles

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem complete_mapped_packing (f : V ↪ W) {P : Finset (Finset V)}
    (hP : IsTrianglePacking (completeGraph V) P) :
    IsTrianglePacking (completeGraph W) (P.map ⟨Finset.map f, Finset.map_injective f⟩) :=
  packing_map f (fun h => f.injective.ne h) hP

theorem mapped_packing_cross (f : V ↪ W) {P : Finset (Finset V)}
    {Q : Finset (Finset W)} (hP : IsTrianglePacking (completeGraph V) P)
    (hf : ∀ t ∈ Q, ∀ a b : V, f a ∈ t → f b ∈ t → a = b) :
    ∀ t ∈ P.map ⟨Finset.map f, Finset.map_injective f⟩, ∀ u ∈ Q,
      Disjoint (triangleEdges (completeGraph W) t) (triangleEdges (completeGraph W) u) := by
  intro t ht u hu
  have htri := (complete_mapped_packing f hP).1 ht
  obtain ⟨t0, _, rfl⟩ := Finset.mem_map.mp ht
  apply (triangleEdges_disjoint_iff (mem_cliqueFinset_iff.mp htri).isClique).mpr
  intro a hat hau b hbt hbu
  obtain ⟨a0, _, rfl⟩ := Finset.mem_map.mp hat
  obtain ⟨b0, _, rfl⟩ := Finset.mem_map.mp hbt
  exact congrArg f (hf u hu a0 b0 hau hbu)

variable (A : Type*) [AddGroup A] [Fintype A] [DecidableEq A]

def cliqueIn0 : A ↪ A ⊕ A ⊕ A := ⟨Sum.inl, Sum.inl_injective⟩
def cliqueIn1 : A ↪ A ⊕ A ⊕ A :=
  ⟨fun a => Sum.inr (Sum.inl a), Sum.inr_injective.comp Sum.inl_injective⟩
def cliqueIn2 : A ↪ A ⊕ A ⊕ A :=
  ⟨fun a => Sum.inr (Sum.inr a), Sum.inr_injective.comp Sum.inr_injective⟩

theorem latin_same_part (i : Fin 3) (t : Finset (A ⊕ A ⊕ A)) (ht : t ∈ latinPacking A)
    (a b : A) :
    (if i = 0 then cliqueIn0 A else if i = 1 then cliqueIn1 A else cliqueIn2 A) a ∈ t →
    (if i = 0 then cliqueIn0 A else if i = 1 then cliqueIn1 A else cliqueIn2 A) b ∈ t → a = b := by
  obtain ⟨⟨x, y, z⟩, _, rfl⟩ := Finset.mem_map.mp ht
  fin_cases i <;> simp [cliqueIn0, cliqueIn1, cliqueIn2, toTriangle_apply, Sum3.in₀,
    Sum3.in₁, Sum3.in₂, Function.Embedding.coeFn_mk] <;> grind

theorem latin_internal_lower_bound :
    Fintype.card A * Fintype.card A + 3 * trianglePackingNumber (completeGraph A) ≤
      trianglePackingNumber (completeGraph (A ⊕ A ⊕ A)) := by
  obtain ⟨P, hP, hcard⟩ := exists_maximum_packing (completeGraph A)
  let P0 := P.map ⟨Finset.map (cliqueIn0 A), Finset.map_injective _⟩
  let P1 := P.map ⟨Finset.map (cliqueIn1 A), Finset.map_injective _⟩
  let P2 := P.map ⟨Finset.map (cliqueIn2 A), Finset.map_injective _⟩
  have h0 : IsTrianglePacking (completeGraph (A ⊕ A ⊕ A)) P0 := complete_mapped_packing _ hP
  have h1 : IsTrianglePacking (completeGraph (A ⊕ A ⊕ A)) P1 := complete_mapped_packing _ hP
  have h2 : IsTrianglePacking (completeGraph (A ⊕ A ⊕ A)) P2 := complete_mapped_packing _ hP
  have hc01 : ∀ t ∈ P0, ∀ u ∈ P1,
      Disjoint (triangleEdges (completeGraph (A ⊕ A ⊕ A)) t)
        (triangleEdges (completeGraph (A ⊕ A ⊕ A)) u) := by
    apply mapped_packing_cross _ hP
    intro t ht a b ha hb
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp ht
    simp [cliqueIn0, cliqueIn1, Function.Embedding.coeFn_mk] at ha
  have hc02 : ∀ t ∈ P0, ∀ u ∈ P2,
      Disjoint (triangleEdges (completeGraph (A ⊕ A ⊕ A)) t)
        (triangleEdges (completeGraph (A ⊕ A ⊕ A)) u) := by
    apply mapped_packing_cross _ hP
    intro t ht a b ha hb
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp ht
    simp [cliqueIn0, cliqueIn2, Function.Embedding.coeFn_mk] at ha
  have hc12 : ∀ t ∈ P1, ∀ u ∈ P2,
      Disjoint (triangleEdges (completeGraph (A ⊕ A ⊕ A)) t)
        (triangleEdges (completeGraph (A ⊕ A ⊕ A)) u) := by
    apply mapped_packing_cross _ hP
    intro t ht a b ha hb
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp ht
    simp [cliqueIn1, cliqueIn2, Function.Embedding.coeFn_mk] at ha
  have hc012 : ∀ t ∈ P0 ∪ P1, ∀ u ∈ P2,
      Disjoint (triangleEdges (completeGraph (A ⊕ A ⊕ A)) t)
        (triangleEdges (completeGraph (A ⊕ A ⊕ A)) u) := by
    intro t ht u hu
    rcases Finset.mem_union.mp ht with ht | ht
    · exact hc02 t ht u hu
    · exact hc12 t ht u hu
  have hi := packing_union (packing_union h0 h1 hc01) h2 hc012
  have hcl : ∀ t ∈ (P0 ∪ P1) ∪ P2, ∀ u ∈ latinPacking A,
      Disjoint (triangleEdges (completeGraph (A ⊕ A ⊕ A)) t)
        (triangleEdges (completeGraph (A ⊕ A ⊕ A)) u) := by
    intro t ht u hu
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht
      · exact mapped_packing_cross (cliqueIn0 A) hP
          (fun u hu a b => by simpa using latin_same_part A 0 u hu a b) t ht u hu
      · exact mapped_packing_cross (cliqueIn1 A) hP
          (fun u hu a b => by simpa using latin_same_part A 1 u hu a b) t ht u hu
    · exact mapped_packing_cross (cliqueIn2 A) hP
        (fun u hu a b => by simpa using latin_same_part A 2 u hu a b) t ht u hu
  have hbound := packing_card_le (packing_union hi (latinPacking_valid A) hcl)
  rw [packing_union_card hi hcl, packing_union_card (packing_union h0 h1 hc01) hc012,
    packing_union_card h0 hc01, latinPacking_card] at hbound
  simp only [P0, P1, P2, Finset.card_map, hcard] at hbound
  omega

end Tuza
