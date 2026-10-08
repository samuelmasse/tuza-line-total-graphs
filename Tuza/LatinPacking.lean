module

public import Tuza.PackingTools
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
public import Mathlib.Algebra.Group.Basic

@[expose] public section

/-! # A Latin-square triangle packing across three equal vertex parts

The triangles indexed by `(a,b,a+b)` in three disjoint copies of a finite
additive group are edge-disjoint. This construction supplies a uniform
complete-graph packing without requiring an unproved edge-coloring theorem.
-/

namespace Tuza

open Finset SimpleGraph
open SimpleGraph.TripartiteFromTriangles

variable (A : Type*) [AddGroup A] [Fintype A] [DecidableEq A]

def latinIndexEmbedding : A × A ↪ A × A × A where
  toFun p := (p.1, p.2, p.1 + p.2)
  inj' := by intro p q h; cases p; cases q; simpa using congrArg (fun x => (x.1, x.2.1)) h

def latinIndices : Finset (A × A × A) := Finset.univ.map (latinIndexEmbedding A)

omit [DecidableEq A] in
@[simp] theorem mem_latinIndices {a b c : A} :
    (a, b, c) ∈ latinIndices A ↔ a + b = c := by
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, _, h⟩ := Finset.mem_map.mp h
    change (x, y, x + y) = (a, b, c) at h
    cases h
    rfl
  · intro h
    apply Finset.mem_map.mpr
    exact ⟨(a, b), Finset.mem_univ _, by change (a, b, a + b) = (a, b, c); rw [h]⟩

instance latinIndices_explicitDisjoint : ExplicitDisjoint (latinIndices A) where
  inj₀ := by
    intro a b c a' h h'
    rw [mem_latinIndices] at h h'
    exact add_right_cancel (h.trans h'.symm)
  inj₁ := by
    intro a b c b' h h'
    rw [mem_latinIndices] at h h'
    exact add_left_cancel (h.trans h'.symm)
  inj₂ := by
    intro a b c c' h h'
    rw [mem_latinIndices] at h h'
    exact h.symm.trans h'

def latinPacking : Finset (Finset (A ⊕ A ⊕ A)) := (latinIndices A).map toTriangle

theorem latinPacking_valid : IsTrianglePacking (completeGraph (A ⊕ A ⊕ A)) (latinPacking A) := by
  rw [isTrianglePacking_iff_shared_vertices]
  constructor
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ht
    exact mem_cliqueFinset_iff.mpr ((toTriangle_is3Clique hx).mono le_top)
  · intro t ht u hu hne a hat hau b hbt hbu
    exact map_toTriangle_disjoint (latinIndices A) ht hu hne ⟨hat, hau⟩ ⟨hbt, hbu⟩

@[simp] theorem latinPacking_card : (latinPacking A).card = Fintype.card A * Fintype.card A := by
  simp [latinPacking, latinIndices]

theorem latinPacking_lower_bound : Fintype.card A * Fintype.card A ≤
    trianglePackingNumber (completeGraph (A ⊕ A ⊕ A)) := by
  simpa using packing_card_le (latinPacking_valid A)

end Tuza
