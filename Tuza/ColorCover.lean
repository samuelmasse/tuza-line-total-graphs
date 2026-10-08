module

public import Tuza.Definitions

@[expose] public section

/-! # A two-coloring supplies a triangle edge cover -/

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The graph edges whose two endpoints have the same Boolean color. -/
def monochromaticEdges (color : V → Bool) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ u ∈ e, ∀ v ∈ e, color u = color v

theorem monochromaticEdges_cover (color : V → Bool) :
    IsTriangleCover G (monochromaticEdges G color) := by
  constructor
  · exact Finset.filter_subset _ _
  · intro t ht
    rw [mem_cliqueFinset_iff, is3Clique_iff] at ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
    have witness {x y : V} (hxy : G.Adj x y) (hx : x ∈ ({a, b, c} : Finset V))
        (hy : y ∈ ({a, b, c} : Finset V)) (hcolor : color x = color y) :
        ¬Disjoint (monochromaticEdges G color) (triangleEdges G {a, b, c}) := by
      apply Finset.not_disjoint_iff.mpr
      refine ⟨s(x, y), ?_, ?_⟩
      · simp only [monochromaticEdges, Finset.mem_filter]
        refine ⟨by simpa using hxy, ?_⟩
        intro u hu v hv
        simp only [Sym2.mem_iff] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all
      · simp only [triangleEdges, Finset.mem_filter]
        refine ⟨by simpa using hxy, ?_⟩
        rw [Sym2.toFinset_mk_eq]
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy
    have colors : color a = color b ∨ color a = color c ∨ color b = color c := by
      cases color a <;> cases color b <;> cases color c <;> simp_all
    rcases colors with h | h | h
    · exact witness hab (by simp) (by simp) h
    · exact witness hac (by simp) (by simp) h
    · exact witness hbc (by simp) (by simp) h

end Tuza
