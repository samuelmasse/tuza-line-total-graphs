import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Data.Finset.Max

/-!
# Triangle packing and edge-cover definitions

Adapted from Samuel Massé's vmath project, VMath/Tuza/Basic.lean.  A
triangle is a three-vertex clique, packings are graph-edge-disjoint, and covers
consist of graph edges meeting every triangle.

The definitions are executable on finite graphs. Packings are edge-disjoint,
not necessarily vertex-disjoint. Both optimization domains are nonempty even
when the graph has no vertices or edges.
-/

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The ordinary graph triangles of `G`, represented by their vertex sets. -/
abbrev triangles : Finset (Finset V) := G.cliqueFinset 3

/-- The graph edges of `G` whose endpoints both lie in `t`. -/
def triangleEdges (t : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => e.toFinset ⊆ t

/-- A family of triangles is a packing when distinct members share no graph edge. -/
def IsTrianglePacking (P : Finset (Finset V)) : Prop :=
  P ⊆ triangles G ∧
    ∀ ⦃t⦄, t ∈ P → ∀ ⦃u⦄, u ∈ P → t ≠ u →
      Disjoint (triangleEdges G t) (triangleEdges G u)

/-- An edge set is a triangle cover when it consists of graph edges and meets every triangle. -/
def IsTriangleCover (C : Finset (Sym2 V)) : Prop :=
  C ⊆ G.edgeFinset ∧
    ∀ ⦃t⦄, t ∈ triangles G → ¬Disjoint C (triangleEdges G t)

instance (P : Finset (Finset V)) : Decidable (IsTrianglePacking G P) := by
  unfold IsTrianglePacking
  infer_instance

instance (C : Finset (Sym2 V)) : Decidable (IsTriangleCover G C) := by
  unfold IsTriangleCover
  infer_instance

/-- All triangle packings of `G`. -/
def trianglePackings : Finset (Finset (Finset V)) :=
  (triangles G).powerset.filter (IsTrianglePacking G)

/-- All triangle covers of `G`. -/
def triangleCovers : Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter (IsTriangleCover G)

theorem triangleEdges_nonempty {t : Finset V} (ht : t ∈ triangles G) :
    (triangleEdges G t).Nonempty := by
  rw [mem_cliqueFinset_iff, is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
  refine ⟨s(a, b), ?_⟩
  apply mem_filter.mpr
  constructor
  · simp [hab]
  · rw [Sym2.toFinset_mk_eq]
    simp

theorem empty_isTrianglePacking : IsTrianglePacking G ∅ := by
  simp [IsTrianglePacking]

theorem edgeFinset_isTriangleCover : IsTriangleCover G G.edgeFinset := by
  refine ⟨Subset.rfl, ?_⟩
  intro t ht hdisjoint
  obtain ⟨e, he⟩ := triangleEdges_nonempty G ht
  have heG : e ∈ G.edgeFinset := (mem_filter.mp he).1
  exact Finset.disjoint_left.mp hdisjoint heG he

theorem trianglePackings_nonempty : (trianglePackings G).Nonempty := by
  refine ⟨∅, ?_⟩
  simp [trianglePackings, empty_isTrianglePacking G]

theorem triangleCovers_nonempty : (triangleCovers G).Nonempty := by
  refine ⟨G.edgeFinset, ?_⟩
  simp [triangleCovers, edgeFinset_isTriangleCover G]

/-- The finite set of attainable triangle-packing sizes. -/
def trianglePackingSizes : Finset ℕ :=
  (trianglePackings G).image card

/-- The finite set of attainable triangle-cover sizes. -/
def triangleCoverSizes : Finset ℕ :=
  (triangleCovers G).image card

theorem trianglePackingSizes_nonempty : (trianglePackingSizes G).Nonempty :=
  (trianglePackings_nonempty G).image card

theorem triangleCoverSizes_nonempty : (triangleCoverSizes G).Nonempty :=
  (triangleCovers_nonempty G).image card

/-- Tuza's integral triangle packing number `ν△(G)`. -/
def trianglePackingNumber : ℕ :=
  (trianglePackingSizes G).max' (trianglePackingSizes_nonempty G)

/-- Tuza's integral triangle edge-cover number `τ△(G)`. -/
def triangleCoverNumber : ℕ :=
  (triangleCoverSizes G).min' (triangleCoverSizes_nonempty G)

/-- The Tuza inequality for one finite simple graph. -/
def SatisfiesTuza : Prop :=
  triangleCoverNumber G ≤ 2 * trianglePackingNumber G

/-- A literal counterexample has integral cover number strictly above twice its packing number. -/
def IsTuzaCounterexample : Prop :=
  2 * trianglePackingNumber G < triangleCoverNumber G

end Tuza
