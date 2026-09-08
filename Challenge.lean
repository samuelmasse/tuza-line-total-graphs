import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Data.Finset.Max

/-!
# Tuza's conjecture for line and total graphs: target statements

Author: Samuel Massé. AI assistance: OpenAI's GPT-6 Astra.

This is a Comparator statement module, not a proof. Its four deliberate
statement holes specify the intended claims. Solution is compiled separately
and must prove every claim without importing this module or using these holes.

Definitions below are copied from Tuza/Definitions.lean and Tuza/Operators.lean
so the statement imports only Mathlib. Keep the copied bodies identical.
-/

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



/-! # Total graphs and the exact finite-root target statements

Line graphs use Mathlib's `SimpleGraph.lineGraph` without changing its meaning.
The total graph has one vertex for each root vertex and one for each root edge.
-/

namespace Tuza

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- Original vertices and edge-vertices form a disjoint sum. -/
abbrev TotalVertex := V ⊕ G.edgeSet

/-- Total-graph adjacency: original adjacency, incidence, or adjacent edges. -/
def totalAdj : TotalVertex G → TotalVertex G → Prop
  | .inl u, .inl v => G.Adj u v
  | .inl u, .inr e => u ∈ (e.val : Sym2 V)
  | .inr e, .inl v => v ∈ (e.val : Sym2 V)
  | .inr e, .inr f => G.lineGraph.Adj e f

/-- The ordinary total graph of a simple graph. -/
def totalGraph : SimpleGraph (TotalVertex G) where
  Adj := totalAdj G
  symm.symm := by
    intro a b h
    cases a <;> cases b
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact G.lineGraph.adj_symm h
  loopless.irrefl := by
    intro a h
    cases a
    · exact G.loopless.irrefl _ h
    · exact G.lineGraph.loopless.irrefl _ h

instance lineGraphDecidableAdj [Fintype V] [DecidableEq V] : DecidableRel G.lineGraph.Adj :=
  fun _ _ => decidable_of_iff' _ SimpleGraph.lineGraph_adj_iff_exists

instance totalGraphDecidableAdj [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (totalGraph G).Adj := by
  intro a b
  change Decidable (totalAdj G a b)
  cases a <;> cases b <;> dsimp [totalAdj] <;> infer_instance

@[simp] theorem totalGraph_adj_inl_inl (u v : V) :
    (totalGraph G).Adj (.inl u) (.inl v) ↔ G.Adj u v := Iff.rfl

@[simp] theorem totalGraph_adj_inl_inr (u : V) (e : G.edgeSet) :
    (totalGraph G).Adj (.inl u) (.inr e) ↔ u ∈ (e.val : Sym2 V) := Iff.rfl

@[simp] theorem totalGraph_adj_inr_inl (e : G.edgeSet) (v : V) :
    (totalGraph G).Adj (.inr e) (.inl v) ↔ v ∈ (e.val : Sym2 V) := Iff.rfl

@[simp] theorem totalGraph_adj_inr_inr (e f : G.edgeSet) :
    (totalGraph G).Adj (.inr e) (.inr f) ↔ G.lineGraph.Adj e f := Iff.rfl

end Tuza

namespace Tuza

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Manuscript Theorem 1.1, including empty and disconnected finite simple roots. -/
theorem lineGraph_satisfiesTuza (G : SimpleGraph V) [DecidableRel G.Adj] :
    SatisfiesTuza G.lineGraph := by sorry

/-- Manuscript Theorem 1.2, with no triangle-free or degree hypothesis. -/
theorem totalGraph_satisfiesTuza (G : SimpleGraph V) [DecidableRel G.Adj] :
    SatisfiesTuza (totalGraph G) := by sorry

/-- Sharpness means an actual line graph has packing number 1 and cover number 2. -/
theorem lineGraph_factor_sharp :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_h : DecidableRel G.Adj),
      @trianglePackingNumber _ _ _ G.lineGraph (lineGraphDecidableAdj G) = 1 ∧
      @triangleCoverNumber _ _ _ G.lineGraph (lineGraphDecidableAdj G) = 2 := by sorry

/-- Manuscript Corollary 1.3. Doubled natural counts express exactly 5n/2. -/
theorem cubic_triangleFree_total_parameters (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : ∀ v, G.degree v = 3) (htriangleFree : G.CliqueFree 3) :
    2 * triangleCoverNumber (totalGraph G) = 5 * Fintype.card V ∧
      2 * trianglePackingNumber (totalGraph G) = 5 * Fintype.card V := by sorry

end Tuza