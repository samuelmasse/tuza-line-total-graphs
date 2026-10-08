module

public import Tuza.Operators

@[expose] public section

/-! # Unique wedge ownership and the line-graph triangle classification -/

namespace Tuza

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two distinct root edges have at most one common endpoint. -/
theorem common_endpoint_unique {e f : G.edgeSet} (hne : e ≠ f)
    {u v : V} (hue : u ∈ e.val) (huf : u ∈ f.val)
    (hve : v ∈ e.val) (hvf : v ∈ f.val) : u = v := by
  by_contra huv
  exact hne (Subtype.ext (Sym2.eq_of_ne_mem huv hue hve huf hvf))

/-- Every edge of the line graph belongs to exactly one incidence packet. -/
theorem lineGraph_edge_unique_owner {e f : G.edgeSet} (h : G.lineGraph.Adj e f) :
    ∃! v, v ∈ e.val ∧ v ∈ f.val := by
  obtain ⟨hne, v, he, hf⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp h
  exact ⟨v, ⟨he, hf⟩, fun w hw => common_endpoint_unique hne hw.1 hw.2 he hf⟩

/-- Three pairwise adjacent root edges are a star or the edges of a root triangle.

The second alternative fixes the ordering of the three edges as `ab, ac, bc`.
This is the complete classification, with no triangle-free hypothesis.
-/
theorem lineGraph_triangle_classification {e f g : G.edgeSet}
    (hef : G.lineGraph.Adj e f) (heg : G.lineGraph.Adj e g)
    (hfg : G.lineGraph.Adj f g) :
    (∃ a, a ∈ e.val ∧ a ∈ f.val ∧ a ∈ g.val) ∨
    (∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
      e.val = s(a, b) ∧ f.val = s(a, c) ∧ g.val = s(b, c)) := by
  classical
  obtain ⟨hne, a, hae, haf⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp hef
  by_cases hag : a ∈ g.val
  · exact Or.inl ⟨a, hae, haf, hag⟩
  · right
    obtain ⟨b, he⟩ := Sym2.mem_iff_exists.mp hae
    obtain ⟨c, hf⟩ := Sym2.mem_iff_exists.mp haf
    have hab : G.Adj a b := by simpa [he] using e.property
    have hac : G.Adj a c := by simpa [hf] using f.property
    have hbc : b ≠ c := by
      intro h
      apply hne
      apply Subtype.ext
      simp [he, hf, h]
    have hbg : b ∈ g.val := by
      obtain ⟨_, x, hxe, hxg⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp heg
      rw [he, Sym2.mem_iff] at hxe
      rcases hxe with rfl | rfl
      · exact False.elim (hag hxg)
      · exact hxg
    have hcg : c ∈ g.val := by
      obtain ⟨_, x, hxf, hxg⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp hfg
      rw [hf, Sym2.mem_iff] at hxf
      rcases hxf with rfl | rfl
      · exact False.elim (hag hxg)
      · exact hxg
    have hg : g.val = s(b, c) := (Sym2.mem_and_mem_iff hbc).mp ⟨hbg, hcg⟩
    have hbcAdj : G.Adj b c := by simpa [hg] using g.property
    exact ⟨a, b, c, hab.ne, hac.ne, hbc, hab, hac, hbcAdj, he, hf, hg⟩

/-- The two branches of the classification cannot hold at the same time. -/
theorem triangle_edges_no_common_endpoint {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬∃ x, x ∈ s(a, b) ∧ x ∈ s(a, c) ∧ x ∈ s(b, c) := by
  simp only [Sym2.mem_iff]
  aesop

end Tuza
