import Tuza.CliqueEdges
import Tuza.LinePackets
import Tuza.ColorCover

/-! # Counting a line graph's monochromatic wedge cover -/

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def coloredIncidence (color : G.edgeSet → Bool) (v : V) (c : Bool) : Finset G.edgeSet :=
  univ.filter fun e => v ∈ e.val ∧ color e = c

@[simp] theorem mem_coloredIncidence (color : G.edgeSet → Bool) (v : V) (c : Bool)
    (e : G.edgeSet) : e ∈ coloredIncidence G color v c ↔ v ∈ e.val ∧ color e = c := by
  simp [coloredIncidence]

private theorem mono_mk (color : G.edgeSet → Bool) (e f : G.edgeSet) :
    s(e, f) ∈ monochromaticEdges G.lineGraph color ↔
      G.lineGraph.Adj e f ∧ color e = color f := by
  simp only [monochromaticEdges, mem_filter, mem_edgeFinset, mem_edgeSet]
  constructor
  · rintro ⟨hadj, hc⟩
    exact ⟨hadj, hc e (by simp) f (by simp)⟩
  · rintro ⟨hadj, hc⟩
    refine ⟨hadj, ?_⟩
    intro a ha b hb
    simp only [Sym2.mem_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

theorem monochromaticEdges_eq_packet_union (color : G.edgeSet → Bool) :
    monochromaticEdges G.lineGraph color =
      univ.biUnion (fun p : V × Bool => cliqueEdges (coloredIncidence G color p.1 p.2)) := by
  ext x
  refine Sym2.inductionOn x ?_
  intro e f
  simp only [mono_mk, mem_biUnion, mem_univ, true_and, mk_mem_cliqueEdges,
    mem_coloredIncidence]
  constructor
  · rintro ⟨h, hc⟩
    obtain ⟨hne, v, he, hf⟩ := lineGraph_adj_iff_exists.mp h
    exact ⟨⟨v, color e⟩, hne, ⟨he, rfl⟩, hf, hc.symm⟩
  · rintro ⟨⟨v, c⟩, hne, ⟨he, hce⟩, hf, hcf⟩
    exact ⟨lineGraph_adj_iff_exists.mpr ⟨hne, v, he, hf⟩, hce.trans hcf.symm⟩

theorem colored_packet_edges_disjoint (color : G.edgeSet → Bool)
    {p q : V × Bool} (hpq : p ≠ q) :
    Disjoint (cliqueEdges (coloredIncidence G color p.1 p.2))
      (cliqueEdges (coloredIncidence G color q.1 q.2)) := by
  apply Finset.disjoint_left.mpr
  intro x
  refine Sym2.inductionOn x ?_
  intro e f he hf
  obtain ⟨hne, hep, hfp⟩ := mk_mem_cliqueEdges.mp he
  obtain ⟨_, heq, hfq⟩ := mk_mem_cliqueEdges.mp hf
  rw [mem_coloredIncidence] at hep hfp heq hfq
  apply hpq
  exact Prod.ext (common_endpoint_unique hne hep.1 hfp.1 heq.1 hfq.1)
    (hep.2.symm.trans heq.2)

theorem line_monochromatic_card (color : G.edgeSet → Bool) :
    (monochromaticEdges G.lineGraph color).card =
      ∑ v, ((coloredIncidence G color v false).card.choose 2 +
        (coloredIncidence G color v true).card.choose 2) := by
  rw [monochromaticEdges_eq_packet_union, card_biUnion]
  · simp only [cliqueEdges_card]
    rw [Fintype.sum_prod_type]
    simp [Nat.add_comm]
  · intro p _ q _ hpq
    exact colored_packet_edges_disjoint G color hpq

theorem line_cover_le_color_cost (color : G.edgeSet → Bool) :
    triangleCoverNumber G.lineGraph ≤
      ∑ v, ((coloredIncidence G color v false).card.choose 2 +
        (coloredIncidence G color v true).card.choose 2) := by
  rw [← line_monochromatic_card]
  exact cover_number_le (monochromaticEdges_cover G.lineGraph color)

end Tuza
