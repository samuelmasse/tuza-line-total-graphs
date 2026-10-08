module

public import Tuza.TotalPackets
public import Tuza.LinePackets
public import Tuza.LineCovers
public import Tuza.BalancedColoring
public import Tuza.CompleteGraphPacking
public import Tuza.ColorCover
public import Tuza.CliqueArithmetic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Total-graph covers from global edge colors and local vertex colors -/

namespace Tuza

open Finset SimpleGraph

theorem total_twice_choose_two_add (n : ℕ) : n.choose 2 + n.choose 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

/-- Adding the original vertex to the minority color makes the augmented packet balanced. -/
theorem total_minority_cost (a b : ℕ) (hab : a ≤ b + 2) (hba : b ≤ a + 2) :
    a.choose 2 + b.choose 2 + min a b = cliqueCoverCost (a + b + 1) := by
  wlog h : b ≤ a generalizing a b
  · simpa [Nat.add_comm, Nat.add_left_comm, Nat.min_comm] using this b a hba hab (by omega)
  have hcases : a = b ∨ a = b + 1 ∨ a = b + 2 := by omega
  rcases hcases with ha | ha | ha
  · subst a
    rw [show b + b + 1 = 2 * b + 1 by omega, cliqueCoverCost_odd, min_self]
    exact total_twice_choose_two_add b
  · subst a
    rw [show b + 1 + b + 1 = 2 * (b + 1) by omega, cliqueCoverCost_even]
    rw [min_eq_right (by omega : b ≤ b + 1)]
    simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_sub_cancel]
    have hh := total_twice_choose_two_add b
    nlinarith
  · subst a
    rw [show b + 2 + b + 1 = 2 * (b + 1) + 1 by omega, cliqueCoverCost_odd]
    rw [min_eq_right (by omega : b ≤ b + 2)]
    simp only [show b + 2 = (b + 1) + 1 by omega,
      Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_zero_right]
    have hh := total_twice_choose_two_add b
    nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def totalOriginalEdges : Finset (Sym2 (TotalVertex G)) :=
  G.edgeFinset.image (Sym2.map Sum.inl)

def totalLineMonoEdges (color : G.edgeSet → Bool) : Finset (Sym2 (TotalVertex G)) :=
  (monochromaticEdges G.lineGraph color).image (Sym2.map Sum.inr)

def totalIncidenceColorEdges (color : G.edgeSet → Bool) (vertexColor : V → Bool) :
    Finset (Sym2 (TotalVertex G)) :=
  univ.biUnion fun v =>
    (univ.filter fun e : G.edgeSet => v ∈ e.val ∧ color e = vertexColor v).image
      (fun e => s(Sum.inl v, Sum.inr e))

def totalColorCover (color : G.edgeSet → Bool) (vertexColor : V → Bool) :
    Finset (Sym2 (TotalVertex G)) :=
  totalOriginalEdges G ∪ totalLineMonoEdges G color ∪
    totalIncidenceColorEdges G color vertexColor

@[simp] theorem mk_mem_monochromaticEdges {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (c : W → Bool) (a b : W) :
    s(a,b) ∈ monochromaticEdges H c ↔ H.Adj a b ∧ c a = c b := by
  simp only [monochromaticEdges, mem_filter, mem_edgeFinset, mem_edgeSet]
  constructor
  · intro h
    exact ⟨h.1, h.2 a (by simp) b (by simp)⟩
  · rintro ⟨hab,hc⟩
    refine ⟨hab, ?_⟩
    intro u hu v hv
    simp only [Sym2.mem_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

theorem totalOriginalEdges_subset : totalOriginalEdges G ⊆ (totalGraph G).edgeFinset := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  induction f using Sym2.inductionOn with
  | _ a b => simpa using hf

theorem totalLineMonoEdges_subset (color : G.edgeSet → Bool) :
    totalLineMonoEdges G color ⊆ (totalGraph G).edgeFinset := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  induction f using Sym2.inductionOn with
  | _ a b => simpa using (mk_mem_monochromaticEdges G.lineGraph color a b).mp hf |>.1

theorem totalIncidenceColorEdges_subset (color : G.edgeSet → Bool) (vertexColor : V → Bool) :
    totalIncidenceColorEdges G color vertexColor ⊆ (totalGraph G).edgeFinset := by
  intro e he
  obtain ⟨v,_,hv⟩ := mem_biUnion.mp he
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hv
  simpa using (mem_filter.mp hf).2.1

theorem totalColorCover_covers (color : G.edgeSet → Bool) (vertexColor : V → Bool) :
    IsTriangleCover (totalGraph G) (totalColorCover G color vertexColor) := by
  let c : TotalVertex G → Bool := Sum.elim vertexColor color
  have hmono : monochromaticEdges (totalGraph G) c ⊆ totalColorCover G color vertexColor := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      obtain ⟨hab,hc⟩ := (mk_mem_monochromaticEdges (totalGraph G) c a b).mp he
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          apply mem_union_left
          apply mem_union_left
          exact mem_image.mpr ⟨s(a,b), by simpa using hab, rfl⟩
        | inr b =>
          apply mem_union_right
          apply mem_biUnion.mpr
          refine ⟨a, mem_univ a, mem_image.mpr ⟨b, ?_, rfl⟩⟩
          exact mem_filter.mpr ⟨mem_univ b, hab, hc.symm⟩
      | inr a =>
        cases b with
        | inl b =>
          apply mem_union_right
          apply mem_biUnion.mpr
          refine ⟨b, mem_univ b, mem_image.mpr ⟨a, ?_, ?_⟩⟩
          · exact mem_filter.mpr ⟨mem_univ a, hab, hc⟩
          · exact Sym2.eq_swap
        | inr b =>
          apply mem_union_left
          apply mem_union_right
          exact mem_image.mpr ⟨s(a,b), mk_mem_monochromaticEdges G.lineGraph color a b |>.mpr
            ⟨hab,hc⟩, rfl⟩
  constructor
  · exact union_subset (union_subset (totalOriginalEdges_subset G)
      (totalLineMonoEdges_subset G color)) (totalIncidenceColorEdges_subset G color vertexColor)
  · intro t ht
    obtain ⟨e,heC,het⟩ := not_disjoint_iff.mp ((monochromaticEdges_cover (totalGraph G) c).2 ht)
    exact not_disjoint_iff.mpr ⟨e,hmono heC,het⟩

theorem total_cover_le_color_cost (color : G.edgeSet → Bool) (vertexColor : V → Bool) :
    triangleCoverNumber (totalGraph G) ≤ G.edgeFinset.card +
      (monochromaticEdges G.lineGraph color).card +
      ∑ v, (univ.filter fun e : G.edgeSet => v ∈ e.val ∧ color e = vertexColor v).card := by
  apply (cover_number_le (totalColorCover_covers G color vertexColor)).trans
  have hO : (totalOriginalEdges G).card ≤ G.edgeFinset.card := card_image_le
  have hL : (totalLineMonoEdges G color).card ≤ (monochromaticEdges G.lineGraph color).card :=
    card_image_le
  have hI : (totalIncidenceColorEdges G color vertexColor).card ≤
      ∑ v, (univ.filter fun e : G.edgeSet => v ∈ e.val ∧ color e = vertexColor v).card := by
    apply (card_biUnion_le).trans
    exact sum_le_sum fun v _ => card_image_le
  have hUL := card_union_le (totalOriginalEdges G) (totalLineMonoEdges G color)
  have hUI := card_union_le (totalOriginalEdges G ∪ totalLineMonoEdges G color)
    (totalIncidenceColorEdges G color vertexColor)
  change (totalOriginalEdges G ∪ totalLineMonoEdges G color ∪
    totalIncidenceColorEdges G color vertexColor).card ≤ _
  omega

theorem total_sum_half_degrees_le_edges : (∑ v, G.degree v / 2) ≤ G.edgeFinset.card := by
  have h := sum_le_sum (s := (univ : Finset V)) (fun v _ => Nat.div_mul_le_self (G.degree v) 2)
  rw [← sum_mul, G.sum_degrees_eq_twice_card_edges] at h
  omega

theorem total_colored_incidence_add (color : G.edgeSet → Bool) (v : V) :
    (coloredIncidence G color v false).card + (coloredIncidence G color v true).card =
      G.degree v := by
  let s := (univ : Finset G.edgeSet).filter (fun e => v ∈ e.val)
  have hcard : s.card = G.degree v := by
    rw [← G.card_incidenceFinset_eq_degree v]
    apply card_bij (fun e _ => e.val)
    · intro e he
      exact (G.mem_incidenceFinset (v := v) (e := e.val)).mpr
        ⟨e.property, (mem_filter.mp he).2⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro e he
      have he' := (G.mem_incidenceFinset (v := v) (e := e)).mp he
      exact ⟨⟨e,he'.1⟩, by simpa [s] using he'.2, rfl⟩
  rw [← hcard]
  simpa [coloredIncidence, s, filter_filter, Bool.not_eq_false] using
    (card_filter_add_card_filter_not (s := s) (fun e => color e = false))

theorem total_cover_le_balanced_color (color : G.edgeSet → Bool)
    (hbalance : ∀ v,
      (coloredIncidence G color v false).card ≤ (coloredIncidence G color v true).card + 2 ∧
      (coloredIncidence G color v true).card ≤ (coloredIncidence G color v false).card + 2) :
    triangleCoverNumber (totalGraph G) ≤
      G.edgeFinset.card + ∑ v, cliqueCoverCost (G.degree v + 1) := by
  let vertexColor (v : V) : Bool := if (coloredIncidence G color v false).card ≤
    (coloredIncidence G color v true).card then false else true
  have hmin (v : V) : (coloredIncidence G color v (vertexColor v)).card =
      min (coloredIncidence G color v false).card (coloredIncidence G color v true).card := by
    dsimp [vertexColor]
    split_ifs with h
    · exact (min_eq_left h).symm
    · exact (min_eq_right (by omega)).symm
  have h := total_cover_le_color_cost G color vertexColor
  change triangleCoverNumber (totalGraph G) ≤ G.edgeFinset.card +
    (monochromaticEdges G.lineGraph color).card +
    ∑ v, (coloredIncidence G color v (vertexColor v)).card at h
  rw [line_monochromatic_card, add_assoc, ← sum_add_distrib] at h
  apply h.trans_eq
  congr 1
  apply sum_congr rfl
  intro v _
  rw [hmin, total_minority_cost _ _ (hbalance v).1 (hbalance v).2,
    total_colored_incidence_add]

/-- The remaining two numerical inputs suffice after the actual total packing is assembled. -/
theorem total_satisfiesTuza_of_cover_bound
    (hcover : triangleCoverNumber (totalGraph G) ≤
      G.edgeFinset.card + ∑ v, cliqueCoverCost (G.degree v + 1))
    (hclique : ∀ d, cliqueCoverCost d ≤
      2 * trianglePackingNumber (completeGraph (Fin d))) : SatisfiesTuza (totalGraph G) := by
  have hlocal := sum_le_sum (s := (univ : Finset V)) (fun v _ => hclique (G.degree v))
  have hhalf := total_sum_half_degrees_le_edges G
  have hpack := total_packing_number_ge_edges_add_line G
  have hline := linePacking_lower_bound G
  simp_rw [cliqueCoverCost_succ] at hcover
  rw [sum_add_distrib] at hcover
  rw [← mul_sum] at hlocal
  unfold SatisfiesTuza
  omega

/-- The explicit minority-color cover has the paper's universal total-graph cost. -/
theorem total_cover_upper_bound : triangleCoverNumber (totalGraph G) ≤
    G.edgeFinset.card + ∑ v, cliqueCoverCost (G.degree v + 1) := by
  obtain ⟨color,hcolor⟩ := exists_balanced_edge_coloring G
  apply total_cover_le_balanced_color G color
  intro v
  simpa only [edgeColorDegree, coloredIncidence] using And.intro (hcolor v).2 (hcolor v).1

/-- Tuza's inequality holds for the total graph of every finite simple root graph. -/
theorem totalGraph_satisfiesTuza : SatisfiesTuza (totalGraph G) :=
  total_satisfiesTuza_of_cover_bound G (total_cover_upper_bound G) cliqueCoverCost_le_twice_packing

end Tuza
