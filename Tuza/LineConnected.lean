import Tuza.LineColorBounds
import Tuza.LineTriangleFree

/-! # Assembly of the connected-root line-graph inequality -/

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem line_sum_clique_bound
    (hclique : ∀ n, cliqueCoverCost n ≤ 2 * trianglePackingNumber (completeGraph (Fin n))) :
    (∑ v, cliqueCoverCost (G.degree v)) ≤
      2 * ∑ v, trianglePackingNumber (completeGraph (Fin (G.degree v))) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun v _ => hclique (G.degree v)

theorem line_sum_clique_slack
    (hclique : ∀ n, cliqueCoverCost n ≤ 2 * trianglePackingNumber (completeGraph (Fin n)))
    (base : V)
    (hbase : cliqueCoverCost (G.degree base) + 2 ≤
      2 * trianglePackingNumber (completeGraph (Fin (G.degree base)))) :
    (∑ v, cliqueCoverCost (G.degree v)) + 2 ≤
      2 * ∑ v, trianglePackingNumber (completeGraph (Fin (G.degree v))) := by
  classical
  calc
    _ = ∑ v, (cliqueCoverCost (G.degree v) + if v = base then 2 else 0) := by
      rw [sum_add_distrib]; simp
    _ ≤ ∑ v, 2 * trianglePackingNumber (completeGraph (Fin (G.degree v))) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v = base
      · subst v
        simp only [↓reduceIte]
        exact hbase
      · simpa only [hv, ↓reduceIte, add_zero] using hclique (G.degree v)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The three mechanisms close every connected root: odd-degree balance,
triangle-free local cuts, or an Euler seam absorbed by packing slack. -/
theorem connected_line_satisfiesTuza_of_local_bounds (hconn : G.Connected)
    (hclique : ∀ n, cliqueCoverCost n ≤ 2 * trianglePackingNumber (completeGraph (Fin n)))
    (hslack : ∀ n, Even n → 6 ≤ n → cliqueCoverCost n + 2 ≤
      2 * trianglePackingNumber (completeGraph (Fin n)))
    (haugment : (∀ v, G.degree v = 2 ∨ G.degree v = 4) → ¬G.CliqueFree 3 →
      (∑ v, trianglePackingNumber (completeGraph (Fin (G.degree v)))) + 1 ≤
        trianglePackingNumber G.lineGraph) :
    SatisfiesTuza G.lineGraph := by
  classical
  have hs := line_sum_clique_bound G hclique
  have hp := linePacking_lower_bound G
  unfold SatisfiesTuza
  by_cases ho : ∃ v, Odd (G.degree v)
  · have hc := line_odd_cover_bound G hconn ho
    omega
  have heven : ∀ v, Even (G.degree v) :=
    fun v => Nat.not_odd_iff_even.mp (fun hv => ho ⟨v, hv⟩)
  by_cases hfree : G.CliqueFree 3
  · have hc := line_triangleFree_cover_bound G hfree
    omega
  have hc := line_eulerian_cover_bound G hconn heven
  by_cases hlarge : ∃ v, 6 ≤ G.degree v
  · obtain ⟨v, hv⟩ := hlarge
    have hss := line_sum_clique_slack G hclique v (hslack _ (heven v) hv)
    omega
  have htri := hfree
  simp only [CliqueFree, not_forall, not_not] at htri
  obtain ⟨t, ht⟩ := htri
  obtain ⟨a, b, c, hab, _, _, _⟩ := is3Clique_iff.mp ht
  letI : Nontrivial V := ⟨⟨a, b, hab.ne⟩⟩
  have hdeg (v : V) : G.degree v = 2 ∨ G.degree v = 4 := by
    have hlo := hconn.preconnected.degree_pos_of_nontrivial v
    have hhi : G.degree v < 6 := Nat.lt_of_not_ge (fun hv => hlarge ⟨v, hv⟩)
    obtain ⟨r, hr⟩ := heven v
    omega
  have hp' := haugment hdeg hfree
  omega

end Tuza
