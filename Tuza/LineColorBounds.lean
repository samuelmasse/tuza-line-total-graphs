module

public import Tuza.LineCovers
public import Tuza.LineArithmetic
public import Tuza.BalancedColoring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem line_cover_le_edge_color_cost (color : G.edgeSet → Bool) :
    triangleCoverNumber G.lineGraph ≤ ∑ v,
      ((edgeColorDegree G color v true).choose 2 +
        (edgeColorDegree G color v false).choose 2) := by
  have h := line_cover_le_color_cost G color
  change triangleCoverNumber G.lineGraph ≤ ∑ v,
    ((edgeColorDegree G color v false).choose 2 +
      (edgeColorDegree G color v true).choose 2) at h
  apply h.trans_eq
  exact Finset.sum_congr rfl (fun _ _ => Nat.add_comm _ _)

theorem line_cover_bound_of_balanced (color : G.edgeSet → Bool)
    (hbal : ∀ v, edgeColorDegree G color v true ≤ edgeColorDegree G color v false + 1 ∧
      edgeColorDegree G color v false ≤ edgeColorDegree G color v true + 1) :
    triangleCoverNumber G.lineGraph ≤ ∑ v, cliqueCoverCost (G.degree v) := by
  apply (line_cover_le_edge_color_cost G color).trans
  apply Finset.sum_le_sum
  intro v _
  rw [balanced_choose_cost _ _ (hbal v).1 (hbal v).2, edgeColorDegree_add]

theorem line_odd_cover_bound (hconn : G.Connected) (ho : ∃ v, Odd (G.degree v)) :
    triangleCoverNumber G.lineGraph ≤ ∑ v, cliqueCoverCost (G.degree v) := by
  obtain ⟨color, hc⟩ := exists_odd_edge_coloring G hconn ho
  exact line_cover_bound_of_balanced G color (fun v => ⟨(hc v).1, (hc v).2.1⟩)

theorem line_eulerian_cover_bound (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) :
    triangleCoverNumber G.lineGraph ≤ (∑ v, cliqueCoverCost (G.degree v)) + 1 := by
  classical
  obtain ⟨base⟩ := hconn.nonempty
  obtain ⟨color, hc⟩ := exists_eulerian_edge_coloring G hconn heven base
  apply (line_cover_le_edge_color_cost G color).trans
  calc
    _ ≤ ∑ v, (cliqueCoverCost (G.degree v) + if v = base then 1 else 0) := by
      apply Finset.sum_le_sum
      intro v _
      have hv := hc v
      by_cases hbase : v = base
      · subst v
        simp only [↓reduceIte] at hv ⊢
        have h1 : edgeColorDegree G color base true ≤ edgeColorDegree G color base false + 2 := by
          split_ifs at hv <;> omega
        have h2 : edgeColorDegree G color base false ≤ edgeColorDegree G color base true + 2 := by
          split_ifs at hv <;> omega
        simpa only [edgeColorDegree_add] using seam_choose_cost _ _ h1 h2
      · simp only [hbase, ↓reduceIte, ite_self, add_zero] at hv ⊢
        have h1 : edgeColorDegree G color v true ≤ edgeColorDegree G color v false + 1 := by omega
        have h2 : edgeColorDegree G color v false ≤ edgeColorDegree G color v true + 1 := by omega
        rw [balanced_choose_cost _ _ h1 h2, edgeColorDegree_add]
    _ = _ := by rw [sum_add_distrib]; simp

end Tuza
