module

public import Tuza.Operators
public import Tuza.Certificates

@[expose] public section

/-! # Exact boundary and sharpness examples, checked by kernel reduction

These fixed examples check the representations and prove the sharpness
witness. They do not replace the universal line-graph or total-graph proofs.
-/

namespace Tuza

open SimpleGraph

/-- The four-leaf star, with centre 0 and leaves 1 through 4. -/
def fourLeafStar : SimpleGraph (Fin 5) where
  Adj u v := (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
  symm.symm := by aesop
  loopless.irrefl := by aesop

instance : DecidableRel fourLeafStar.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem completeGraph_fin_four_parameters :
    trianglePackingNumber (completeGraph (Fin 4)) = 1 ∧
      triangleCoverNumber (completeGraph (Fin 4)) = 2 := by
  decide

theorem empty_total_parameters :
    trianglePackingNumber (totalGraph (⊥ : SimpleGraph (Fin 0))) = 0 ∧
      triangleCoverNumber (totalGraph (⊥ : SimpleGraph (Fin 0))) = 0 := by
  have ht : triangles (totalGraph (⊥ : SimpleGraph (Fin 0))) = ∅ := by
    ext t
    constructor
    · intro h
      rw [mem_cliqueFinset_iff, is3Clique_iff] at h
      obtain ⟨a, b, c, _⟩ := h
      exact isEmptyElim a
    · simp
  constructor
  · apply Nat.eq_zero_of_le_zero
    apply Finset.max'_le
    intro k hk
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hk
    have hsub := (Finset.mem_filter.mp hP).2.1
    rw [ht] at hsub
    have hzero : P = ∅ := Finset.subset_empty.mp hsub
    simp [hzero]
  · apply Nat.eq_zero_of_le_zero
    have hcover : IsTriangleCover (totalGraph (⊥ : SimpleGraph (Fin 0))) ∅ := by
      simp [IsTriangleCover, ht]
    simpa using cover_number_le hcover

theorem single_edge_total_parameters :
    trianglePackingNumber (totalGraph (completeGraph (Fin 2))) = 1 ∧
      triangleCoverNumber (totalGraph (completeGraph (Fin 2))) = 1 := by
  decide

theorem triangle_line_parameters :
    trianglePackingNumber (completeGraph (Fin 3)).lineGraph = 1 ∧
      triangleCoverNumber (completeGraph (Fin 3)).lineGraph = 1 := by
  decide

theorem fourLeafStar_line_parameters :
    trianglePackingNumber fourLeafStar.lineGraph = 1 ∧
      triangleCoverNumber fourLeafStar.lineGraph = 2 := by
  decide

/-- An actual finite simple line graph attains the ratio two. -/
theorem lineGraph_factor_sharp :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (_h : DecidableRel G.Adj),
      @trianglePackingNumber _ _ _ G.lineGraph (lineGraphDecidableAdj G) = 1 ∧
      @triangleCoverNumber _ _ _ G.lineGraph (lineGraphDecidableAdj G) = 2 := by
  exact ⟨5, fourLeafStar, inferInstance, fourLeafStar_line_parameters⟩

end Tuza
