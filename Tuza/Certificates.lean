import Tuza.Definitions

/-! # Converting explicit packing and cover witnesses into numerical bounds -/

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem packing_card_le {P : Finset (Finset V)} (hP : IsTrianglePacking G P) :
    P.card ≤ trianglePackingNumber G := by
  apply Finset.le_max'
  apply Finset.mem_image.mpr
  exact ⟨P, by simpa [trianglePackings] using And.intro hP.1 hP, rfl⟩

theorem cover_number_le {C : Finset (Sym2 V)} (hC : IsTriangleCover G C) :
    triangleCoverNumber G ≤ C.card := by
  apply Finset.min'_le
  apply Finset.mem_image.mpr
  exact ⟨C, by simpa [triangleCovers] using And.intro hC.1 hC, rfl⟩

theorem exists_maximum_packing (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P, IsTrianglePacking G P ∧ P.card = trianglePackingNumber G := by
  have h := Finset.max'_mem (trianglePackingSizes G) (trianglePackingSizes_nonempty G)
  obtain ⟨P, hP, hcard⟩ := Finset.mem_image.mp h
  exact ⟨P, (Finset.mem_filter.mp hP).2, hcard⟩

theorem exists_minimum_cover (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ C, IsTriangleCover G C ∧ C.card = triangleCoverNumber G := by
  have h := Finset.min'_mem (triangleCoverSizes G) (triangleCoverSizes_nonempty G)
  obtain ⟨C, hC, hcard⟩ := Finset.mem_image.mp h
  exact ⟨C, (Finset.mem_filter.mp hC).2, hcard⟩

/-- One cover and one packing in the same graph suffice for Tuza's inequality. -/
theorem satisfiesTuza_of_certificates {P : Finset (Finset V)} {C : Finset (Sym2 V)}
    (hP : IsTrianglePacking G P) (hC : IsTriangleCover G C)
    (hsize : C.card ≤ 2 * P.card) : SatisfiesTuza G := by
  have hp := packing_card_le hP
  have hc := cover_number_le hC
  unfold SatisfiesTuza
  omega

/-- Explicit compatible certificates are equivalent to the numerical inequality. -/
theorem satisfiesTuza_iff_certificates : SatisfiesTuza G ↔
    ∃ P C, IsTrianglePacking G P ∧ IsTriangleCover G C ∧ C.card ≤ 2 * P.card := by
  constructor
  · intro h
    obtain ⟨P, hP, hp⟩ := exists_maximum_packing G
    obtain ⟨C, hC, hc⟩ := exists_minimum_cover G
    exact ⟨P, C, hP, hC, by simpa [hp, hc, SatisfiesTuza] using h⟩
  · rintro ⟨P, C, hP, hC, hsize⟩
    exact satisfiesTuza_of_certificates hP hC hsize

/-- Each packed triangle requires a different edge of any cover. -/
theorem packing_card_le_cover_card {P : Finset (Finset V)} {C : Finset (Sym2 V)}
    (hP : IsTrianglePacking G P) (hC : IsTriangleCover G C) : P.card ≤ C.card := by
  classical
  have hit : ∀ t : P, ∃ e, e ∈ C ∧ e ∈ triangleEdges G t.val := by
    intro t
    exact Finset.not_disjoint_iff.mp (hC.2 (hP.1 t.property))
  choose edge hedge using hit
  let f : P → C := fun t => ⟨edge t, (hedge t).1⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro t u h
  apply Subtype.ext
  by_contra hne
  have disj := hP.2 t.property u.property hne
  have heq : edge t = edge u := congrArg Subtype.val h
  exact Finset.disjoint_left.mp disj (hedge t).2 (heq ▸ (hedge u).2)

theorem packing_number_le_cover_number (G : SimpleGraph V) [DecidableRel G.Adj] :
    trianglePackingNumber G ≤ triangleCoverNumber G := by
  obtain ⟨P, hP, hp⟩ := exists_maximum_packing G
  obtain ⟨C, hC, hc⟩ := exists_minimum_cover G
  simpa [hp, hc] using packing_card_le_cover_card hP hC

end Tuza
