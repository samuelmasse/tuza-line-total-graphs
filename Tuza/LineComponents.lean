import Tuza.PackingTools
import Tuza.Operators
import Tuza.BalancedColoring

/-! # Assembling line-graph certificates across root components -/

namespace Tuza

open SimpleGraph Finset

private theorem map_mem_triangleEdges {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : SimpleGraph W} [DecidableRel H.Adj] (f : V ↪ W)
    (hf : ∀ {a b}, G.Adj a b → H.Adj (f a) (f b)) {e : Sym2 V} {t : Finset V}
    (he : e ∈ triangleEdges G t) : Sym2.map f e ∈ triangleEdges H (t.map f) := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    obtain ⟨hab, ha, hb⟩ := mk_mem_triangleEdges.mp he
    exact mk_mem_triangleEdges.mpr ⟨hf hab, by simpa using ha, by simpa using hb⟩

/-- Tuza certificates assemble over a finite disjoint partition into induced graphs.
The hypotheses include actual inclusion maps, edge closure, and vertex coverage. -/
theorem satisfiesTuza_of_graph_partition {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : I → Type*) [∀ i, Fintype (U i)] [∀ i, DecidableEq (U i)]
    (H : (i : I) → SimpleGraph (U i)) [∀ i, DecidableRel (H i).Adj]
    (f : (i : I) → H i ↪g G)
    (hsurj : ∀ v, ∃ i x, f i x = v)
    (hclosed : ∀ i x y, G.Adj (f i x) y → ∃ z, f i z = y)
    (hdisj : ∀ i j x y, f i x = f j y → i = j)
    (htuza : ∀ i, SatisfiesTuza (H i)) : SatisfiesTuza G := by
  classical
  have hex i := (satisfiesTuza_iff_certificates (G := H i)).mp (htuza i)
  choose P₀ C₀ hP₀ hC₀ hsize using hex
  let P i := (P₀ i).map ⟨Finset.map (f i).toEmbedding,
    Finset.map_injective (f i).toEmbedding⟩
  let C i := (C₀ i).map (f i).toEmbedding.sym2Map
  have hP i : IsTrianglePacking G (P i) :=
    packing_map (f i).toEmbedding (fun h => (f i).map_adj_iff.mpr h) (hP₀ i)
  have hvertex i {t : Finset V} (ht : t ∈ P i) {a : V} (ha : a ∈ t) :
      ∃ x, f i x = a := by
    obtain ⟨t₀, _, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨x, _, hx⟩ := Finset.mem_map.mp ha
    exact ⟨x, hx⟩
  have hcross i (_ : i ∈ (Finset.univ : Finset I)) j (_ : j ∈ Finset.univ)
      (hne : i ≠ j) (t : Finset V) (ht : t ∈ P i) (u : Finset V) (hu : u ∈ P j) :
      Disjoint (triangleEdges G t) (triangleEdges G u) := by
    apply Finset.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro het heu
      obtain ⟨x, hx⟩ := hvertex i ht (mk_mem_triangleEdges.mp het).2.1
      obtain ⟨y, hy⟩ := hvertex j hu (mk_mem_triangleEdges.mp heu).2.1
      exact hne (hdisj i j x y (hx.trans hy.symm))
  have hC : IsTriangleCover G (Finset.univ.biUnion C) := by
    constructor
    · intro e he
      obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
      obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_map.mp hei
      have heG := (hC₀ i).1 he₀
      induction e₀ using Sym2.inductionOn with
      | hf a b =>
        have hab : (H i).Adj a b := by simpa using heG
        simpa using (f i).map_adj_iff.mpr hab
    · intro t ht
      rw [mem_cliqueFinset_iff, is3Clique_iff] at ht
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := ht
      obtain ⟨i, x, rfl⟩ := hsurj a
      obtain ⟨y, rfl⟩ := hclosed i x b hab
      obtain ⟨z, rfl⟩ := hclosed i x c hac
      have hlocal : ({x, y, z} : Finset (U i)) ∈ triangles (H i) := by
        rw [mem_cliqueFinset_iff, is3Clique_iff]
        exact ⟨x, y, z, (f i).map_adj_iff.mp hab, (f i).map_adj_iff.mp hac,
          (f i).map_adj_iff.mp hbc, rfl⟩
      obtain ⟨e, heC, het⟩ := Finset.not_disjoint_iff.mp ((hC₀ i).2 hlocal)
      apply Finset.not_disjoint_iff.mpr
      refine ⟨Sym2.map (f i) e, ?_, ?_⟩
      · apply Finset.mem_biUnion.mpr
        exact ⟨i, Finset.mem_univ _, Finset.mem_map.mpr ⟨e, heC, rfl⟩⟩
      · simpa using map_mem_triangleEdges (f i).toEmbedding
          (fun h => (f i).map_adj_iff.mpr h) het
  have hpack := packing_biUnion P (fun i _ => hP i) hcross
  apply satisfiesTuza_of_certificates hpack hC
  calc
    (Finset.univ.biUnion C).card ≤ ∑ i, (C i).card := Finset.card_biUnion_le
    _ ≤ ∑ i, 2 * (P i).card := by
      apply Finset.sum_le_sum
      intro i _
      simpa [C, P] using hsize i
    _ = 2 * (Finset.univ.biUnion P).card := by
      rw [packing_biUnion_card P (fun i _ => hP i) hcross]
      simp [Finset.mul_sum]

variable {V : Type*} (G : SimpleGraph V)

/-- The actual inclusion of a root component induces an embedding of its line graph. -/
def componentLineEmbedding (K : G.ConnectedComponent) :
    K.toSimpleGraph.lineGraph ↪g G.lineGraph :=
  (K.toSimpleGraph_hom.toCopy Subtype.val_injective).toLineGraphEmbedding

theorem componentLine_mem (K : G.ConnectedComponent) (e : K.toSimpleGraph.edgeSet)
    {v : V} (hv : v ∈ ((componentLineEmbedding G K) e).val) : v ∈ K.supp := by
  change v ∈ Sym2.map Subtype.val e.val at hv
  obtain ⟨w, _, rfl⟩ := Sym2.mem_map.mp hv
  exact w.property

theorem componentLine_lift (K : G.ConnectedComponent) (e : G.edgeSet) {v : V}
    (hvK : v ∈ K.supp) (hve : v ∈ e.val) :
    ∃ eK, componentLineEmbedding G K eK = e := by
  obtain ⟨w, he⟩ := Sym2.mem_iff_exists.mp hve
  have hadj : G.Adj v w := by simpa [he] using e.property
  have hwK : w ∈ K.supp := (K.mem_supp_congr_adj hadj).mp hvK
  let eK : K.toSimpleGraph.edgeSet := ⟨s(⟨v, hvK⟩, ⟨w, hwK⟩), hadj⟩
  refine ⟨eK, Subtype.ext ?_⟩
  change Sym2.map Subtype.val s((⟨v, hvK⟩ : K), ⟨w, hwK⟩) = e.val
  simpa using he.symm

attribute [local instance] Classical.propDecidable

/-- Line-graph Tuza inequalities for all root components imply the full finite-root
inequality, including empty roots and isolated vertices. -/
theorem line_satisfiesTuza_of_components [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : ∀ K : G.ConnectedComponent, SatisfiesTuza K.toSimpleGraph.lineGraph) :
    SatisfiesTuza G.lineGraph := by
  classical
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  apply satisfiesTuza_of_graph_partition G.lineGraph
    (fun K : G.ConnectedComponent => K.toSimpleGraph.edgeSet)
    (fun K => K.toSimpleGraph.lineGraph) (componentLineEmbedding G)
    ?_ ?_ ?_ h
  · intro e
    obtain ⟨a, ha⟩ : ∃a, a ∈ e.val := by
      obtain ⟨e, he⟩ := e
      induction e using Sym2.inductionOn with
      | hf a b => exact ⟨a, by simp⟩
    obtain ⟨eK, heK⟩ := componentLine_lift G (G.connectedComponentMk a) e rfl ha
    exact ⟨G.connectedComponentMk a, eK, heK⟩
  · intro K e f hadj
    obtain ⟨_, v, hve, hvf⟩ := lineGraph_adj_iff_exists.mp hadj
    exact componentLine_lift G K f (componentLine_mem G K e hve) hvf
  · intro K L e f hef
    obtain ⟨v, hv⟩ : ∃v, v ∈ (componentLineEmbedding G K e).val := by
      induction (componentLineEmbedding G K e).val using Sym2.inductionOn with
      | hf a b => exact ⟨a, by simp⟩
    exact ConnectedComponent.eq_of_common_vertex (componentLine_mem G K e hv)
      (componentLine_mem G L f (hef ▸ hv))

end Tuza
