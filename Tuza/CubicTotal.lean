module

public import Tuza.TotalPackets
public import Tuza.LinePackets
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.Hall.Finite

@[expose] public section

/-! # Cubic total graphs: a distinct incident-edge assignment and the exact bounds

The sharp cover uses Hall's theorem, as in the revised paper's cubic argument.
An injective choice of one incident root edge per vertex exists whenever the minimum
degree is at least two. In a cubic packet, select that incidence edge and the wedge
between the other two edge-vertices. Select the original root edges outside the
assignment image. The resulting cover has at most `|E| + |V|` edges; triangle-freeness
rules out the two kinds of triangles outside packets and bridges. The bridge/local
packing lower bound and the degree-sum identity then force both exact parameters.
-/

namespace Tuza

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every graph of minimum degree at least two has distinct incident-edge representatives. -/
theorem total_exists_incident_edge_assignment (hdeg : ∀ v, 2 ≤ G.degree v) :
    ∃ pick : V ↪ G.edgeSet, ∀ v, v ∈ (pick v).val := by
  classical
  have hhall (S : Finset V) : S.card ≤ (S.biUnion (fun v => G.incidenceFinset v)).card := by
    let D := (univ : Finset G.Dart).filter (fun d => d.fst ∈ S)
    have hD : D.card = ∑ v ∈ S, G.degree v := by
      rw [card_eq_sum_card_fiberwise (f := fun d : G.Dart => d.fst) (t := S)
        (by intro d hd; exact (mem_filter.mp hd).2)]
      apply sum_congr rfl
      intro v hv
      have hf : D.filter (fun d => d.fst = v) = univ.filter (fun d : G.Dart => d.fst = v) := by
        ext d
        simp only [D, mem_filter, mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨h ▸ hv, h⟩
      rw [hf, G.dart_fst_fiber_card_eq_degree]
    have hmaps : (D : Set G.Dart).MapsTo SimpleGraph.Dart.edge
        (S.biUnion (fun v => G.incidenceFinset v)) := by
      intro d hd
      apply mem_biUnion.mpr
      refine ⟨d.fst, (mem_filter.mp hd).2, ?_⟩
      rw [mem_incidenceFinset]
      exact ⟨d.edge_mem, by simp [SimpleGraph.Dart.edge]⟩
    have hupper : D.card ≤ (S.biUnion (fun v => G.incidenceFinset v)).card * 2 := by
      rw [card_eq_sum_card_fiberwise hmaps]
      calc
        _ ≤ ∑ _e ∈ S.biUnion (fun v => G.incidenceFinset v), 2 := by
          apply sum_le_sum
          intro e he
          obtain ⟨v,_,hev⟩ := mem_biUnion.mp he
          have heG : e ∈ G.edgeSet := G.incidenceSet_subset v
            ((G.mem_incidenceFinset (v := v) (e := e)).mp hev)
          rw [← G.dart_edge_fiber_card e heG]
          apply card_le_card
          exact filter_subset_filter _ (filter_subset _ _)
        _ = _ := by simp
    have hlower : S.card * 2 ≤ D.card := by
      rw [hD]
      calc
        S.card * 2 = ∑ _v ∈ S, 2 := by simp
        _ ≤ _ := sum_le_sum (fun v _ => hdeg v)
    omega
  obtain ⟨f,hf,hmem⟩ := (all_card_le_biUnion_card_iff_existsInjective'
    (fun v => G.incidenceFinset v)).mp hhall
  let pick : V ↪ G.edgeSet := ⟨fun v => ⟨f v, G.incidenceSet_subset v
    ((G.mem_incidenceFinset (v := v) (e := f v)).mp (hmem v))⟩,
    fun _ _ h => hf (congrArg Subtype.val h)⟩
  refine ⟨pick, fun v => ?_⟩
  exact (G.edge_mem_incidenceSet_iff).mp
    ((G.mem_incidenceFinset (v := v) (e := f v)).mp (hmem v))

theorem cubic_total_packing_lower_bound (hdeg : ∀ v, G.degree v = 3) :
    5 * Fintype.card V ≤ 2 * trianglePackingNumber (totalGraph G) := by
  have hp := total_packing_number_ge_edges_add_line G
  have hl := linePacking_lower_bound G
  have hK : trianglePackingNumber (completeGraph (Fin 3)) = 1 := by decide
  have hlocal (v : V) : trianglePackingNumber (completeGraph (Fin (G.degree v))) = 1 := by
    rw [complete_packing_number_eq (Equiv.cast (congrArg Fin (hdeg v)))]
    exact hK
  simp_rw [hlocal] at hl
  simp only [sum_const, card_univ, smul_eq_mul, mul_one] at hl
  have hd := G.sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hd
  simp only [sum_const, card_univ, smul_eq_mul] at hd
  omega

def totalIncidentEdges (v : V) : Finset G.edgeSet :=
  univ.filter fun e => v ∈ e.val

@[simp] theorem mem_totalIncidentEdges (v : V) (e : G.edgeSet) :
    e ∈ totalIncidentEdges G v ↔ v ∈ e.val := by simp [totalIncidentEdges]

theorem totalIncidentEdges_card (v : V) : (totalIncidentEdges G v).card = G.degree v := by
  rw [← G.card_incidenceFinset_eq_degree v]
  apply card_bij (fun e _ => e.val)
  · intro e he
    exact (G.mem_incidenceFinset (v := v) (e := e.val)).mpr
      ⟨e.property, (mem_totalIncidentEdges G v e).mp he⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro e he
    have he' := (G.mem_incidenceFinset (v := v) (e := e)).mp he
    exact ⟨⟨e,he'.1⟩, by simpa using he'.2, rfl⟩

theorem cubic_remaining_pair (hdeg : ∀ v, G.degree v = 3)
    (pick : V ↪ G.edgeSet) (hpick : ∀ v, v ∈ (pick v).val) (v : V) :
    ∃ a b : G.edgeSet, a ≠ b ∧ a ≠ pick v ∧ b ≠ pick v ∧
      (totalIncidentEdges G v).erase (pick v) = {a,b} := by
  have hp : pick v ∈ totalIncidentEdges G v := (mem_totalIncidentEdges G v _).mpr (hpick v)
  have hc : ((totalIncidentEdges G v).erase (pick v)).card = 2 := by
    rw [card_erase_of_mem hp, totalIncidentEdges_card, hdeg]
  obtain ⟨a,b,hab,heq⟩ := card_eq_two.mp hc
  have ha : a ∈ (totalIncidentEdges G v).erase (pick v) := by rw [heq]; simp
  have hb : b ∈ (totalIncidentEdges G v).erase (pick v) := by rw [heq]; simp
  exact ⟨a,b,hab,(mem_erase.mp ha).1,(mem_erase.mp hb).1,heq⟩

set_option maxHeartbeats 4000000 in
/-- A distinct incident-edge assignment gives the sharp cubic total-graph cover. -/
theorem cubic_total_cover_of_assignment (hdeg : ∀ v, G.degree v = 3)
    (htriangleFree : G.CliqueFree 3) (pick : V ↪ G.edgeSet)
    (hpick : ∀ v, v ∈ (pick v).val) :
    triangleCoverNumber (totalGraph G) ≤ G.edgeFinset.card + Fintype.card V := by
  classical
  choose a b hab hpa hpb hrem using cubic_remaining_pair G hdeg pick hpick
  have hai (v : V) : v ∈ (a v).val := by
    apply (mem_totalIncidentEdges G v _).mp
    apply mem_of_mem_erase
    rw [hrem v]
    simp
  have hbi (v : V) : v ∈ (b v).val := by
    apply (mem_totalIncidentEdges G v _).mp
    apply mem_of_mem_erase
    rw [hrem v]
    simp
  let R : Finset (Sym2 V) := univ.image (fun v => (pick v).val)
  let O : Finset (Sym2 (TotalVertex G)) :=
    (G.edgeFinset \ R).image (Sym2.map (Sum.inl : V → TotalVertex G))
  let I : Finset (Sym2 (TotalVertex G)) := univ.image (fun v => s(Sum.inl v, Sum.inr (pick v)))
  let W : Finset (Sym2 (TotalVertex G)) := univ.image (fun v => s(Sum.inr (a v), Sum.inr (b v)))
  let C : Finset (Sym2 (TotalVertex G)) := O ∪ I ∪ W
  have hO : O ⊆ (totalGraph G).edgeFinset := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    have hfG := (mem_sdiff.mp hf).1
    induction f using Sym2.inductionOn with
    | _ x y => simpa using hfG
  have hI : I ⊆ (totalGraph G).edgeFinset := by
    intro e he
    obtain ⟨v,_,rfl⟩ := mem_image.mp he
    simpa using hpick v
  have hW : W ⊆ (totalGraph G).edgeFinset := by
    intro e he
    obtain ⟨v,_,rfl⟩ := mem_image.mp he
    have hadj := lineGraph_adj_iff_exists.mpr ⟨hab v, v, hai v, hbi v⟩
    simpa using hadj
  have hC : C ⊆ (totalGraph G).edgeFinset := union_subset (union_subset hO hI) hW
  have hit {t : Finset (TotalVertex G)} {x y : TotalVertex G}
      (hx : x ∈ t) (hy : y ∈ t) (hxy : s(x,y) ∈ C) :
      ¬Disjoint C (triangleEdges (totalGraph G) t) := by
    exact not_disjoint_iff.mpr ⟨s(x,y),hxy,
      mk_mem_triangleEdges.mpr ⟨by simpa using hC hxy,hx,hy⟩⟩
  have hitI {t : Finset (TotalVertex G)} (v : V)
      (hv : Sum.inl v ∈ t) (hp : Sum.inr (pick v) ∈ t) :
      ¬Disjoint C (triangleEdges (totalGraph G) t) := by
    apply hit hv hp
    exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨v,mem_univ _,rfl⟩))
  have hitW {t : Finset (TotalVertex G)} (v : V)
      (ha : Sum.inr (a v) ∈ t) (hb : Sum.inr (b v) ∈ t) :
      ¬Disjoint C (triangleEdges (totalGraph G) t) := by
    apply hit ha hb
    exact mem_union_right _ (mem_image.mpr ⟨v,mem_univ _,rfl⟩)
  have hitBridge {t : Finset (TotalVertex G)} (u v : V) (e : G.edgeSet)
      (huv : G.Adj u v) (hue : u ∈ e.val) (hve : v ∈ e.val)
      (hu : Sum.inl u ∈ t) (hv : Sum.inl v ∈ t) (he : Sum.inr e ∈ t) :
      ¬Disjoint C (triangleEdges (totalGraph G) t) := by
    have heq : e.val = s(u,v) := (Sym2.mem_and_mem_iff huv.ne).mp ⟨hue,hve⟩
    by_cases hR : s(u,v) ∈ R
    · obtain ⟨w,_,hw⟩ := mem_image.mp hR
      have hp : pick w = e := Subtype.ext (hw.trans heq.symm)
      have hwmem : w = u ∨ w = v := by simpa [hp,heq] using hpick w
      rcases hwmem with hwmem | hwmem
      · exact hitI w (hwmem.symm ▸ hu) (hp.symm ▸ he)
      · exact hitI w (hwmem.symm ▸ hv) (hp.symm ▸ he)
    · apply hit hu hv
      apply mem_union_left
      apply mem_union_left
      exact mem_image.mpr ⟨s(u,v),mem_sdiff.mpr ⟨by simpa using huv,hR⟩,rfl⟩
  have hitPacket2 {t : Finset (TotalVertex G)} (v : V) (e f : G.edgeSet)
      (hef : e ≠ f) (hve : v ∈ e.val) (hvf : v ∈ f.val)
      (hv : Sum.inl v ∈ t) (he : Sum.inr e ∈ t) (hf : Sum.inr f ∈ t) :
      ¬Disjoint C (triangleEdges (totalGraph G) t) := by
    by_cases hep : e = pick v
    · exact hitI v hv (hep ▸ he)
    by_cases hfp : f = pick v
    · exact hitI v hv (hfp ▸ hf)
    have heab : e = a v ∨ e = b v := by
      have hh : e ∈ (totalIncidentEdges G v).erase (pick v) :=
        mem_erase.mpr ⟨hep,(mem_totalIncidentEdges G v e).mpr hve⟩
      rw [hrem v] at hh
      simpa only [mem_insert,mem_singleton] using hh
    have hfab : f = a v ∨ f = b v := by
      have hh : f ∈ (totalIncidentEdges G v).erase (pick v) :=
        mem_erase.mpr ⟨hfp,(mem_totalIncidentEdges G v f).mpr hvf⟩
      rw [hrem v] at hh
      simpa only [mem_insert,mem_singleton] using hh
    rcases heab with heab | heab
    · rcases hfab with hfab | hfab
      · exact (hef (heab.trans hfab.symm)).elim
      · exact hitW v (heab ▸ he) (hfab ▸ hf)
    · rcases hfab with hfab | hfab
      · exact hitW v (hfab ▸ hf) (heab ▸ he)
      · exact (hef (heab.trans hfab.symm)).elim
  have hitPacket3 {t : Finset (TotalVertex G)} (v : V) (e f g : G.edgeSet)
      (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (hve : v ∈ e.val) (hvf : v ∈ f.val) (hvg : v ∈ g.val)
      (he : Sum.inr e ∈ t) (hf : Sum.inr f ∈ t) (hg : Sum.inr g ∈ t) :
      ¬Disjoint C (triangleEdges (totalGraph G) t) := by
    have hsub : ({e,f,g} : Finset G.edgeSet) ⊆ totalIncidentEdges G v := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rw [mem_totalIncidentEdges]
      rcases hx with hx | hx | hx
      · exact hx.symm ▸ hve
      · exact hx.symm ▸ hvf
      · exact hx.symm ▸ hvg
    have heq : ({e,f,g} : Finset G.edgeSet) = totalIncidentEdges G v :=
      eq_of_subset_of_card_le hsub (by rw [totalIncidentEdges_card,hdeg]; simp [hef,heg,hfg])
    have ha : a v = e ∨ a v = f ∨ a v = g := by
      have hh := (mem_totalIncidentEdges G v (a v)).mpr (hai v)
      rw [← heq] at hh
      simpa only [mem_insert,mem_singleton] using hh
    have hb : b v = e ∨ b v = f ∨ b v = g := by
      have hh := (mem_totalIncidentEdges G v (b v)).mpr (hbi v)
      rw [← heq] at hh
      simpa only [mem_insert,mem_singleton] using hh
    apply hitW v
    · rcases ha with ha | ha | ha
      · exact ha.symm ▸ he
      · exact ha.symm ▸ hf
      · exact ha.symm ▸ hg
    · rcases hb with hb | hb | hb
      · exact hb.symm ▸ he
      · exact hb.symm ▸ hf
      · exact hb.symm ▸ hg
  have noRootTriangle {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) : False :=
    (is3Clique_iff.mpr ⟨u,v,w,huv,huw,hvw,rfl⟩).not_cliqueFree htriangleFree
  have hcover : IsTriangleCover (totalGraph G) C := by
    refine ⟨hC,?_⟩
    intro t ht
    rw [mem_cliqueFinset_iff,is3Clique_iff] at ht
    obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := ht
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        cases z with
        | inl z => exact (noRootTriangle hxy hxz hyz).elim
        | inr z => exact hitBridge x y z hxy hxz hyz (by simp) (by simp) (by simp)
      | inr y =>
        cases z with
        | inl z => exact hitBridge x z y hxz hxy hyz (by simp) (by simp) (by simp)
        | inr z =>
          exact hitPacket2 x y z (fun h => hyz.ne (congrArg Sum.inr h))
            hxy hxz (by simp) (by simp) (by simp)
    | inr x =>
      cases y with
      | inl y =>
        cases z with
        | inl z => exact hitBridge y z x hyz hxy hxz (by simp) (by simp) (by simp)
        | inr z =>
          exact hitPacket2 y x z (fun h => hxz.ne (congrArg Sum.inr h))
            hxy hyz (by simp) (by simp) (by simp)
      | inr y =>
        cases z with
        | inl z =>
          exact hitPacket2 z x y (fun h => hxy.ne (congrArg Sum.inr h))
            hxz hyz (by simp) (by simp) (by simp)
        | inr z =>
          rcases lineGraph_triangle_classification hxy hxz hyz with hc | hr
          · obtain ⟨v,hvx,hvy,hvz⟩ := hc
            exact hitPacket3 v x y z (fun h => hxy.ne (congrArg Sum.inr h))
              (fun h => hxz.ne (congrArg Sum.inr h)) (fun h => hyz.ne (congrArg Sum.inr h))
              hvx hvy hvz (by simp) (by simp) (by simp)
          · obtain ⟨u,v,w,_,_,_,huv,huw,hvw,_⟩ := hr
            exact (noRootTriangle huv huw hvw).elim
  have hRsub : R ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨v,_,rfl⟩ := mem_image.mp he
    exact mem_edgeFinset.mpr (pick v).property
  have hRcard : R.card = Fintype.card V := by
    have hinj : Function.Injective (fun v => (pick v).val) :=
      Subtype.val_injective.comp pick.injective
    simp only [R,card_image_of_injective _ hinj,card_univ]
  have hm : Fintype.card V ≤ G.edgeFinset.card := by
    rw [← hRcard]
    exact card_le_card hRsub
  have hOcard : O.card ≤ G.edgeFinset.card - Fintype.card V := by
    apply card_image_le.trans
    rw [card_sdiff_of_subset hRsub,hRcard]
  have hIcard : I.card ≤ Fintype.card V := card_image_le.trans_eq (card_univ)
  have hWcard : W.card ≤ Fintype.card V := card_image_le.trans_eq (card_univ)
  have hCI := card_union_le O I
  have hCW := card_union_le (O ∪ I) W
  have hc := cover_number_le hcover
  change triangleCoverNumber (totalGraph G) ≤ (O ∪ I ∪ W).card at hc
  omega

theorem cubic_total_cover_upper_bound (hdeg : ∀ v, G.degree v = 3)
    (htriangleFree : G.CliqueFree 3) :
    2 * triangleCoverNumber (totalGraph G) ≤ 5 * Fintype.card V := by
  obtain ⟨pick,hpick⟩ := total_exists_incident_edge_assignment G (fun v => by rw [hdeg]; omega)
  have hc := cubic_total_cover_of_assignment G hdeg htriangleFree pick hpick
  have hd := G.sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hd
  simp only [sum_const,card_univ,smul_eq_mul] at hd
  omega

theorem cubic_triangleFree_total_parameters (hdeg : ∀ v, G.degree v = 3)
    (htriangleFree : G.CliqueFree 3) :
    2 * triangleCoverNumber (totalGraph G) = 5 * Fintype.card V ∧
      2 * trianglePackingNumber (totalGraph G) = 5 * Fintype.card V := by
  have hl := cubic_total_packing_lower_bound G hdeg
  have hu := cubic_total_cover_upper_bound G hdeg htriangleFree
  have hm := packing_number_le_cover_number (totalGraph G)
  omega

end Tuza
