module

public import Tuza.Eulerian
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! # Alternating edge colorings and exact incidence balance -/

namespace Tuza

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of root edges of a given color incident with a root vertex. -/
def edgeColorDegree (color : G.edgeSet → Bool) (v : V) (c : Bool) : ℕ :=
  ((Finset.univ : Finset G.edgeSet).filter (fun e => v ∈ e.val ∧ color e = c)).card

theorem edgeColorDegree_add (color : G.edgeSet → Bool) (v : V) :
    edgeColorDegree G color v true + edgeColorDegree G color v false = G.degree v := by
  classical
  let s := (Finset.univ : Finset G.edgeSet).filter (fun e => v ∈ e.val)
  have hcard : s.card = G.degree v := by
    rw [← G.card_incidenceFinset_eq_degree v]
    apply Finset.card_bij (fun e _ => e.val)
    · intro e he
      apply (G.mem_incidenceFinset (v := v) (e := e.val)).mpr
      exact ⟨e.property, (Finset.mem_filter.mp he).2⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro e he
      have he' := G.mem_incidenceFinset (v := v) (e := e) |>.mp he
      exact ⟨⟨e, he'.1⟩, by simpa [s] using he'.2, rfl⟩
  rw [← hcard]
  simpa [edgeColorDegree, s, Finset.filter_filter, Bool.not_eq_true] using
    (Finset.card_filter_add_card_filter_not (s := s) (fun e => color e = true))

/-- An injective graph homomorphism preserves distinct colored incidences. -/
theorem edgeColorDegree_map_le {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (f : G →g H)
    (hf : Function.Injective f) (color : H.edgeSet → Bool) (v : V) (c : Bool) :
    edgeColorDegree G (fun e => color (f.mapEdgeSet e)) v c ≤
      edgeColorDegree H color (f v) c := by
  classical
  apply Finset.card_le_card_of_injOn f.mapEdgeSet
  · intro e he
    obtain ⟨hv, hc⟩ := Finset.mem_filter.mp he |>.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Sym2.mem_map.mpr ⟨v, hv, rfl⟩, hc⟩
  · exact (SimpleGraph.Hom.mapEdgeSet.injective f hf).injOn

/-- If an injective homomorphism preserves the whole degree at a vertex, it
preserves each color degree there as well. -/
theorem edgeColorDegree_map_eq {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (f : G →g H)
    (hf : Function.Injective f) (color : H.edgeSet → Bool) (v : V)
    (hdeg : G.degree v = H.degree (f v)) (c : Bool) :
    edgeColorDegree G (fun e => color (f.mapEdgeSet e)) v c =
      edgeColorDegree H color (f v) c := by
  have hr := edgeColorDegree_map_le G H f hf color v true
  have hb := edgeColorDegree_map_le G H f hf color v false
  have hs := edgeColorDegree_add G (fun e => color (f.mapEdgeSet e)) v
  have ht := edgeColorDegree_add H color (f v)
  cases c <;> omega

private theorem edgeColorDegree_eq_countP {u w : V} (p : G.Walk u w)
    (hp : p.IsEulerian) (color : Sym2 V → Bool) (v : V) (c : Bool) :
    edgeColorDegree G (fun e => color e.val) v c =
      p.edges.countP (fun e => v ∈ e ∧ color e = c) := by
  classical
  have hcard : edgeColorDegree G (fun e => color e.val) v c =
      (hp.isTrail.edgesFinset.filter fun e => v ∈ e ∧ color e = c).card := by
    apply Finset.card_bij (fun e _ => e.val)
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact Finset.mem_filter.mpr ⟨hp.mem_edges_iff.mpr e.property, he⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro e he
      obtain ⟨he, hc⟩ := Finset.mem_filter.mp he
      exact ⟨⟨e, hp.mem_edges_iff.mp he⟩, by simpa using hc, rfl⟩
  rw [hcard, ← Multiset.coe_countP, Multiset.countP_eq_card_filter]
  rfl

private def alternatingColor {α : Type*} [DecidableEq α] : List α → α → Bool
  | [], _ => true
  | a :: l, x => if x = a then true else !(alternatingColor l x)

private theorem alternatingColor_count {α : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (f : α → Bool) :
    ((l.countP fun a => f a && alternatingColor l a) : ℤ) -
        ((l.countP fun a => f a && !(alternatingColor l a)) : ℤ) =
      (l.map (fun a => if f a then (1 : ℤ) else 0)).alternatingSum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnot := (List.nodup_cons.mp hl).1
    have hnodup := hl.of_cons
    have htrue : (l.countP fun x => f x && alternatingColor (a :: l) x) =
        (l.countP fun x => f x && !(alternatingColor l x)) := by
      apply List.countP_congr
      intro x hx
      simp [alternatingColor, show x ≠ a by intro h; subst x; exact hnot hx]
    have hfalse : (l.countP fun x => f x && !(alternatingColor (a :: l) x)) =
        (l.countP fun x => f x && alternatingColor l x) := by
      apply List.countP_congr
      intro x hx
      simp [alternatingColor, show x ≠ a by intro h; subst x; exact hnot hx]
    rw [List.countP_cons, List.countP_cons, htrue, hfalse]
    simp only [alternatingColor, ↓reduceIte, Bool.and_true, Bool.not_true,
      Bool.and_false, Bool.false_eq_true, Nat.cast_add, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, List.map_cons, List.alternatingSum_cons]
    have := ih hnodup
    cases f a <;> simp_all <;> omega

private def walkAlternatingIncidence {u v : V} (p : G.Walk u v) (x : V) : ℤ :=
  (p.edges.map fun e => if x ∈ e then (1 : ℤ) else 0).alternatingSum

private theorem walkAlternatingIncidence_eq {u v : V} (p : G.Walk u v) (x : V) :
    walkAlternatingIncidence G p x =
      (if x = u then 1 else 0) -
        (if Even p.length then (if x = v then 1 else 0)
          else -(if x = v then 1 else 0)) := by
  induction p with
  | nil => simp [walkAlternatingIncidence]
  | @cons u v w huv p ih =>
    simp only [walkAlternatingIncidence, Walk.edges_cons, List.map_cons,
      List.alternatingSum_cons] at ih ⊢
    rw [ih]
    simp only [Walk.length_cons, Nat.even_add_one, ← Nat.not_even_iff_odd, Sym2.mem_iff]
    have hne := huv.ne
    by_cases hxu : x = u <;> by_cases hxv : x = v <;>
      by_cases hxw : x = w <;> by_cases he : Even p.length <;>
      simp only [hxu, hxv, hxw, he, not_true_eq_false, not_false_eq_true,
        or_self, false_or, or_false, true_or, or_true, ↓reduceIte] <;> simp_all

/-- Exact color discrepancy for a connected even-degree graph.  The only possible
imbalance is two extra `true` edges at the prescribed base of an odd Euler tour. -/
theorem exists_eulerian_edge_coloring (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) (base : V) :
    ∃ color : G.edgeSet → Bool, ∀ v,
      (edgeColorDegree G color v true : ℤ) - (edgeColorDegree G color v false : ℤ) =
        if Even G.edgeFinset.card then 0 else if v = base then 2 else 0 := by
  classical
  obtain ⟨p, hp⟩ := exists_eulerian_closed_walk G hconn heven base
  refine ⟨fun e => alternatingColor p.edges e.val, ?_⟩
  intro v
  rw [edgeColorDegree_eq_countP G p hp, edgeColorDegree_eq_countP G p hp]
  have hc := alternatingColor_count p.edges hp.isTrail.edges_nodup
    (fun e => decide (v ∈ e))
  have hc' :
      ((p.edges.countP fun e => decide (v ∈ e ∧ alternatingColor p.edges e = true)) : ℤ) -
      ((p.edges.countP fun e => decide (v ∈ e ∧ alternatingColor p.edges e = false)) : ℤ) =
        walkAlternatingIncidence G p v := by
    simpa [walkAlternatingIncidence] using hc
  rw [hc', walkAlternatingIncidence_eq]
  have hlen : p.length = G.edgeFinset.card := by
    rw [← hp.edgesFinset_eq]
    exact (Walk.length_edges p).symm
  rw [hlen]
  by_cases he : Even G.edgeFinset.card <;> by_cases hv : v = base <;> simp [he, hv]

/-- Adjoin one dummy vertex and join it precisely to the odd-degree vertices. -/
def oddAugment : SimpleGraph (Option V) where
  Adj
    | some u, some v => G.Adj u v
    | none, some v => Odd (G.degree v)
    | some v, none => Odd (G.degree v)
    | none, none => False
  symm.symm := by
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact G.adj_symm h
  loopless.irrefl := by
    intro a h
    cases a
    · exact h
    · exact G.loopless.irrefl _ h

instance oddAugmentDecidableAdj : DecidableRel (oddAugment G).Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [oddAugment] <;> infer_instance

/-- The root embeds into its dummy augmentation. -/
def oddAugmentHom : G →g oddAugment G where
  toFun := Option.some
  map_rel' := id

theorem oddAugment_degree_some (v : V) :
    (oddAugment G).degree (some v) = G.degree v + if Odd (G.degree v) then 1 else 0 := by
  classical
  have hs : (oddAugment G).neighborFinset (some v) =
      if Odd (G.degree v) then insert none ((G.neighborFinset v).map .some)
      else (G.neighborFinset v).map .some := by
    ext w
    simp only [mem_neighborFinset]
    cases w <;> by_cases ho : Odd (G.degree v) <;> simp [oddAugment, ho]
  rw [← (oddAugment G).card_neighborFinset_eq_degree, hs]
  split_ifs <;> simp [add_comm]

theorem oddAugment_degree_none :
    (oddAugment G).degree none = (Finset.univ.filter fun v => Odd (G.degree v)).card := by
  classical
  have hs : (oddAugment G).neighborFinset none =
      (Finset.univ.filter fun v => Odd (G.degree v)).map .some := by
    ext w
    simp only [mem_neighborFinset]
    cases w <;> simp [oddAugment]
  rw [← (oddAugment G).card_neighborFinset_eq_degree, hs, Finset.card_map]

theorem oddAugment_even (v : Option V) : Even ((oddAugment G).degree v) := by
  classical
  cases v with
  | none =>
    rw [oddAugment_degree_none]
    exact G.even_card_odd_degree_vertices
  | some v =>
    rw [oddAugment_degree_some]
    by_cases ho : Odd (G.degree v)
    · simpa [ho] using ho.add_odd (by decide : Odd 1)
    · simpa [ho] using Nat.not_odd_iff_even.mp ho

theorem oddAugment_connected (hconn : G.Connected) (ho : ∃v, Odd (G.degree v)) :
    (oddAugment G).Connected := by
  obtain ⟨v, hv⟩ := ho
  have hreach : ∀ w, (oddAugment G).Reachable none w := by
    intro w
    cases w with
    | none => rfl
    | some w =>
      have hfirst : (oddAugment G).Adj none (some v) := hv
      exact hfirst.reachable.trans ((hconn.preconnected v w).map (oddAugmentHom G))
  exact ⟨fun a b => (hreach a).symm.trans (hreach b)⟩

/-- A connected graph with an odd-degree vertex has an exactly balanced coloring:
even degrees split equally and odd degrees split with discrepancy one. -/
theorem exists_odd_edge_coloring (hconn : G.Connected) (ho : ∃v, Odd (G.degree v)) :
    ∃ color : G.edgeSet → Bool, ∀ v,
      edgeColorDegree G color v true ≤ edgeColorDegree G color v false + 1 ∧
      edgeColorDegree G color v false ≤ edgeColorDegree G color v true + 1 ∧
      (Even (G.degree v) → edgeColorDegree G color v true = edgeColorDegree G color v false) := by
  classical
  obtain ⟨color, hc⟩ := exists_eulerian_edge_coloring (oddAugment G)
    (oddAugment_connected G hconn ho) (oddAugment_even G) none
  let rootColor : G.edgeSet → Bool := fun e => color ((oddAugmentHom G).mapEdgeSet e)
  refine ⟨rootColor, ?_⟩
  intro v
  have hb := hc (some v)
  simp only [Option.some_ne_none, ↓reduceIte, ite_self, sub_eq_zero] at hb
  have hbr : edgeColorDegree (oddAugment G) color (some v) true =
      edgeColorDegree (oddAugment G) color (some v) false := by exact_mod_cast hb
  have hr := edgeColorDegree_map_le G (oddAugment G) (oddAugmentHom G)
    (Option.some_injective V) color v true
  have hb' := edgeColorDegree_map_le G (oddAugment G) (oddAugmentHom G)
    (Option.some_injective V) color v false
  have hs := edgeColorDegree_add G rootColor v
  have ht := edgeColorDegree_add (oddAugment G) color (some v)
  rw [oddAugment_degree_some] at ht
  change edgeColorDegree G rootColor v true ≤
    edgeColorDegree (oddAugment G) color (some v) true at hr
  change edgeColorDegree G rootColor v false ≤
    edgeColorDegree (oddAugment G) color (some v) false at hb'
  have hd : (if Odd (G.degree v) then 1 else 0) ≤ 1 := by split_ifs <;> omega
  refine ⟨by omega, by omega, ?_⟩
  intro he
  have hn : ¬Odd (G.degree v) := Nat.not_odd_iff_even.mpr he
  simp only [hn, ↓reduceIte, add_zero] at ht
  omega

theorem exists_connected_balanced_edge_coloring (hconn : G.Connected) :
    ∃ color : G.edgeSet → Bool, ∀ v,
      edgeColorDegree G color v true ≤ edgeColorDegree G color v false + 2 ∧
      edgeColorDegree G color v false ≤ edgeColorDegree G color v true + 2 := by
  classical
  by_cases ho : ∃v, Odd (G.degree v)
  · obtain ⟨color, hc⟩ := exists_odd_edge_coloring G hconn ho
    exact ⟨color, fun v => ⟨by have := (hc v).1; omega, by have := (hc v).2.1; omega⟩⟩
  · have he : ∀v, Even (G.degree v) := fun v => Nat.not_odd_iff_even.mp (by aesop)
    obtain ⟨base⟩ := hconn.nonempty
    obtain ⟨color, hc⟩ := exists_eulerian_edge_coloring G hconn he base
    refine ⟨color, fun v => ?_⟩
    have h := hc v
    split_ifs at h <;> omega

/-- The induced connected component retains every root incidence at its vertices. -/
theorem component_degree (C : G.ConnectedComponent) [Fintype C]
    [DecidableRel C.toSimpleGraph.Adj] (v : C) :
    C.toSimpleGraph.degree v = G.degree v.val := by
  classical
  rw [← C.toSimpleGraph.card_neighborSet_eq_degree, ← G.card_neighborSet_eq_degree]
  apply Fintype.card_congr
  exact
    { toFun := fun w => ⟨w.val.val, w.property⟩
      invFun := fun w => ⟨⟨w.val, (C.mem_supp_congr_adj w.property).mp v.property⟩,
        w.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Every finite simple graph has a global edge coloring with discrepancy at most
two. Combined with `edgeColorDegree_add`, odd degrees necessarily have discrepancy
at most one.  Component colorings are transported through their actual inclusions. -/
theorem exists_balanced_edge_coloring :
    ∃ color : G.edgeSet → Bool, ∀ v,
      edgeColorDegree G color v true ≤ edgeColorDegree G color v false + 2 ∧
      edgeColorDegree G color v false ≤ edgeColorDegree G color v true + 2 := by
  classical
  have hex (C : G.ConnectedComponent) : ∃ color : G.edgeSet → Bool, ∀ v : C,
      edgeColorDegree G color v.val true ≤ edgeColorDegree G color v.val false + 2 ∧
      edgeColorDegree G color v.val false ≤ edgeColorDegree G color v.val true + 2 := by
    obtain ⟨localColor, hc⟩ := exists_connected_balanced_edge_coloring C.toSimpleGraph
      C.connected_toSimpleGraph
    let f := C.toSimpleGraph_hom
    have hinj : Function.Injective f := Subtype.val_injective
    have hej := SimpleGraph.Hom.mapEdgeSet.injective f hinj
    let color := Function.extend f.mapEdgeSet localColor (fun _ => true)
    have hext : (fun e => color (f.mapEdgeSet e)) = localColor :=
      funext (hej.extend_apply localColor (fun _ => true))
    refine ⟨color, fun v => ?_⟩
    have ht := edgeColorDegree_map_eq C.toSimpleGraph G f hinj color v
      (component_degree G C v) true
    have hf := edgeColorDegree_map_eq C.toSimpleGraph G f hinj color v
      (component_degree G C v) false
    rw [hext] at ht hf
    simpa only [ht, hf, f, ConnectedComponent.toSimpleGraph_hom_apply] using hc v
  choose colors hc using hex
  have endpoint (e : G.edgeSet) : ∃v, v ∈ e.val := by
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | hf a b => exact ⟨a, by simp⟩
  let base (e : G.edgeSet) : V := (endpoint e).choose
  have hbase (e : G.edgeSet) : base e ∈ e.val := (endpoint e).choose_spec
  let color (e : G.edgeSet) := colors (G.connectedComponentMk (base e)) e
  refine ⟨color, fun v => ?_⟩
  have heq (c : Bool) : edgeColorDegree G color v c =
      edgeColorDegree G (colors (G.connectedComponentMk v)) v c := by
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro e _
    by_cases hv : v ∈ e.val
    · have hcomp : G.connectedComponentMk (base e) = G.connectedComponentMk v := by
        obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hv
        have hb := hbase e
        rw [hw] at hb
        rcases Sym2.mem_iff.mp hb with he | he
        · rw [he]
        · rw [he]
          have hadj : G.Adj v w := by simpa [hw] using e.property
          exact ConnectedComponent.sound hadj.symm.reachable
      simp [color, hcomp]
    · simp [hv]
  rw [heq true, heq false]
  exact hc (G.connectedComponentMk v) ⟨v, rfl⟩

end Tuza
