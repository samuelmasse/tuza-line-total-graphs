module

public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

/-! # Euler tours from longest trails

This supplies the existence direction missing from Mathlib's `Trails` module.
The proof uses a longest trail, the parity of its endpoint incidences, and rotation.
-/

namespace Tuza

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem trail_incidence_count_eq_degree {u v x : V} (p : G.Walk u v)
    (hp : p.IsTrail) (h : ∀ y, G.Adj x y → s(x, y) ∈ p.edges) :
    (p.edges.countP fun e => x ∈ e) = G.degree x := by
  rw [← G.card_incidenceFinset_eq_degree x]
  change _ = (G.incidenceFinset x).card
  have heq : hp.edgesFinset.filter (x ∈ ·) = G.incidenceFinset x := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_mk, Multiset.mem_coe,
      G.mem_incidenceFinset, mem_incidenceSet]
    constructor
    · rintro ⟨he, hx⟩
      exact ⟨p.edges_subset_edgeSet he, hx⟩
    · rintro ⟨he, hx⟩
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hx
      exact ⟨h y he, by simp⟩
  rw [← heq]
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
  rfl

/-- A finite connected graph with even degrees has an Euler tour based at any vertex. -/
theorem exists_eulerian_closed_walk (hconn : G.Connected)
    (heven : ∀ v, Even (G.degree v)) (base : V) :
    ∃ p : G.Walk base base, p.IsEulerian := by
  classical
  letI : Nonempty V := ⟨base⟩
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isTrail_forall_isTrail_length_le_length G
  have endpoint : ∀ y, G.Adj u y → s(u, y) ∈ p.edges := by
    intro y huy
    by_contra hnot
    have htrail := hp.cons huy.symm (by simpa [Sym2.eq_swap] using hnot)
    have := hmax y v (p.cons huy.symm) htrail
    simp only [Walk.length_cons] at this
    omega
  have huv : u = v := by
    have he : Even (p.edges.countP fun e => u ∈ e) := by
      rw [trail_incidence_count_eq_degree G p hp endpoint]
      exact heven u
    have := (hp.even_countP_edges_iff u).mp he
    by_contra hne
    exact (this hne).1 rfl
  subst v
  have used : ∀ x ∈ p.support, ∀ y, G.Adj x y → s(x, y) ∈ p.edges := by
    intro x hx y hxy
    by_contra hnot
    let q := p.rotate x hx
    have hq : q.IsTrail := hp.rotate hx
    have hnotq : s(y, x) ∉ q.edges := by
      simpa only [q, (p.rotate_edges x hx).mem_iff, Sym2.eq_swap] using hnot
    have := hmax y x (q.cons hxy.symm) (hq.cons hxy.symm hnotq)
    simp only [Walk.length_cons, q, Walk.length_rotate] at this
    omega
  have support_all : ∀ x, x ∈ p.support := by
    intro x
    obtain ⟨q⟩ := hconn.preconnected u x
    have walk_closed : ∀ {a b : V}, (q : G.Walk a b) →
        a ∈ p.support → b ∈ p.support := by
      intro a b q
      induction q with
      | nil => exact id
      | @cons a b c hab q ih =>
        intro ha
        exact ih (p.snd_mem_support_of_mem_edges (used a ha b hab))
    exact walk_closed q p.start_mem_support
  have heuler : p.IsEulerian := hp.isEulerian_of_forall_mem (by
    intro e he
    induction e using Sym2.inductionOn with
    | hf x y => exact used x (support_all x) y he)
  refine ⟨p.rotate base (support_all base), ?_⟩
  intro e he
  rw [(p.rotate_edges base (support_all base)).perm.count_eq]
  exact heuler e he

end Tuza
