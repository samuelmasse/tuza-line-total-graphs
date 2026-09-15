# Clique packing and seam augmentation verification

Mode: VERIFICATION. These are supporting results for the paper's line and
total graph theorems; they do not address Tuza's conjecture for arbitrary
graphs.

## Uniform clique bounds

`Tuza.CompleteGraphPacking` proves, for every natural number `n`,

```
cliqueCoverCost n ≤ 2 * trianglePackingNumber (completeGraph (Fin n))
```

At every even order at least six it also proves the same inequality with
`cliqueCoverCost n + 2` on the left. Cardinality-equivalence versions cover
any finite vertex type. The empty graph is included.

The formal proof and revised paper use the same elementary construction.
It replaces the earlier manuscript's round-robin proof. For a finite additive
group `A`, the triangles indexed by
`(a, b, a + b)` use one vertex from each of three disjoint copies. Cancellation
shows that distinct triangles share at most one vertex. They give exactly
`|A|²` triangles. Adding an arbitrary maximum internal clique packing in each
copy gives

```
D(3q) ≥ q² + 3 D(q),  q > 0.
```

The construction, transport, cross-packet disjointness, and exact counts are
proved in `LatinPacking`, `CliqueConstruction`, and `CliqueRecurrence`.
`CliqueRecurrenceArithmetic` proves that, for `q ≥ 7` and `s < 3`,

```
t(3q + s) + 2 ≤ 2q² + 3t(q).
```

Strong induction uses this inequality, the recurrence, and monotonicity under
vertex inclusion. The 21 base orders below 21 use literal triangle lists in
`CliqueFiniteCertificates`. `CliqueCertificateTools` proves that cardinality
three and pairwise intersection cardinality at most one imply a valid packing,
no duplicate list entries, and the claimed exact list-length lower bound.
Every finite check uses kernel reduction. No optimum is computed and no
native evaluator is accepted as a proof oracle.

## Reserving a root triangle

`CliqueEdgeAvoidance` proves that at orders two and four a maximum clique
packing can use at most one vertex of any prescribed set of at most two
vertices. At order four, deleting one member of that set leaves a triangle;
the packing number is one. The order-two packing is empty.

`LineTriangleAugment` applies this result to a non-star line triangle. Its
intersection with each incidence clique has at most two vertices: otherwise
all three edges would have a common root endpoint. Maximum local packings
can therefore be chosen to share no line edge with that triangle. Their
union is still a packing, and adjoining the reserved triangle increases the
size by one. An explicit translation of a root triangle supplies the required
non-star line triangle. The final theorem is

```
line_packing_augment_root_triangle
  (G : SimpleGraph V)
  (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 4)
  (htri : ¬G.CliqueFree 3)
```

with conclusion `sum_v D(degree v) + 1 ≤ trianglePackingNumber G.lineGraph`.

## Focused validation and trust boundary

The changed modules were built with the pinned Lean/Mathlib toolchain.
The clique bounds, avoidance lemmas, and both augmentation theorems were
audited with `#print axioms`;
only `propext`, `Classical.choice`, and `Quot.sound` were reported. Source
checks found no proof holes, custom axioms, or `native_decide` calls in these
modules.

The first finite-certificate implementations spent several minutes reducing
bounded quantifiers over triangle finsets. A separate `#synth` check confirmed
that the inferred instance was `Fintype.decidableForallFintype`, enumerating
all triangle vertex subsets. Explicitly supplying
`List.decidableBAll` to `of_decide_eq_true` limits the check to the literal
list. The largest base independently compiled with this change, then all
21 bases compiled together in approximately 20 seconds. This changes
evaluation cost only; both paths have the same kernel trust boundary.
