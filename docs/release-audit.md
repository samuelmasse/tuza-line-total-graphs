# Release statement and dependency audit

Date: 8 September 2026. Mode: VERIFICATION, separate judgment pass.

Historical snapshot audit. The [11 September proof-alignment audit](proof-alignment-2026-09-11.md)
records the revised manuscript's correspondence to the same proof constructions.

## Result

**Accepted within the checked scope.** No accidental extra assumption, omitted
finite-root case, circular proof dependency, unapproved axiom, or unsafe proof
shortcut was found. All four advertised declarations are present in the
compiled `Solution` environment. Their printed types match the corresponding
declarations in a separately imported `Challenge` environment.

This is a local statement/dependency audit of the existing compiled modules.
It is not a fresh whole-project rebuild, Comparator execution, NanoDa replay,
human review, or novelty judgment. Final release acceptance still depends on
the required checks of the immutable submitted snapshot.

## Concrete checks

The static import graph contained 38 local Lean modules and no cycle.
Traversing the imports of `Solution` reached the proof modules and did not
reach `Challenge`. Challenge imports only the three pinned Mathlib modules
listed at its top. The four deliberate `sorry` statements are confined to
Challenge; none occurs in `Tuza.lean`, `Tuza/`, or `Solution.lean`.

The implementation scan also found no custom axiom declaration,
`native_decide`, `unsafe` declaration, `implemented_by`, `extern`,
`Lean.ofReduceBool`, `Lean.ofReduceNat`, or evaluated external value used as a
proof. The finite clique certificates use ordinary proof-producing decision
procedures, including explicit `decide +kernel`. `of_decide_eq_true` there is
the standard theorem applied to a decision result reduced by the kernel.
Increased heartbeat and recursion settings affect elaboration resources, not
the logical statement or accepted axioms.

Axiom inspection through `import Solution` returned the same permitted list
for all four targets:

| Declaration | Transitive axioms |
|---|---|
| `Tuza.lineGraph_satisfiesTuza` | `propext`, `Classical.choice`, `Quot.sound` |
| `Tuza.totalGraph_satisfiesTuza` | `propext`, `Classical.choice`, `Quot.sound` |
| `Tuza.lineGraph_factor_sharp` | `propext`, `Classical.choice`, `Quot.sound` |
| `Tuza.cubic_triangleFree_total_parameters` | `propext`, `Classical.choice`, `Quot.sound` |

The universal clique bound, even-order slack, finite base theorem,
root-triangle augmentation, connected line assembly and component assembly
were also inspected in their compiled environments. Their axiom lists contain
only those same three axioms. In particular, the final universal clique theorem
has no undischarged finite-base premise, and the final line theorem has no
undischarged local-bound, augmentation, or connectedness premise.

The installed Lean reports version 4.33.1. The manifest pins Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`. This inspection does not claim an
independent reconstruction of the local dependency cache.

## Statement and graph-case review

The complete copied namespace bodies in Challenge still match
`Tuza/Definitions.lean` and `Tuza/Operators.lean`, after normalizing line endings.
The detailed semantic comparison is in [statement-audit.md](statement-audit.md).
The later integrated Solution exports now discharge the export/type-check
follow-up left open by that earlier snapshot.

The four targets retain the intended semantics:

- `IsTrianglePacking` requires disjoint graph-edge sets of distinct triangles;
  sharing one vertex remains allowed. Covers are subsets of graph edges that
  meet every triangle. The numerical optima range over all finite candidates.
- Line graphs use Mathlib's distinct intersecting root edges. Total graphs use
  the disjoint sum of original vertices and root-edge vertices, with exactly
  original adjacency, incidence, and line-graph adjacency in the respective
  cases.
- The universal line and total targets have no connectedness, nonemptiness,
  triangle-free, maximum-degree, or positivity assumption. Finite type and
  decidability instances do not exclude any finite simple graph.
- The sharpness witness has packing number 1 and cover number 2, so a smaller
  coefficient really fails on an actual line graph.
- Cubic equality assumes degree exactly 3 and `CliqueFree 3`, with
  `2 * tau = 5 * card V` and `2 * nu = 5 * card V`. These are exact rational
  `5n/2` identities, not truncated natural division. The empty root is allowed;
  its cubic hypothesis is vacuous and both counts are zero.

Empty roots and disconnected roots are not discarded in an internal reduction.
The line-component theorem assembles actual mapped packings and covers over
all root components. Empty unions remain valid. In a connected singleton or
edgeless root the triangle-free branch applies. In the low-degree seam branch,
the root triangle establishes nontriviality, and connectedness then supplies
positive degree; evenness and degree below six legitimately reduce the degrees
to two or four. This does not silently discard isolated vertices elsewhere.

Euler-tour existence is proved locally from a longest trail, endpoint parity,
rotation and connected support propagation. The proof does not assume the
existence theorem left as a TODO in pinned Mathlib. The dummy augmentation and
the component color extension are transported through their actual graph
inclusions, with degree and color-degree counts checked at those inclusions.

## Proof differences and their effect

The documented Latin recurrence and Hall-based cubic proof preserve their
target conclusions. The clique recurrence uses explicit checked bases at
orders 0 through 20 and strong induction thereafter: for order at least 21,
`q = n / 3` satisfies `7 ≤ q < n`. Thus universal bounds follow from an actual
induction, not from finite testing alone. The certificate checker verifies
three vertices per triangle and pairwise intersection size at most one, and
derives absence of duplicate list entries before using the list length.

Three further reorganizations were checked and are harmless:

1. The universal total cover is proved by containing all monochromatic edges
   of a single coloring of the total graph. The general binary-color cover
   theorem then covers every triangle. This replaces the manuscript's
   case-by-case verification without omitting any triangle type.
2. The total packing lemma adds all bridges to **any** line-graph packing
   transported to edge-vertices. It proves disjointness from the bridges and
   cardinality preservation. The final bound uses the elementary incidence
   packing lower bound; it does not assume the universal line-graph Tuza theorem.
3. Connected line assembly permits the weaker `T + 1` Euler bound for every
   even-degree component, including even-edge ones. High-degree slack,
   triangle-free local cuts, and the degree-two/four root-triangle augmentation
   still give exhaustive closing branches. Charging an unnecessary unit in
   this intermediate bound introduces no new hypothesis or missing case.

Several cover counts are proved as upper bounds where the paper records an
exact construction size. Those upper bounds suffice for the advertised
inequalities. The four targets do not separately formalize every intermediate
manuscript identity or proposition: in particular, the general sharper
triangle-free total cover, its odd-vertex correction, and a universal balanced
orientation are outside the four declarations. Release wording should retain
that scope rather than claiming a separate proof of every displayed statement
in the manuscript.

## Trust boundary and release follow-up

This pass shares the encoded graph definitions and the pinned Mathlib semantics
with proof development. The auditing agent also authored the Euler, coloring
and component-assembly modules. A separate judgment pass does not make those
parts independent of their author or of the common statement translation.
The axiom inspections read the existing compiled modules; no whole-project
rebuild was launched by this audit.

No mathematical correction is requested by this pass. Before submission,
freeze the completed source, rerun the required release checks and external
replay, and ensure README, progress records, metadata and alignment status
describe the four proved exports and the actual completed external checks.
Development-era statements saying the universal results or cubic equality are
missing must not survive in the release description. Later source or import
changes require a corresponding audit refresh.
