# Statement alignment audit

Date: 8 September 2026. Mode: VERIFICATION.

This audit records the original frozen manuscript. Its statement conclusions
remain applicable because the four headline statements have not changed.
The [11 September proof-alignment audit](proof-alignment-2026-09-11.md)
supersedes the discussion of alternate proof routes and manuscript coverage.

## Conclusion and scope

Accepted for statement alignment: the four declarations in
[`Challenge.lean`](../Challenge.lean) express the four advertised conclusions of
[`paper/main.tex`](../paper/main.tex), with the finite, simple, empty-root and
disconnected-root scope preserved. No weakening of edge-disjoint triangle
packing to vertex-disjoint packing was found.

This is an encoding audit, not a claim of independent proof replay, novelty,
or expert review. The subsequent [release audit](release-audit.md) inspected
the integrated Solution and separately loaded Challenge: all four printed
types match. The four-target readiness and transitive axiom checks pass.
External Comparator verification remains a separate step.

## Shared definitions

The entire `namespace Tuza` bodies of
[`Tuza/Definitions.lean`](../Tuza/Definitions.lean) and
[`Tuza/Operators.lean`](../Tuza/Operators.lean) occur identically in Challenge
after normalizing CRLF to LF. The compared bodies had 3,567 and 1,807 characters,
respectively. This checks definitions, implicit-variable context, instances and
supporting declarations together, rather than comparing only names.

- `triangles G = G.cliqueFinset 3` represents sets of exactly three pairwise
  adjacent vertices. `triangleEdges G t` contains graph edges with both
  endpoints in `t`; for a triangle these are its three edges.
- `IsTrianglePacking` requires pairwise disjoint **edge sets** of distinct
  triangles. Triangles may share a vertex. A `Finset` prevents duplicate
  triangle copies, as required for ordinary packing.
- `IsTriangleCover` requires a subset of the graph's edges meeting every
  triangle. Non-disjointness is the intended nonempty intersection.
- The packing maximum and cover minimum range over all finite candidates,
  not a restricted construction or search bound. The empty packing and the
  full edge-set cover ensure both optimization domains are nonempty, including
  when the graph has no vertices or edges.
- Mathlib's `SimpleGraph` enforces symmetry and looplessness and uses a relation
  rather than parallel edge copies. Its line graph has the root-edge subtype
  as vertex set; adjacency means two distinct root edges have a common endpoint.
- `TotalVertex G = V ⊕ G.edgeSet` keeps original vertices and edge-vertices
  disjoint. The four `totalAdj` cases are original adjacency, incidence in
  either order, and line-graph adjacency between edge-vertices. These are
  exactly the ordinary total-graph adjacencies.

## Target-by-target comparison

| Challenge declaration | Manuscript conclusion | Alignment finding |
|---|---|---|
| `Tuza.lineGraph_satisfiesTuza` | Theorem `thm:line`, inequality part | Every finite simple root; no connectedness, triangle-free, positivity, or degree assumption. |
| `Tuza.totalGraph_satisfiesTuza` | Theorem `thm:total` | Every finite simple root, with the same unrestricted quantifiers. |
| `Tuza.lineGraph_factor_sharp` | Theorem `thm:line`, sharpness part | An actual finite line graph has packing number 1 and cover number 2. This is enough to rule out every coefficient below 2 because the packing number is positive. |
| `Tuza.cubic_triangleFree_total_parameters` | Corollary `cor:cubic` | Degree exactly 3 at every vertex and `G.CliqueFree 3`, with exact doubled packing and cover counts. |

`Fintype V` ranges over finite vertex types. The decidable-equality and
decidable-adjacency instances are computational presentations available
classically for every such graph; they impose no additional graph-theoretic
restriction. None of the universal target statements assumes `Nonempty V`.
Consequently the empty cubic root is included: its degree condition is vacuous
and both asserted optimization values are zero.

Mathlib defines `CliqueFree 3` as the absence of any 3-clique, which is ordinary
triangle-freeness for a simple graph. The cubic target states
`2 * tau = 5 * card V` and `2 * nu = 5 * card V` in natural numbers. These are
exactly the rational identities `tau = nu = 5 * card V / 2`; they do not use
truncated natural-number division. They also imply that the vertex count is
even, consistently with the cubic degree sum.

The implemented sharpness declaration in `Tuza/SmallGraphs.lean` has the same
type as Challenge. The newly written total and cubic declarations in
`Tuza/TotalBound.lean` and `Tuza/CubicTotal.lean` have the same universal
parameters and conclusions after expanding their section variables. The line
headline was subsequently integrated in `Tuza/LineBound.lean`; the release
audit checked its exported type against Challenge as well.

## Manuscript coverage limitation

The four targets certify the two universal inequalities, line-graph sharpness
and cubic triangle-free equality. They do **not** separately advertise every
intermediate manuscript result. In particular, the general sharper cover in
Proposition `prop:tf-cover` for all triangle-free roots and the standalone
balanced-orientation assertion are not among these four targets. The cubic
formalization may use its checked incident-edge-assignment construction
instead of the manuscript's orientation route without changing the cubic
statement. Completion of the four targets must not be described as a separate
formal proof of every lemma and proposition printed in the manuscript.

## Trust boundary and validation

This audit shares the encoded definitions and pinned Mathlib graph semantics
with the implementation. Separate inspection and exact body comparison help
detect transcription or quantifier errors; they are not mathematical
independence from that shared encoding. Lean checks the statement it receives,
not its informal interpretation. Challenge's deliberate holes have no proof
status and must remain outside Solution's imports.

The new Euler existence, exact Euler color discrepancy, odd-degree coloring,
global coloring, finite graph-partition assembly and line-component assembly
were individually built. Axiom inspection of these six results found only
`propext`, `Classical.choice` and `Quot.sound`. This records the checked helper
scope and does not substitute for the final four headline audits or external
Comparator/NanoDa replay.

Frozen audit inputs (SHA-256):

| File | Hash |
|---|---|
| `paper/main.tex` | `E8B9A20AD5DFF7D752BB437892487540EE13F5C7E9A2C6D0D9F778D64F0CEF08` |
| `Challenge.lean` | `58757679B6EBCB62FEEF2018CDEE620534D38D5D664560E58EF148D6F807D2D4` |
| `Tuza/Definitions.lean` | `D6499CA8B1E02FEDAEC3D0E1624E2DEBB1BEBD67A93D29C5DCAE828B57B373D3` |
| `Tuza/Operators.lean` | `592B55B1AD92AC1F8DEAB9BAEBBC4D982EC7265E9CA1C424B9B59FD3A2D47C7D` |

If any frozen input changes, repeat the affected comparison. Integration
status above was refreshed after the final Solution export and axiom checks.
