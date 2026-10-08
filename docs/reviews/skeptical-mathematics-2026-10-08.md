# Skeptical mathematics review

Date: 8 October 2026. Mode: VERIFICATION.

Frozen claim: the four manuscript/Challenge targets at source commit
`09dbb9a839ebf205891f7e14bf6c8167b4e67970`.

## Decision and trust boundary

Accepted at the level of mathematical reconstruction and source-level
statement/proof correspondence. No mathematical gap requiring a correction
was found in the frozen manuscript. This is a separate skeptical AI pass,
not human expert review, a novelty decision, a fresh Lean/NanoDa replay, or
independent re-encoding of the entire theorem. It shares the manuscript,
Lean definitions, and model family with the development. The independently
written finite check below shares the source data, but not the repository's
certificate-checker implementation.

Concurrent module-export and toolchain migration edits were visible during
the review. This verdict covers the frozen mathematical arguments; successful
compilation and axiom audits of the revised working tree require their own
validation.

The full Tuza conjecture is outside scope. Acceptance here does not remove
any unresolved obligation for arbitrary finite simple graphs.

## Reconstructed arguments

1. **Clique slack.** The initial cyclic triples have at most one second-half
   vertex. Sharing their first-half pair identifies a triple; sharing one
   first-half vertex and the second-half vertex identifies the other index
   by cancellation modulo the half-order. The even extra triple uses only
   second-half edges. An odd extra triple cannot use an edge of an initial
   triple: the required other index would equal the first. Distinct odd
   extras have different second-half coordinates because doubling is
   injective on the specified index set. The stated Latin recurrence uses
   disjoint cross-part edges and internal edges. The two displayed arithmetic
   differences and thresholds are correct. Strong induction genuinely drops
   from `n` to `floor(n/3)`.
2. **Euler coloring.** The dummy vertex has even degree by the handshake
   lemma and makes every original degree even. Starting the tour at the dummy
   confines any odd cyclic seam to it; deleting one dummy incidence at each
   originally odd vertex leaves discrepancy one. In an Eulerian root, the
   first/last pair creates exactly the stated discrepancy at the chosen base.
   This includes the zero-edge connected graph via its empty tour.
3. **Line graphs.** Two distinct simple-root edges have a unique common
   endpoint, so packet edges really are disjoint. Pairwise-intersecting
   three-edge sets give exactly the star/root-triangle classification. The
   global monochromatic-edge cover hits both types. There is one surcharge
   per odd-edge Eulerian component. An even degree at least six pays for it
   using clique slack. With no such degree, triangle-freeness allows unrelated
   local balanced cuts. Otherwise the degrees are two or four; a maximum
   local packing can avoid the prescribed wedge at each vertex of one root
   triangle, and the added root triangle is disjoint from their union. No
   witnesses from incompatible graph states are combined.
4. **Line sharpness.** The line graph of the four-leaf star is `K4`.
   Its triangles pairwise share edges; one edge misses a triangle and two
   opposite edges meet every triangle. The ratio-two witness has the exact
   packing and cover numbers asserted by Challenge.
5. **Total graphs.** A root edge-vertex keeps one global color even though
   it belongs to two packets. Each original vertex belongs to just its own
   packet and can take the minority color independently. Packet discrepancies
   zero, one, or two become one, zero, or one. Every monochromatic edge is
   selected, including all original-original edges, so the cover also handles
   triangles crossing packets. Bridges use original/incidence edges; the
   local line packings use wedge edges. Their union is therefore an actual
   simultaneous packing. The successor identity for `t` and the degree sum
   give the stated factor two with the inequality in the correct direction.
6. **Cubic triangle-free equality.** Hall's incidence count gives an
   injective choice of one incident root edge per vertex. In each `K4`
   packet, the chosen incidence edge and opposite wedge meet every packet
   triangle. An assigned bridge is met by its chosen incidence; an unassigned
   bridge by its original edge. The four vertex-type cases exclude all other
   triangles under triangle-freeness. Injectivity gives exactly `n` assigned
   root edges, so the cover has at most `m+n=5n/2` edges. The `m` bridges and
   one local triangle per cubic vertex give a packing of that size. The
   packing-cover inequality closes the exact sandwich.

## Boundary and encoding checks

The Challenge quantifies over finite simple roots without connectivity,
positivity, or triangle-freeness restrictions in either universal inequality.
Its total adjacency is the ordinary disjoint-sum construction, and its
packing definition means edge-disjoint triangles. The cubic hypothesis is
pointwise degree three plus absence of a three-clique; its doubled natural
equalities exactly express `5n/2`. Empty roots give zero on both sides,
including the vacuously cubic empty root. Isolated root vertices contribute
no triangles. Component colorings and line certificates are transported
through actual inclusions in `BalancedColoring.lean` and
`LineComponents.lean`; no connectedness assumption leaks into the headline
targets.

The informal order of the seam cases differs from the connected Lean
assembly, which uses its uniform `T+1` bound even for some even-edge
components. The exact Euler parity lemma supports the sharper prose
organization. This is an aligned construction, not a missing implication.

## Independent finite reconstruction

A fresh in-memory JavaScript check read `CliqueFiniteCertificates.lean`
through `git show HEAD:Tuza/CliqueFiniteCertificates.lean`, reconstructed the
paper recipe independently, and compared each ordered list after sorting
the vertices of each triangle. All 21 lists matched. Every triangle had
three distinct vertices in range; no graph edge repeated; all 4,706 pairs
of triangles within a list had intersection at most one. All basic and
even-order slack inequalities passed. The total was 328 triangles, with
counts

`0,0,0,1,1,2,4,6,7,8,11,15,16,18,22,28,29,32,37,45,46`.

This check supports correspondence and transcription accuracy. It is not
needed as a new premise of the theorem and does not replace kernel replay.

## Optional simplification

The cyclic recipe described as finite bases actually works at every order.
For `n=2r>=6` it has `choose(r,2)+1` triples and hence `2p=t(n)+2`.
For `n=2r+1`, it has `choose(r,2)+r` triples when `r` is odd and
`choose(r,2)+r/2` when `r` is even; these give `2p>=r^2=t(n)`.
Thus a uniform proof of that recipe could eliminate the recurrence and base
tables. This is an optional future exposition/formalization simplification,
not a defect or publication blocker. The currently aligned proof is valid;
changing it requires its own formal correspondence checks.
