# Source and contribution provenance

Author and responsible maintainer: Samuel Massé.

The MIT license was selected explicitly on 8 September 2026.

## Mathematical source

The original `paper/main.tex` and `paper/references.bib` were copied without
mathematical changes from the author's vmath paper package dated 7 September
2026. The following hashes identify that historical, submitted snapshot;
they do not identify the revised manuscript of 11 September.

- Manuscript SHA-256:
  `e8b9a20ad5dff7d752bb437892487540ee13f5c7e9a2c6d0d9f778d64f0cef08`
- Bibliography SHA-256:
  `91ccee364517fc1713c66b19c76fab0f2ed7b0c44aa38ad1efd6e8f0435e04a8`
- PDF SHA-256:
  `3356f02c945d2c4e58c5c555f06175ba5bf6046742421519c35e81491b2aeb63`

The source is an internally audited manuscript, not a previously registered
formal proof. Its finite Python checks are not premises in this Lean project.
The prior novelty search located no exact headline collision but did not
establish priority. The bibliography retains the classical clique-packing
attribution to Sebő reported in Munaro's thesis and the relevant earlier work.

## Formal source

`Tuza/Definitions.lean` adapts the author's
`vmath/proofs/lean/VMath/Tuza/Basic.lean`: three-vertex cliques, pairwise
edge-disjoint packings, edge covers and finite extremal numbers. The namespace,
imports and documentation are adjusted for this standalone project. It is not
claimed as a separately independent translation of those definitions.

Mathlib is an imported dependency and retains its Apache-2.0 license and
contributor attribution. This repository does not relicense Mathlib.

## AI assistance and review

OpenAI's GPT-6 Astra assisted with the source proofs, internal argument checks,
literature searches, manuscript preparation, repository setup and Lean code.
The AI is credited as an automated contributor, not as a human author or
responsible maintainer. Human expert review and an independent review of the
formal statement have not been recorded.

## Formal proof architecture

The submitted targets are the two universal inequalities, line-graph
sharpness, and the cubic triangle-free equality. The formalization does not
claim that every auxiliary proposition displayed in the manuscript has a
corresponding Lean declaration.

Two constructions differed from the original manuscript's proofs while
retaining those exact conclusions. The revised paper now uses these same
constructions:

- The clique bounds use a Latin-square packing on three equal parts, together
  with internal packings, to prove `D(3q) >= q*q + 3*D(q)`. Strong induction,
  monotonicity, arithmetic and explicit finite certificates below order 21
  supply the required bound and even-order slack. This does not assume an
  exact formula for the complete-graph packing number.
- The cubic equality uses Hall's theorem to assign distinct incident edges to
  root vertices. A matching in each four-vertex incidence packet, together
  with unassigned original edges, gives the required cover. The general
  triangle-free total-graph cover proposition and the balanced-orientation
  construction are now preserved in a separate informal note outside the
  revised paper.

Euler-tour existence, alternating incidence counts, global component gluing,
packing transport and the packet constructions are proved within the Lean
development. Existential certificates remain attached to their own graph.

## Proof-aligned revision, 11 September 2026

At the author's request, the paper was rewritten to follow the checked
constructions themselves. The [proof-alignment audit](proof-alignment-2026-09-11.md)
records the substitutions, complete proof map, finite-certificate comparison
and shared trust boundary. The earlier round-robin and orientation arguments
remain accessible in the immutable source commit cited above. The stronger
orientation refinement is also retained as [an informal note](informal-orientation-cover.md).
The four headline statements, bibliography and Lean proof terms are unchanged.
