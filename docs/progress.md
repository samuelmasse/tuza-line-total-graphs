# Formalization progress

Started 8 September 2026. Mode: VERIFICATION of the frozen manuscript.

The scope is the finite simple graph theorems in `paper/main.tex`. Vertex sets
may be empty; roots may be disconnected or contain triangles. The only extra
hypotheses are the explicitly named cubic triangle-free equality case.

## Headline obligations

| Declaration in Challenge | Manuscript result | Lean proof status |
|---|---|---|
| `Tuza.lineGraph_satisfiesTuza` | Theorem 1.1: every finite simple line graph | Missing |
| `Tuza.totalGraph_satisfiesTuza` | Theorem 1.2: every finite simple total graph | Missing |
| `Tuza.lineGraph_factor_sharp` | Sharp factor two, witnessed by a four-leaf star | Proved by kernel reduction of the explicit finite witness |
| `Tuza.cubic_triangleFree_total_parameters` | Corollary 1.3: τ = ν = 5n/2 | Missing |

## Dependency plan

1. Freeze finite triangle, edge-packing and edge-cover semantics; prove that
   explicit compatible witnesses imply the numerical inequality and that any
   packing is no larger than any cover.
2. Define total graphs, retain Mathlib's line graphs, prove unique wedge
   ownership and the complete triangle classifications.
3. Formalize complete-graph packing constructions and their even-order slack.
   Arithmetic identities alone do not discharge this obligation.
4. Construct the balanced edge coloring, including the single odd Eulerian
   seam per connected component. Prove all parity and component facts.
5. Combine local witnesses into genuine disjoint global packings and covers;
   prove the three seam-repair branches and the two headline inequalities.
6. Formalize balanced orientations, the sharper triangle-free cover, the cubic
   equality, and the explicit sharpness witness.
7. Compare the exact Challenge/Solution declarations, replay the proofs, audit
   source alignment, complete the Palomar review process and obtain the
   author's decision on registration.

The initial milestone has a standalone project with compiled finite-graph
definitions, certificate lemmas, graph operators, the unrestricted line-graph
triangle classification, unique wedge ownership, clique parity identities,
the monochromatic-edge triangle cover and the sharpness witness. Fixed
representation checks cover `K_4`, the empty total graph, a single-edge total
graph and the line graph of a triangle. Every remaining universal proof is
listed above rather than replaced by a stub theorem in Solution.

Total-graph bridge construction, forced bridge identification for two original
vertices and the incidence-triangle construction also compile.

## Validation of the initial milestone

- `lake build`: passed for all implemented modules and Solution.
- `lake build Challenge`: passed with exactly four deliberate statement-hole
  warnings. Those declarations are not imported by Solution.
- `lake env lean scripts/Audit.lean`: 24 named proofs passed the axiom check;
  only `propext`, `Classical.choice` and `Quot.sound` were found. The
  [recorded output](axiom-audit-2026-09-08.txt) identifies each checked theorem.
- `lake env lean scripts/CheckReady.lean`: correctly failed on the two universal
  inequalities and cubic equality, while accepting the sharpness proof. See
  [the readiness output](readiness-check-2026-09-08.txt).
- Metadata passed the upstream v0.4 JSON schema. The copied Challenge
  definitions, four target declarations, statement size and absence of
  Challenge imports/proof holes in the implementation were checked.
- Copied manuscript, bibliography and PDF hashes match the frozen source.

No Palomar intake, Comparator execution or NanoDa replay has occurred.

## Trust boundary

Ordinary Lean compilation checks proof terms using its kernel. Tactics are
proposal tools. Challenge holes have no evidential status. No claim of
Comparator or NanoDa replay is made until those tools have actually passed.
Statement alignment and novelty remain distinct from kernel checking.

The parent conjecture's closure status is unchanged by packaging or by proving
proper-special-class results. This project certifies the manuscript's scope.

## Performance

Use the installed Lean release and existing Mathlib cache. Initial whole-Mathlib
import dependency scanning was too broad; imports were narrowed to graph,
finite-set and required tactic modules. No exhaustive graph search or bounded
computation is needed for the formalization. Build only changed modules during
development, then check the small standalone project at an integration point.
The first narrowed definition build took 89 seconds; subsequent changed-module
builds took about 12–29 seconds. Whole-machine physical RAM was 16.7–17.3 GiB
in the recorded samples. Local dependency-cache reuse is ignored build state;
the tracked manifest contains public Git URLs and full commit pins.
