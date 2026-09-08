# Completion campaign

Authorized 8 September 2026: continue the entire formalization and Palomar
submission workflow. Mode remains VERIFICATION of the frozen paper.

The acceptance condition is the exact four-theorem Challenge/Solution pair,
with no unapproved proof axioms, accepted by the required independent replay
and Palomar's submission checks. A successful supporting-library build does
not meet that condition. The final registration decision follows review of
Palomar's actual report under its submission protocol.

## Proof dependency order

1. Transport and combine packing/cover witnesses, preserving cardinalities,
   actual edge membership and pairwise disjointness.
2. Prove uniform complete-graph packing bounds and even-order slack.
3. Prove the needed balanced edge coloring constructions.
   Pinned Mathlib currently gives necessary Eulerian degree conditions but
   leaves the existence direction as a TODO; do not assume that missing result.
4. Formalize incidence packets and count the compatible global certificates.
5. Prove the two universal operator-class inequalities and cubic equality,
   update the exact statement/proof alignment, and run release verification.
6. Submit the immutable public proof snapshot and process the actual review.

The completed cubic proof uses Hall's theorem instead of the planned
orientation route. Only the four advertised targets are the acceptance scope;
the general triangle-free total-cover proposition is not separately formalized.

Every existential certificate stays bound to its graph and construction.
Alternative proofs may be used when their exact mathematical statement is
unchanged; record a source-proof divergence before submission.

## Computation plan

The repeated workload is Lean elaboration and kernel checking, not a graph
search. Use narrow imports, cached pinned dependencies and changed-module
builds. The measured initial setup used 12–29 seconds per changed proof module
and about 17 GiB of whole-machine RAM. Independent module checks may run
concurrently, with memory monitoring below 54 GiB. Benchmark a materially slow
proof or tactic before expanding it; use structural lemmas and proof-producing
arithmetic instead of enlarging finite computations or substituting native
evaluation. GPU and native solver routes are not useful for these proof terms.

Stop a proposed implementation route if a mathematical counterexample or a
statement mismatch is found; repair the route or report the precise issue.
Do not submit partial proofs or replace the registered target with supporting
lemmas. The general Tuza conjecture is outside the manuscript's scope.
