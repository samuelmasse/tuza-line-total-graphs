# Manuscript publication audit

Date: 11 September 2026. Mode: VERIFICATION.

Historical assessment before the author's request to align the actual proof
constructions. The recommendation below to retain the alternative arguments
was superseded by the [completed proof-alignment revision](proof-alignment-2026-09-11.md).

## Recommendation

Revise the existing short paper; do not replace its proof architecture. The
manuscript's four headline conclusions agree with the frozen Challenge and
the recorded statement audit. Palomar's mechanical report accepted those
targets with Comparator, Lean and NanoDa. The manuscript still describes the
earlier informal-only presentation and omits this formal verification.

This pass read the manuscript and bibliography, the formalization metadata,
the proof-architecture and statement audits, and the previous internal referee
and novelty reports. It checked the logical outline of the written arguments;
it did not rerun the kernels or provide independent human expert review.
No new mathematical gap was identified in this pass. Novelty remains
provisional, and the general Tuza conjecture is not resolved by these classes.

## Changes before the next paper release

1. **Add a formal verification and availability section.** Map Theorems 1.1
   and 1.2, the sharpness assertion, and Corollary 1.3 to the four Lean
   declarations. Link the public repository and exact checked commit
   `82f6bb5195653b60ee05ad5c662faf4d3bae7667`. Record Lean 4.33.1,
   the pinned Mathlib revision, the three permitted axioms, and successful
   Comparator/Lean/NanoDa verification. Refer build details to repository
   documentation. Do not describe this as completed Palomar registration.
2. **Describe proof differences accurately.** The paper's clique argument
   uses complete-graph factorizations; Lean uses a Latin-square recurrence and
   kernel-checked finite certificates below order 21. The paper derives cubic
   equality from balanced orientations; Lean uses a Hall assignment. These
   prove the same headline statements. Proposition 5.1's general
   triangle-free cover is proved in prose but is not separately formalized.
   No wholesale rewrite to imitate Lean is needed.
3. **Qualify the computation wording.** The sentence at the end of the
   introduction saying no computation is needed is appropriate for the
   written argument, but should be explicitly scoped to it once the formal
   proof is discussed. The acknowledgement should distinguish the analytic
   proofs, finite corroborating tests, and kernel-checked finite certificates
   used in the alternative formal proof.
4. **Tighten the contribution and prior-art paragraph.** Keep the cautious
   priority wording. Clearly identify arbitrary roots, rather than
   triangle-free roots, as the line-graph extension, the all-root total-graph
   result, and the exact cubic equality. Keep the classical clique construction
   attribution. Verify the earliest attribution of the triangle-free line
   subclass directly in the original literature before assigning priority;
   the earlier audit inspected only the abstract of Tuza's 1990 paper.
   Negative searches and kernel acceptance do not settle novelty.
5. **Prepare release metadata.** Retain Samuel Massé and the GPT-6 Astra
   acknowledgement, adding formalization to the latter's listed contributions.
   Use the actual revision date. Add an author-selected contact address and
   affiliation/ORCID only if supplied and appropriate for the chosen venue.
   Publish matching TeX, bibliography, PDF and source-revision references.

## Small clarity improvements

- Define `delta_F(v)` explicitly when introducing the total-graph packets.
- In the exceptional line-graph seam argument, illustrate the degree-four
  choice that avoids a prescribed wedge. A small diagram is optional; the
  existing text already supplies a valid construction.
- Add one sentence near the main theorems saying the general conjecture
  remains outside their scope. The current title already includes Tuza and
  identifies the two graph classes correctly.
- Keep the orientation refinement: it gives an additional general
  triangle-free bound beyond the formally advertised cubic equality.

## Suggested formalization paragraph

The two main inequalities, line-graph sharpness and the cubic triangle-free
identity have been formalized in Lean 4. The corresponding four declarations
at repository commit `82f6bb5195653b60ee05ad5c662faf4d3bae7667` passed
Palomar's Comparator check and replay by Lean's kernel and the independent
NanoDa checker. The formal proofs use only propositional extensionality,
classical choice and quotient soundness. They retain finite simple roots,
including empty and disconnected cases. For the clique bound and cubic
identity, the formal development uses alternative constructions described
in the repository. Proposition 5.1 and the standalone balanced-orientation
argument are not separately formalized. These checks concern the encoded
statements; they do not establish novelty or human expert review.

## Publication evidence and remaining review

The [successful mechanical run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34193414990)
and [saved report](palomar-mechanical-report-2026-09-08.json) establish the
recorded formal-verification outcome. The manuscript's main proof map and
coverage boundary are in [the statement audit](statement-audit.md) and
[provenance note](provenance.md).

A focused web refresh found no exact headline collision; this was not a new
exhaustive novelty audit. The live [Gupta preprint record](https://arxiv.org/abs/2608.06538)
still lists version 1 and the maximum-degree-seven scope. The
[Tuza publisher record](https://link.springer.com/article/10.1007/BF01787705)
confirms the parent formulation and bibliographic details but provides only
an abstract without subscription access. The attempted live retrieval of
Munaro's thesis timed out; the earlier recorded page-specific audit remains
the evidence for that comparison. No new earliest-attribution claim is made.

For journal submission, a graph theorist should check the claimed novelty and
the written proof, especially the seam repair and the unformalized general
triangle-free refinement. This is a recommendation for expert scrutiny, not
a claim that the existing kernel checks failed or a prerequisite imposed by
Palomar for an ordinary submission.

The active retry `vlq1fgk84an7` reads an immutable earlier snapshot. No
manuscript or proof file was changed during this audit. A revised paper would
be a new version; including it in Palomar's review requires an intake of the
new commit rather than assuming the current retry will pick it up.
