# Tuza's conjecture for line and total graphs

**Author: Samuel Massé. AI assistance: OpenAI's GPT-6 Astra. License: MIT.**

Lean proofs of the four advertised results in the
[paper](paper/tuza-line-total-graphs.pdf): the two universal
inequalities, line-graph sharpness, and cubic triangle-free equality.
Palomar verification and registration are separate from local compilation;
see [the submission record](docs/palomar-submission.md) for the current status
and [the progress record](docs/progress.md) for local proof checks.

For a graph G, let ν(G) be the largest number of pairwise edge-disjoint
triangles, and τ(G) the smallest number of edges meeting every triangle.
The manuscript proves τ(G) ≤ 2ν(G) for line graphs and total graphs of all
finite simple roots. It also proves sharpness for line graphs and the exact
equality τ(Tot(F)) = ν(Tot(F)) = 5|V(F)|/2 for cubic triangle-free roots.
These are special graph classes; the general Tuza conjecture is not resolved.

## Build and status

The reviewed 8 October 2026 revision pins Lean 4.35.0-rc4 and Mathlib commit
`1f414401f69059aa7eead47b53ee40bd38455eeb`, an ancestor of Mathlib's canonical
master branch. The project and Mathlib toolchain files agree exactly, allowing
the matching dependency cache. With the Lean toolchain installed:

```sh
lake build
```

Run `lake env lean scripts/CheckReady.lean` to require all four headline
declarations and audit their transitive axioms. The four targets retain empty
and disconnected roots. They do not separately certify every auxiliary
proposition printed in the manuscript.

The October build, 42-theorem axiom audit, local exported-statement comparison,
fresh Lean replay and NanoDa replay pass. The paper's proof and literature
reviews are recorded in [the publication audit](docs/publication-review-2026-10-08.md).
Earlier Palomar attempts passed mechanical verification but failed rendering;
none reached registration. The October revision is prepared for author review,
with its required hosted full preflight still pending. See the
[submission preview](docs/submission-preview.md) for the exact proposed scope
and remaining release steps.

- `Tuza/`: definitions and implemented proof modules.
- `Challenge.lean`: the independent, readable target statements; deliberate
  statement holes are permitted here by Comparator's design.
- `Solution.lean`: proof entry point, which never imports Challenge.
- `comparator.json`: all four advertised target declarations.
- `scripts/check-ready.ps1`: rejects missing headline proofs and unapproved
  axioms.
- `formalization.yaml`: author, sources, automation disclosure and limitations.
- `paper/`: the current manuscript, bibliography and reviewed PDF.

## Provenance and verification

The manuscript and initial finite-graph definitions come from the author's
[vmath project](https://github.com/samuelmasse/vmath). The source manuscript's
SHA-256 is recorded in [the provenance note](docs/provenance.md).

GPT-6 Astra assisted with proof development, internal argument checking,
literature search, exposition and Lean formalization. The manuscript has an
internal AI-assisted audit and finite checks. The Lean development supplies
universal proofs independently of those finite experiments. Neither the
internal audit nor kernel checking establishes expert review or novelty.
No formal proof uses a missing theorem as an axiom or relies on `native_decide`.

The revised paper follows the checked proof constructions: Latin-square
induction for the clique bounds and a Hall assignment for cubic equality.
The [proof alignment audit](docs/proof-alignment-2026-09-11.md) maps its steps
to Lean declarations. The former general orientation refinement is preserved
as a [separate informal note](docs/informal-orientation-cover.md). The
[statement audit](docs/statement-audit.md) records the four-target semantics
and shared-definition trust boundary.

[Palomar](https://palomar-registry.org/about) requires completed formal proofs,
Comparator verification, Lean and NanoDa replay, and automated review of the
formal/informal alignment. The author must inspect the actual review before
deciding on permanent registration.
