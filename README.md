# Tuza's conjecture for line and total graphs

**Author: Samuel Massé. AI assistance: OpenAI's GPT-6 Astra. License: MIT.**

Lean proofs of the four advertised results in the
[seven-page paper](paper/tuza-line-total-graphs.pdf): the two universal
inequalities, line-graph sharpness, and cubic triangle-free equality.
Palomar verification and registration are separate from local compilation;
see [the progress record](docs/progress.md) for the recorded status.

For a graph G, let ν(G) be the largest number of pairwise edge-disjoint
triangles, and τ(G) the smallest number of edges meeting every triangle.
The manuscript proves τ(G) ≤ 2ν(G) for line graphs and total graphs of all
finite simple roots. It also proves sharpness for line graphs and the exact
equality τ(Tot(F)) = ν(Tot(F)) = 5|V(F)|/2 for cubic triangle-free roots.
These are special graph classes; the general Tuza conjecture is not resolved.

## Build and status

The project pins Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. With the Lean toolchain installed:

```sh
lake exe cache get
lake build
```

Run `lake env lean scripts/CheckReady.lean` to require all four headline
declarations and audit their transitive axioms. The four targets retain empty
and disconnected roots. They do not separately certify every auxiliary
proposition printed in the manuscript.

- `Tuza/`: definitions and implemented proof modules.
- `Challenge.lean`: the independent, readable target statements; deliberate
  statement holes are permitted here by Comparator's design.
- `Solution.lean`: proof entry point, which never imports Challenge.
- `comparator.json`: all four advertised target declarations.
- `scripts/check-ready.ps1`: rejects missing headline proofs and unapproved
  axioms.
- `formalization.yaml`: author, sources, automation disclosure and limitations.
- `paper/`: the frozen manuscript, bibliography and PDF.

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

The [provenance note](docs/provenance.md) records two formal proof alternatives:
Latin-square induction for the clique bounds and a Hall assignment for cubic
equality. The [statement audit](docs/statement-audit.md) describes the exact
four-target scope and its shared-definition trust boundary.

[Palomar](https://palomar-registry.org/about) requires completed formal proofs,
Comparator verification, Lean and NanoDa replay, and automated review of the
formal/informal alignment. The author must inspect the actual review before
deciding on permanent registration.
