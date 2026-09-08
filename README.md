# Tuza's conjecture for line and total graphs

**Author: Samuel Massé. AI assistance: OpenAI's GPT-6 Astra. License: MIT.**

Lean formalization **in progress** of the [seven-page paper](paper/tuza-line-total-graphs.pdf).
The two headline theorems are not yet proved in Lean. This repository has not
been submitted to or registered with Palomar.

The implemented proofs include the line-graph triangle classification,
unique wedge ownership, packing/cover certificate lemmas, clique parity
identities and the sharpness witness `L(K_{1,4})` with `(ν, τ) = (1, 2)`.

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

`lake build` checks implemented supporting proofs. It does **not** mean that
the manuscript has been completely formalized. See the exact outstanding
obligations in [the progress record](docs/progress.md).

- `Tuza/`: definitions and implemented proof modules.
- `Challenge.lean`: the independent, readable target statements; deliberate
  statement holes are permitted here by Comparator's design.
- `Solution.lean`: proof entry point, which never imports Challenge.
- `comparator.json`: all four advertised target declarations; the two universal
  inequalities and cubic equality are still absent from Solution.
- `scripts/check-ready.ps1`: rejects missing headline proofs and unapproved
  axioms. This check must fail while formalization is incomplete.
- `formalization.yaml`: author, sources, automation disclosure and limitations.
- `paper/`: the frozen manuscript, bibliography and PDF.

## Provenance and verification

The manuscript and initial finite-graph definitions come from the author's
[vmath project](https://github.com/samuelmasse/vmath). The source manuscript's
SHA-256 is recorded in [the provenance note](docs/provenance.md).

GPT-6 Astra assisted with proof development, internal argument checking,
literature search, exposition and Lean formalization. The manuscript has an
internal AI-assisted audit and independent finite checks. Those checks do not
establish universal Lean proofs, expert review or novelty. No formal proof may
use a missing theorem as an axiom or rely on `native_decide`.

[Palomar](https://palomar-registry.org/about) requires completed formal proofs,
Comparator verification, Lean and NanoDa replay, and automated review of the
formal/informal alignment. The author must inspect the actual review before
deciding on permanent registration.
