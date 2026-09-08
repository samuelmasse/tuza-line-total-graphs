# Source and contribution provenance

Author and responsible maintainer: Samuel Massé.

The MIT license was selected explicitly on 8 September 2026.

## Mathematical source

`paper/main.tex` and `paper/references.bib` were copied without mathematical
changes from the author's vmath paper package, dated 7 September 2026.

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
