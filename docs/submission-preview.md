# Proposed Palomar submission

Prepared 8 October 2026 for Samuel Massé's review. **Not submitted.**

On 8 October the author authorized committing and pushing this revision and
running the full hosted preflight. Intake and registration remain separate.

[Read the reviewed paper](../paper/tuza-line-total-graphs.pdf) ·
[Publication audit](publication-review-2026-10-08.md) ·
[Metadata to be submitted](../formalization.yaml)

## Submission fields

| Field | Proposed value |
| --- | --- |
| Title | Tuza's conjecture for line and total graphs |
| Author and responsible maintainer | Samuel Massé |
| Repository | [samuelmasse/tuza-line-total-graphs](https://github.com/samuelmasse/tuza-line-total-graphs) |
| Source commit | The release commit containing this reviewed revision; its full SHA will be reported with the hosted preflight result |
| Comparator configuration | `comparator.json` |
| Submitter relationship | `maintainer` |
| Source manuscript | `paper/main.tex`, revised 8 October 2026; 9-page accompanying PDF |
| License | MIT |
| Classification | math.CO; MSC 05C35, 05C70 |
| Lean / Mathlib | Lean 4.35.0-rc4; Mathlib `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| AI disclosure | GPT-6 Astra assisted with proof development, exposition and formalization; Codex assisted with the October review and compatibility work |

The review baseline `09dbb9a839ebf205891f7e14bf6c8167b4e67970` is **not**
the proposed submission SHA: it does not contain the reviewed changes.
Freeze the release SHA after commit and show it with the preflight result.

## Description in formalization.yaml

For a finite simple graph, let nu be the maximum number of pairwise
edge-disjoint triangles and tau the minimum number of edges meeting all
triangles. This project proves tau <= 2 nu for the line graph and the total
graph of every finite simple root. The line-graph factor two is sharp.
For cubic triangle-free roots on n vertices, the total graph satisfies
tau = nu = 5n/2. Empty and disconnected roots are included. These graph
classes do not resolve Tuza's conjecture for arbitrary graphs.

## Exact advertised claims

| Paper claim | Lean declaration |
| --- | --- |
| Every finite simple root H satisfies tau(L(H)) <= 2 nu(L(H)) | `Tuza.lineGraph_satisfiesTuza` |
| Every finite simple root F satisfies tau(Tot(F)) <= 2 nu(Tot(F)) | `Tuza.totalGraph_satisfiesTuza` |
| A line graph attains nu = 1 and tau = 2 | `Tuza.lineGraph_factor_sharp` |
| For cubic triangle-free F, 2 tau(Tot(F)) = 2 nu(Tot(F)) = 5 card(V(F)) | `Tuza.cubic_triangleFree_total_parameters` |

Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`. The four
deliberate Challenge holes are isolated from Solution. No proof holes or
additional axioms occur in the implementation.

## Review outcome and limits

The paper's proofs survived the skeptical pass, all finite certificates match
the Lean witnesses, and the current build, axiom audit, exported-statement
comparison, Lean replay and NanoDa replay pass. All nine PDF pages were
visually inspected. Established method attributions have been corrected.

The literature search located no earlier theorem covering these exact full
classes. It did not certify novelty: the original Guruswami 1999 and Tuza
1990 full texts were inaccessible, and no specialist has reviewed the work.
The paper retains cautious priority language. The September Palomar reports
are historical mechanical acceptance, followed by rendering failure; they
do not constitute review or registration of this revision.

## Remaining release sequence

1. Author authorization to commit and push the reviewed changes on main was
   received on 8 October. Publish that revision and freeze its full SHA.
2. Run `.github/workflows/palomar-preflight.yml` against the resulting SHA.
   It calls pipeline `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` in full mode
   with execution profile `palomar-standard-v1`. Require a downloaded report
   with status `pass`, matching the repository, source SHA and comparator path.
3. Show the exact immutable tuple and preflight report to the author before
   creating a new Palomar intake. The current preview is not a submitted form.
4. After verification and automated review, show the actual returned review.
   The author decides separately whether to register it permanently.

The hosted preflight is a current Palomar requirement, not an unresolved
mathematical lemma. Local checks do not substitute for it or establish that
the remote renderer now works.
