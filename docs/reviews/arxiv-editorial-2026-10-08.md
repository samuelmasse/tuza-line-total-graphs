# arXiv audience and exposition audit, 8 October 2026

Mode: VERIFICATION of exposition and publication packaging. Intended readers:
graph theorists and combinatorialists reading a math.CO preprint. This pass
does not constitute a new mathematical or novelty review.

The previous paper mixed a self-contained mathematical argument with internal
formalization and publication history. In particular, Section 6 described a
superseded proof version, an abandoned refinement, a failed Palomar rendering
stage, Challenge/Solution mechanics, and pending review. Those records remain
in the repository documentation and are omitted from the revised paper.

Changes:

- Shortened the abstract to definitions, the two graph-class inequalities,
  sharpness, the cubic equality, proof ingredients, and a brief Lean statement.
- Removed repeated comparisons between prose and implementation from proofs.
- Replaced the formalization progress report and declaration-name table with
  a concise availability and reproducibility statement. Kept a visible
  repository URL and an immutable link to the checked proof commit
  `33a75de51646668b1058c8d505e0b8d0d16bead4`.
- Kept the precise graph hypotheses, attribution of classical ingredients,
  cautious priority wording, total-graph sharpness limitation, and material
  AI-assistance disclosure. The paper does not claim the general conjecture.
- Rewrote the proof summary around local packings and the global coloring.

Validation:

- All eight theorem, lemma, and corollary statement environments are identical
  to the manuscript at the checked proof commit.
- No Lean proof, toolchain, or dependency-lock changes are part of this pass.
- BibTeX and three pdfLaTeX passes completed without final LaTeX warnings,
  missing references, or overfull boxes.
- All eight PDF pages were rendered and visually inspected.
- The arXiv archive and draft abstract/comments were regenerated from the
  revised manuscript. The source ZIP contains only `main.tex`, `references.bib`,
  and `main.bbl`; it contains no local reports or authentication material.

The earlier nine-page reviewed PDF has SHA-256
`254b234ce627184948b2a888fb9b90c03f9d13240fee01ea6b22718250165a34`.
The first editorial revision, an eight-page PDF, has SHA-256
`2699a10c4ab9c37dc27f3d3af47989efa3cbdedcbb7192e60eac7e9499a20d27`.
The historical verification manifest is preserved; it binds the earlier
snapshot. The current local manuscript/package hashes are recorded in
`paper/arxiv/submission-metadata.json`.

This editorial revision is local and uncommitted. It has not been pushed,
uploaded to arXiv, or substituted into the existing immutable Palomar intake.
The author's guided reading remains in progress.

Publishing references checked during this audit:

- [arXiv ancillary-file guidance](https://info.arxiv.org/help/ancillary_files.html)
  explicitly supports program code accompanying research articles.
- [AI4SLT, arXiv:2602.02285v2](https://arxiv.org/abs/2602.02285v2) provides an
  example of an arXiv paper linking its accompanying Lean code on GitHub.
  This is evidence of a normal practice, not an arXiv requirement to use GitHub.

## Illustrated exposition revision

At the author's request, a second exposition pass added three vector figures
and explanatory passages for research readers. The resulting paper is ten
pages. Its PDF SHA-256 is
`82e58a4175be2b4fb3a59589ecdce0d4851f4e8592b8ccb2e9740e358aad166a`.
The previous eight-page revision above is superseded by this local draft.

- Figure 1 shows a maximum triangle packing and a minimum transversal in
  `K_4`, including why their sizes are one and two.
- Figure 2 shows a three-vertex root path, its line graph, and its total
  graph, with consistent labels for original vertices and edge-vertices.
- Figure 3 contrasts star triangles with root triangles and shows how one
  shared coloring covers both. Color is supplemented by solid/dashed edges
  and filled/open vertices.
- Added the elementary bounds `nu <= tau <= 3 nu`, the constructive
  cover-versus-packing proof strategy, and the obstruction to independent
  local covers. Introductions to the clique construction, Euler balancing
  and seam repair, total-graph balancing, and Hall assignment explain their
  roles before the calculations.

All eight theorem, lemma, and corollary statement environments remain
identical to the checked proof version. Lean sources and dependency pins
are unchanged. The added examples and figures were checked against the
definitions; this is an exposition pass, not a new independent proof or
novelty audit.

All ten pages were rendered and visually inspected; figure labels and later
page breaks were rechecked after final adjustments. The final LaTeX log has
no warnings, missing references, missing characters, or box diagnostics.
The arXiv ZIP was regenerated and compiled in a fresh directory, and its
PDF text matches the reviewed local PDF. All graphics are embedded TikZ
source, so the archive still contains exactly `main.tex`, `references.bib`,
and `main.bbl`. Current hashes and the ten-page/three-figure count are in
`paper/arxiv/submission-metadata.json`.

This revision remains local and uncommitted. No arXiv upload, Palomar update,
commit, or push was performed in this exposition pass.

## Final editorial polish

The author's requested final pass tightened the introduction and the
transitions into the clique, Euler-coloring, total-graph, and cubic-root
arguments. It removed the duplicate balanced-clique explanation, replaced
the repeated `K_4` sharpness argument with a reference to Figure 1, and cut
the concluding recap of the proof roadmap. The abstract seam warning was
replaced with the concrete five-cycle example: its local cover and packing
counts are zero, while the alternating Euler cover selects one edge.

The Euler-coloring statement now stays on one page, and all seven references
appear together on the final page. The paper remains ten pages with three
figures. The mathematical scope, all eight theorem/lemma/corollary statements,
all three figure environments, and the Lean proof inputs are unchanged.

All ten pages were rendered and visually inspected, with affected pages
rechecked after the pagination changes. Compilation and a fresh-directory
build of the regenerated arXiv ZIP passed without warnings or box diagnostics;
the resulting PDF text matches the reviewed PDF. Current PDF SHA-256:
`dc53edb5acb72163d343db0c13c4875e35b2e0594fc96848e9e121bc8f8199da`.
Current archive SHA-256:
`021632d07c82364b7375a92a89ece4485413d589b1ee7dd3f274a2ab105d82a7`.
The previous illustrated draft's hash remains recorded above and in the
submission metadata. Earlier verification manifests are unchanged.

This completes the requested exposition pass. Author reading and the recorded
arXiv submission steps remain pending. No commit, push, upload, or external
submission was performed.

## Structural organization

At the author's request, the results remain in one paper with a clearer
hierarchy. A common-tools section now contains the clique-packing bounds and
the Euler-coloring lemma used by both main proofs. The line-graph and
total-graph results follow in separate sections. The exact cubic triangle-free
case is a subsection of the total-graph argument, and formal verification is
a closing note with the repository and fixed proof-version links preserved.

The paper remains ten pages with three figures. All eight theorem, lemma,
and corollary environments match the checked proof version exactly despite
their reordered numbering. All eight proof environments and all three figures
match the preceding polished draft exactly. Lean sources and dependency pins
are unchanged. This is an organizational revision, not a new proof or novelty
audit.

All ten pages were rendered and visually inspected, including the revised
page breaks and cross-references. The final compilation had no warnings or
box diagnostics. The regenerated arXiv ZIP contains exactly the three expected
source files, compiles cleanly in a fresh directory, and produces the same PDF
text as the reviewed manuscript. Current PDF SHA-256:
`a13e8b3cfda685ed599e1a06bfb59cf699c44f7452d021a45c285c31ee5a28b8`.
Current archive SHA-256:
`18ccb09e90642d1f3b97b49c78bba9b9ffca7dca77ce45efd9c8fb7e88cd6dd5`.
The preceding polished PDF hash is preserved above and in submission metadata.

This revision is local and uncommitted. Author reading and the recorded arXiv
submission steps remain pending; no push, upload, or external submission was
performed.

## arXiv draft preparation

Draft `8202368` was started in `math.CO` (Combinatorics). The author approved
the arXiv Submission Agreement and CC BY 4.0; both choices were entered and
confirmed in the submission form. arXiv then blocked progression to file
upload because the account requires endorsement for this category.

The endorsement page generated a request and reported sending its code to
the author's registered Arizona email address. An eligible mathematics author
must supply the endorsement. No personal outreach was sent or forwarded.
The source package and its recorded hashes remain unchanged; no source upload,
arXiv compilation, completed metadata entry, or final submission has occurred.
The resumable draft and current remaining steps are recorded in
`paper/arxiv/submission-metadata.json`.

For personal endorsement, Andrea Munaro is a relevant candidate because the
manuscript cites his work on triangle packings and transversals and his thesis's
line-graph result. His [public homepage](https://andreamunaro.github.io/) lists
`andrea.munaro@unipr.it`. On 8 October 2026, the authenticated
[arXiv eligibility page](https://arxiv.org/auth/show-endorsers/2609.24684)
explicitly confirmed that he can endorse for `math.CO`. Eligibility does not
imply willingness, manuscript review, or endorsement; he has not been contacted.

arXiv's [current endorsement guidance](https://info.arxiv.org/help/endorsement.html)
permits approaching eligible authors of related work and requires at least one
positive endorsement. The
[January 2026 policy announcement](https://blog.arxiv.org/2026/01/21/attention-authors-updated-endorsement-policy/)
confirms that an institutional email alone no longer qualifies a first-time
author for automatic endorsement. The endorsement request code is available
in the author's arXiv account and email, and is not stored in this tracked note.
