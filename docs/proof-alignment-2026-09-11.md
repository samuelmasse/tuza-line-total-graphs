# Revised paper: proof construction alignment

Date: 11 September 2026. Mode: VERIFICATION.

## Decision

Accepted for correspondence of proof constructions and dependencies after
revision. The earlier paper and Lean development proved the same four
headline statements but used different clique and cubic arguments. The author
required alignment of the proofs themselves. The revised paper now follows
the existing checked constructions. The headline statements and quantifiers
have not changed.

This is a source-level audit against the existing Lean encoding. A separate
proof agent inspected the full revised manuscript and the actual relevant
Lean modules, independently regenerated every finite base, and accepted the
construction/dependency correspondence. It shares the encoded definitions and
model family with the development. It is not independent re-encoding, human
expert review, novelty certification, or a new external kernel replay.

## Repairs

- Replaced the clique factorization proof with the formal Latin-square
  recurrence, monotonicity, explicit bases below 21 and strong induction.
  The finite recipe describes the exact literal lists checked by Lean.
- Replaced the cubic orientation proof with the formal Hall assignment,
  incidence/wedge cover and packing-cover sandwich.
- Replaced the general total-cover proof by the global monochromatic-edge
  argument used in Lean. Used the same cardinal upper bound and degree-sum
  inequality, omitting the stronger unadvertised odd-degree refinement.
- Moved the general orientation proposition out of the paper into
  [a separate informal note](informal-orientation-cover.md). It is preserved,
  but it is not claimed as part of the aligned formalized paper.
- Added formal-verification scope, source and theorem links, and explicit
  disclosure of the finite kernel checks. Preserved author and AI credit.

## Proof map

Names below are in namespace `Tuza` unless otherwise stated.

| Paper construction or argument | Lean declarations |
|---|---|
| Definitions of packing, cover and extremal numbers | `IsTrianglePacking`, `IsTriangleCover`, `trianglePackingNumber`, `triangleCoverNumber` in `Definitions.lean` |
| Three-part Latin packing and disjoint internal packings | `latinPacking_valid`, `latinPacking_card`, `latin_internal_lower_bound` |
| Recurrence and monotonicity | `complete_fin_packing_recurrence`, `complete_fin_packing_mono` |
| Literal base certificates | `cliqueBase0` through `cliqueBase20`, `completePacking_list_length_le`, `clique_packing_small` |
| Arithmetic lift and strong induction | `clique_recurrence_arithmetic`, `clique_packing_with_slack_of_small` |
| Lemma 2.1 and even-order slack | `cliqueCoverCost_le_twice_packing`, `cliqueCoverCost_add_two_le_twice_packing` |
| Unique wedge ownership; Lemma 3.1 | `lineGraph_edge_unique_owner`, `lineGraph_triangle_classification`, `triangle_edges_no_common_endpoint` |
| Simultaneous local clique packing | `exists_line_packet_packing`, `incidence_clique_packing_number`, `line_packet_cross_disjoint`, `linePacking_lower_bound` |
| Euler tours and Lemma 3.2 | `exists_eulerian_closed_walk`, `exists_eulerian_edge_coloring`, `exists_odd_edge_coloring` |
| Dummy augmentation and gluing colorings | `oddAugment_even`, `oddAugment_connected`, `exists_balanced_edge_coloring` |
| Monochromatic line cover and its cost | `monochromaticEdges_cover`, `line_cover_le_color_cost`, `balanced_choose_cost`, `seam_choose_cost` |
| Triangle-free branch of Lemma 3.3 | `exists_clique_cut`, `line_triangleFree_cover_bound` |
| High-degree slack and reserved root triangle | `line_sum_clique_slack`, `complete_two_or_four_packing_avoiding_set`, `line_packing_augment_root_triangle` |
| Connected and disconnected line assembly | `connected_line_satisfiesTuza_of_local_bounds`, `line_satisfiesTuza_of_components`, `lineGraph_satisfiesTuza` |
| Four-leaf-star sharpness | `fourLeafStar_line_parameters`, `completeGraph_fin_four_parameters`, `lineGraph_factor_sharp` |
| Minority-color total cover | `totalColorCover_covers`, `total_minority_cost`, `total_cover_upper_bound` |
| Bridge packing and compatibility with line triangles | `totalBridges_packing`, `totalBridge_disjoint_line_triangle`, `total_packing_from_line`, `total_packing_number_ge_edges_add_line` |
| Total arithmetic and theorem | `cliqueCoverCost_succ`, `total_sum_half_degrees_le_edges`, `total_satisfiesTuza_of_cover_bound`, `totalGraph_satisfiesTuza` |
| Lemma 5.1: Hall's incidence count and assignment | `total_exists_incident_edge_assignment`, using Mathlib's finite Hall theorem |
| Cubic selected incidence/wedge pairs and unassigned edges | `cubic_remaining_pair`, `cubic_total_cover_of_assignment`, `cubic_total_cover_upper_bound` |
| Cubic lower bound and exact sandwich | `cubic_total_packing_lower_bound`, `packing_number_le_cover_number`, `cubic_triangleFree_total_parameters` |

The paper groups cases for readability. In particular it isolates odd-edge
Eulerian components; the formal connected assembly uses the available
uniform `T+1` bound for the remaining Eulerian cases. Exact seam parity is
proved by `exists_eulerian_edge_coloring`, so this reordering introduces no
alternative construction or missing assumption. The sharpness paragraph
explains the same finite witness whose parameters Lean checks by reduction.

## Focused validation

The [certificate correspondence checker](../scripts/check-paper-certificates.py)
compares the recipe with the literal Lean lists, reads the counts from the
actual TeX tables, checks all 328 triangles, checks all 4,706 pairs within
the 21 lists, and verifies every required numerical bound. It passes; the
[recorded output](paper-certificates-2026-09-11.json) gives every order.
The separate agent's in-memory JavaScript reconstruction independently matched
the same lists and bounds. Both computations share the literal Lean source
and paper description as inputs; neither replaces the kernel's own checks.

The two displayed arithmetic differences are respectively
`2r²-6r-2` for even q and `2r²-4r-4` for odd q. The thresholds r >= 4 and
r >= 3 agree with q >= 7. The Hall proof, cover construction, specialized
triangle case analysis and counting agree with `CubicTotal.lean`.

The checker passes file-scoped Ruff and strict Pyright. The PDF build uses
the installed MiKTeX toolchain with package installation disabled. Build
instructions are [scripts/build-paper.ps1](../scripts/build-paper.ps1).

## Publication boundary

The [earlier mechanical run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34193414990)
accepted the four Lean targets at commit
`82f6bb5195653b60ee05ad5c662faf4d3bae7667`. This revision changes exposition,
metadata and a Lean module comment, not proof terms, graph definitions or
theorem statements. The old verification does not constitute automated review
of the revised prose. The active Palomar retry `vlq1fgk84an7` still refers
to the old immutable snapshot; the revised paper must be committed and
submitted as a new snapshot before it can be the reviewed paper of record.
