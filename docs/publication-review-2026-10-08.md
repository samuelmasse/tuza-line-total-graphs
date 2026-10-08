# Publication review, 8 October 2026

Mode: VERIFICATION. Baseline: `09dbb9a839ebf205891f7e14bf6c8167b4e67970`.

The scope is the four declarations in `comparator.json`: the two universal
line/total inequalities, line-graph sharpness, and cubic triangle-free equality.
Finite simple roots, including empty and disconnected roots, remain fixed.
The task reviews the manuscript, its formal interpretation, literature claims,
dependency boundary, PDF, metadata and current Palomar intake requirements.
No new parent-conjecture claim is made. Parent impact: special-class-result,
NEUTRAL; universal-obligation delta zero.

## Verification contract

Acceptance requires a fresh project build, the separate Challenge build, all
four theorem and transitive-axiom checks, exact comparison of the duplicated
definition bodies, complete finite-certificate correspondence, reviewed paper
proofs, current policy preflight and visual PDF inspection. The independent
review passes share the baseline statement and source encoding. They are
AI-assisted audits, not external human review or novelty certification.
The September Comparator/Lean/NanoDa report remains evidence only for its
immutable historical snapshot. October local replay is recorded separately
below; no hosted October verification or registration is claimed.

## Dependency and build plan

Palomar's live minimum on this date is Lean 4.35.0-rc2. Its current policy
requires module headers and exact toolchain agreement with pinned Mathlib.
The September dependency mismatch cannot be reused for a new submission.
The selected compatible pair is Lean 4.35.0-rc4 and Mathlib commit
`1f414401f69059aa7eead47b53ee40bd38455eeb` (release tag v4.35.0-rc4).
The user approved installing this Lean release on Windows.

This is compiler replay, not a graph search. The workload is the 38 existing
Lean source files (including two audit scripts) and their dependency closure,
plus the new exported-statement comparison helper.
Use Mathlib's authenticated release cache and Lake's dependency scheduler;
do not rebuild unrelated Mathlib targets. Calibrate on Definitions, Operators
and Challenge before the full local project build. Native code and GPU search
do not apply. No solver campaign or new finite bound is needed.
Build locally on the existing 16-core Ryzen 9950X. The Ubuntu inventory has
no Lean toolchain; installing a second toolchain there adds setup and transfer
without independent re-encoding, so this run uses Windows. Monitor aggregate
physical memory and stay below 54 GiB. Cache setup, representative build and
full-project timing will be recorded separately.

## Publication boundary

Do not commit, push, create a Palomar intake or register during this review.
Prepare the actual corrected files, rendered paper and exact proposed metadata
for the author's review. A submission SHA can only be frozen after the author
authorizes committing and publishing the reviewed working tree. The author
also retains the separate decision on Palomar's returned review.

## Checks and findings

### Accepted mathematics and attribution corrections

The [skeptical proof pass](reviews/skeptical-mathematics-2026-10-08.md) accepted
all four frozen paper claims, the packet ownership argument, all three seam
branches, total-graph arithmetic and the Hall assignment. It independently
reconstructed the 21 finite bases: 328 triangles and 4,706 pair checks.
The separate recipe-to-Lean-list checker also passed. These passes share the
paper's statement translation; they are not independent human peer review.

The [literature pass](reviews/novelty-2026-10-08.md) found two missing or weak
method attributions. The revised paper cites Guruswami's 1999 maximum-cut
method and Hanaka--Kobayashi--Sone's accessible account, and explicitly credits
the cyclic finite packing to Sebő through Munaro's thesis. The four headline
claims and all mathematical proof constructions are unchanged. No earlier
full-scope headline statement was located. The original Guruswami and Tuza
1990 full texts were inaccessible; priority and significance remain open to
specialist review. The paper makes no definitive first-proof claim.

### Current mechanical checks

| Check | Result |
| --- | --- |
| Matching Lean / Mathlib release | 4.35.0-rc4 on both; exact toolchain-file agreement |
| Mathlib provenance | `1f414401f69059aa7eead47b53ee40bd38455eeb`; canonical-master ancestor (GitHub comparison: ahead 0, behind 39 when checked) |
| Imported dependency cache | 1,281 cache objects downloaded and decompressed successfully |
| Representative Definitions / Operators / Challenge build | Pass; 1,032 jobs, 11.02 seconds |
| Full project build after API repairs | Pass; 1,333 jobs, 30.58 seconds |
| Headline and supporting axiom audits | All four headlines and 42 named theorems pass; only permitted axioms |
| Fresh Lean replay | `lake env leanchecker --fresh Solution`, exit 0 |
| Exported proof replay | `leanchecker --from-export`, accepts Solution |
| Independent NanoDa replay | Exit 0, with unpermitted axioms configured as hard errors; initial run 3.12 seconds |
| Exact exported-statement comparison | All four declarations and their referenced definitions accepted by Lake's `compareAt`; transitive axioms accepted by `checkAxioms` |
| Hostile audit control | Removing `Classical.choice` from permission list is rejected as an illegal axiom |
| Source policy checks | 39 Lean files use module headers; no implementation holes, custom axioms, unsafe or native_decide; no Solution-side Challenge import |
| Challenge boundary | 225 lines, 8,116 bytes; four deliberate holes; both copied definition bodies exactly match implementation |
| Metadata | Current upstream formalization.yaml v0.4 schema accepts |
| PDF | 9 pages, no LaTeX warnings or overfull boxes; all pages rendered and inspected |

The migration needed nine explicit argument-name adaptations in three files
after Mathlib made `mem_incidenceFinset` arguments implicit. Audit scripts
needed `import all` of each theorem's defining module: that import mode does
not propagate through ordinary public imports. The checks continue to require
actual theorem declarations. New Mathlib style lints are non-fatal and do not
indicate proof holes; no linter was disabled.

Whole-machine RAM samples stayed approximately 23--25 GiB, below the 54 GiB
ceiling. There was no exhaustive search or remote compute campaign. Local
kernel/export checks use the installed official Lean binaries and the reviewed
workspace; their trust boundary is weaker than Palomar's isolated clean build.
Lake's sandboxed CLI requires Linux namespaces and was not run on Windows.
The local comparison calls its public comparison routines on serialized exports,
not on proof `.olean` files loaded into the comparison process.

The compact [verification manifest](reviews/verification-2026-10-08.json)
binds the reviewed proof sources, metadata and paper to SHA-256 hashes.
The [axiom output](reviews/axioms-2026-10-08.txt) records the 42 named checks.

### Reproducing the local export comparison

The helper `scripts/CompareExports.lean` accepts the comparator JSON and two
exports generated by the pinned `leanexport`. Export all four target names,
all permitted axioms, `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` and the
primitive names listed in the helper from each of Challenge and Solution:
`lake env leanexport MODULE -- NAMES...`. Preserve UTF-8 output bytes.

Compile the helper against the bundled libraries (the export parser is not
available to plain `lean --run` on this Windows distribution):

```powershell
lake env lean -c tmp/verification/CompareExports.c scripts/CompareExports.lean
lake env leanc -o tmp/verification/compare-exports.exe tmp/verification/CompareExports.c -lLake -lLeanExport
./tmp/verification/compare-exports.exe comparator.json tmp/verification/challenge.ndjson tmp/verification/solution.ndjson
```

This compares the fixed theorem-only configuration in this repository; it
does not implement definition-hole submissions or replace the hosted workflow.

### Remaining publication gates

The author authorized committing and pushing this revision on 8 October,
after reviewing the prepared packet. At the time of release preparation there
is no full hosted preflight report and no new intake. The workflow matches current Palomar inputs and
is pinned to `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`; it must produce a
matching `pass` report on the eventual source SHA before intake. Renderer
compatibility and Palomar's review remain untested on that revision.

The corrected paper and [submission preview](submission-preview.md) are ready
for the author's review. No commit, push, submission or registration was made
during the review itself. Commit, push and full hosted preflight are the
authorized next release actions; intake awaits the resulting report and exact SHA.
