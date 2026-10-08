# Palomar submission

**Current status, 8 October 2026:** no registration. The September retry
also passed mechanical verification and failed rendering. An updated,
locally checked revision is prepared for the author's review; it has not been
submitted. See [the proposed submission](submission-preview.md).

## Historical intake, 8 September

Submitted on 8 September 2026 after the author's confirmation of the exact
repository, commit, configuration and maintainer relationship.

- Submission: `81h38g7ma5ji`.
- Repository: `samuelmasse/tuza-line-total-graphs`.
- Submitted commit: `362032ce3034e50b4a4d25d8d67fa103ab51d342`.
- Comparator configuration: `comparator.json`.
- Declared relationship: `maintainer`.
- [Source CI](https://github.com/samuelmasse/tuza-line-total-graphs/actions/runs/34190469370): passed.
- Fresh local `leanchecker --fresh Solution` replay: passed.
- [Palomar mechanical run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34190966591): failed before proof checking.

The authenticated GitHub CLI flow established the required repository-write
proof and identified a GitHub account through a secret gist. Palomar documents
that these two proofs do not establish that the two actors are the same
account. The temporary tag and secret gist were deleted immediately after
verification. No credential or private review is included in this record.

Submission is distinct from registration. Comparator, independent NanoDa
replay and Palomar's automated review must complete before an author can
decide on registering the actual returned review. No registration is claimed
at this checkpoint.

## Dependency ancestry repair

The first mechanical run rejected the Mathlib release pin
`0df444a360eaa60ab8c11dca51a86af692955474`: it is not an ancestor of the
canonical `master` branch. Its parent
`db584cd6d46c92f209a44c0f1c829460d327499d` is on that branch, and the exact Git
diff between the two revisions changes only Mathlib's `lean-toolchain` file.
All mathematical source and Mathlib manifest entries are identical.

The repair pins the canonical parent and retains the patched Lean 4.33.1
kernel. CI builds from source instead of requesting the incompatible release
cache. The [clean source CI run](https://github.com/samuelmasse/tuza-line-total-graphs/actions/runs/34191958684)
passed, including the Challenge build, the 42-theorem axiom audit and all four
headline proof checks. A local cache probe using the explicit Lean 4.33.1 Lake
executable in the Mathlib root downloaded and decompressed 973 modules; the
subsequent 1,297-job rebuild and four-target readiness check also passed.
The repair changes no manuscript, Challenge, Solution or proof-module source.

## Corrected intake

After the author's explicit agreement to the corrected tuple, Palomar accepted
a new submission at 06:08:46 UTC on 8 September 2026:

- Submission: `rp7erx040zjk`.
- Repository: `samuelmasse/tuza-line-total-graphs`.
- Submitted commit: `82f6bb5195653b60ee05ad5c662faf4d3bae7667`.
- Comparator configuration: `comparator.json`.
- Declared relationship: `maintainer`.
- [Mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34193414990): passed.

The temporary verification tag and secret gist were deleted. Credentials are
encrypted in ignored local state. The first submission remains settled and is
not being retried. The corrected submission passed mechanical verification;
automated review and registration are blocked by the rendering failure below.

Palomar's current verifier runs a full Mathlib build during trusted dependency
replay. The canonical-parent cache predates the retained kernel patch, so this
can require substantially more rebuilding than the project's imported closure.
For context, the source-identical Mathlib 4.33.1 release's
[upstream cache-publishing run](https://github.com/leanprover-community/mathlib4/actions/runs/32480253855)
passed, including a roughly 46-minute build and subsequent tests on upstream's
own runners. This supports full-dependency compatibility; it is not a Palomar
verification result or a runtime estimate for Palomar's runner.

## Mechanical verification accepted

Palomar recorded verification success at 10:00:19 UTC on 8 September 2026.
The [downloaded mechanical report](palomar-mechanical-report-2026-09-08.json)
records status `pass`, no errors and no warnings. Comparator compared all four
advertised declarations, and both the independent NanoDa kernel and Lean's
default kernel accepted the Solution. The report's SHA-256 is
`14eec62004f4cd8af72fd3a495a5fc77c7b284a9a72b940435c7b29484cd5174`.
Its recorded full-dependency replay took approximately 3 hours 40 minutes;
the subsequent Comparator phase took approximately 59 seconds.

These checks certify the encoded claims and permitted axioms. They do not
constitute an editorial review, a novelty finding or registry publication.

## Challenge rendering blocker

Palomar tried the Challenge renderability check three times, starting at
10:02:56, 11:38:49 and 13:00:10 UTC. The
[last rendering run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34229319497)
failed during Mathlib cache discovery. Its report records
`palomar.render_failed`, owner `palomar`, stage `workspace`, retryable `true`
and repairable `false`. The cache client exits before reporting any cache keys;
its diagnostic points to the differing project and Mathlib toolchain files.

The API status became `verification-error` at 13:03:37 UTC, after the successful
mechanical result. No automated review has started, and the submission is not
registered. Palomar's diagnostic advises retaining the submitted repository
snapshot, retrying the same commit later, and reporting the rendering workflow
URL if the error recurs. A report is prepared locally for the author's approval;
no GitHub issue or message to Palomar has been sent.

## Author-requested retry on 11 September 2026

The author requested another attempt. The previous intake still reported the
same rendering failure, and the upstream patch-release fix remained unmerged.
Palomar accepted one fresh intake at 19:37:32 UTC, retaining the exact approved
repository, commit, Comparator path and maintainer relationship:

- Submission: `vlq1fgk84an7`.
- Submitted commit: `82f6bb5195653b60ee05ad5c662faf4d3bae7667`.
- [New mechanical run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34639843678): subsequently passed.

The temporary ownership-verification tag and secret gist were deleted after
intake. Access credentials are encrypted in ignored local state, with the
previous submission's credential retained separately. No proof, dependency,
toolchain or manuscript was changed for the retry. The new intake does not yet
establish that the rendering blocker is resolved; automated review and the
author's decision on the actual review remain prerequisites for registration.

## Retry outcome and October repair

The [retry's final rendering run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/34667477675)
failed at workspace cache discovery, again before automated review. The report
classified `palomar.render_failed` as service-owned, retryable and not a
submission repair. Retrying the unchanged snapshot did not remove the
toolchain/cache mismatch. No registry entry was found for this project in the
public registry search on 8 October.

Current Palomar policy requires exact agreement between the project and the
resolved Mathlib `lean-toolchain`, Lean at least 4.35.0-rc2, and `module`
headers in committed Lean files. This revision uses matching 4.35.0-rc4
toolchains and a canonical Mathlib pin. Local proof checks pass, but renderer
success is not inferred from them.

The current [agent intake protocol](https://submit.palomar-registry.org/llms.txt)
also requires a passing **full** hosted mechanical preflight before intake,
using the exact source commit and pinned reusable workflow. The prepared
workflow pins pipeline `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, requests
`mode: full` and `execution_profile: palomar-standard-v1`, and names
`comparator.json`. Its configuration was checked against that workflow's
declared inputs. It has not yet been dispatched.

After the author approves committing and pushing the reviewed files, freeze
the full resulting SHA and run this preflight. Require its report to say
`pass` for exactly that repository, SHA, configuration and pipeline. Then
show the author the exact intake tuple for submission approval. Historical
September authorization is not authorization for a different source SHA.
Registration still requires the author's decision on the actual returned
Palomar review.
