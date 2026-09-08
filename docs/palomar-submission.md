# Palomar submission

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
cache. Validation and a new immutable submission snapshot are pending.
