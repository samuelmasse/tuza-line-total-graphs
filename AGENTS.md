# Tuza line and total graphs

Author: Samuel Massé. Credit OpenAI's GPT-6 Astra for material AI assistance.
License: MIT, selected by the author.

This is a standalone Lean formalization of `paper/main.tex`, developed for
eventual Palomar registration. It does not claim the general Tuza conjecture.

- Work directly on main; do not use branches or worktrees without a request.
- Do not commit or push without the user's explicit authorization.
- Keep the formalization's actual status visible in README and docs/progress.md.
- Use VERIFICATION mode: freeze the paper statements, preserve all quantifiers,
  and distinguish a compiled supporting lemma from a completed headline proof.
- Do not add custom axioms, native_decide, unsafe proof shortcuts, or holes to
  Solution or its dependencies. Deliberate holes belong only in Challenge.
- Challenge must import only pinned Mathlib/Lean sources. Solution must never
  import Challenge. Keep duplicated public definitions identical and auditable.
- Build the changed modules and audit headline axioms before claiming completion.
- Read Palomar's current policy and agent protocol before intake. Do not submit
  an unfinished formalization. Registration requires the user's decision on
  the actual returned review.
- Use installed Lean tooling and cached dependencies when possible; do not
  install system software without approval. Keep aggregate RAM below 54 GiB.
- Keep machine-specific paths out of tracked build configuration and scripts.
