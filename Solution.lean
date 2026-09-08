import Tuza

/-!
# Proof entry point

The library supplies all four declarations listed in `comparator.json`: Tuza's
inequality for every finite simple line and total root, line-graph sharpness,
and the exact cubic triangle-free total-graph parameters. This module never
imports `Challenge`; its deliberate statement holes are not proof premises.

The release check requires all four proofs and audits their transitive axioms.
Comparator and independent NanoDa replay are separate verification steps.
-/
