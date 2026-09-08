import Tuza

/-!
# Proof entry point — development in progress

The library contains supporting proofs and the line-graph sharpness witness.
The two universal inequalities and cubic equality listed in `comparator.json`
are intentionally absent until their complete proofs are implemented. This
module never imports `Challenge`: the deliberate statement holes there are
not available as premises here.

`lake build` checks implemented mathematics; it does not certify completion.
The separate release check must fail until every advertised theorem exists
and has only the permitted axioms.
-/
