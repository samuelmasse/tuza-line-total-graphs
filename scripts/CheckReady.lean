import Solution
import Lean.Util.CollectAxioms

/-! This check must fail until all advertised proof declarations are present. -/

open Lean Elab Command in
run_cmd do
  let permitted : Array Name := #[`propext, `Quot.sound, `Classical.choice]
  let targets : Array Name := #[
    `Tuza.lineGraph_satisfiesTuza,
    `Tuza.totalGraph_satisfiesTuza,
    `Tuza.lineGraph_factor_sharp,
    `Tuza.cubic_triangleFree_total_parameters]
  let env ← getEnv
  for name in targets do
    match env.find? name with
    | some (.thmInfo _) =>
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless permitted.contains axiomName do
          logError m!"Forbidden axiom {axiomName} in {name}"
      logInfo m!"Checked {name}; axioms: {axioms}"
    | _ => logError m!"Missing proof declaration: {name}"
