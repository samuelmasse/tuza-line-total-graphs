import Solution
import Lean.Util.CollectAxioms

/-! Local axiom audit of implemented results. This does not replace Comparator. -/

open Lean Elab Command in
run_cmd do
  let permitted : Array Name := #[`propext, `Quot.sound, `Classical.choice]
  let targets : Array Name := #[
    `Tuza.packing_card_le,
    `Tuza.cover_number_le,
    `Tuza.exists_maximum_packing,
    `Tuza.exists_minimum_cover,
    `Tuza.satisfiesTuza_iff_certificates,
    `Tuza.packing_card_le_cover_card,
    `Tuza.packing_number_le_cover_number,
    `Tuza.cliqueCoverCost_even,
    `Tuza.cliqueCoverCost_odd,
    `Tuza.cliqueCoverCost_succ,
    `Tuza.monochromaticEdges_cover,
    `Tuza.common_endpoint_unique,
    `Tuza.lineGraph_edge_unique_owner,
    `Tuza.lineGraph_triangle_classification,
    `Tuza.triangle_edges_no_common_endpoint,
    `Tuza.completeGraph_fin_four_parameters,
    `Tuza.empty_total_parameters,
    `Tuza.single_edge_total_parameters,
    `Tuza.triangle_line_parameters,
    `Tuza.fourLeafStar_line_parameters,
    `Tuza.lineGraph_factor_sharp,
    `Tuza.two_original_vertices_force_bridge,
    `Tuza.bridge_is_triangle,
    `Tuza.incidence_is_triangle]
  let env ← getEnv
  for name in targets do
    match env.find? name with
    | some (.thmInfo _) =>
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless permitted.contains axiomName do
          logError m!"Forbidden axiom {axiomName} in {name}"
      logInfo m!"{name}: {axioms}"
    | _ => logError m!"Expected theorem is missing: {name}"
