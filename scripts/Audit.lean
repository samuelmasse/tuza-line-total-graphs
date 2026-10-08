module

import Solution
import all Tuza.Certificates
import all Tuza.CliqueArithmetic
import all Tuza.ColorCover
import all Tuza.LineTriangles
import all Tuza.SmallGraphs
import all Tuza.TotalTriangles
import all Tuza.CompleteGraphPacking
import all Tuza.Eulerian
import all Tuza.BalancedColoring
import all Tuza.LinePackets
import all Tuza.LineCovers
import all Tuza.LineTriangleFree
import all Tuza.LineColorBounds
import all Tuza.LineComponents
import all Tuza.TotalPackets
import all Tuza.TotalBound
import all Tuza.CubicTotal
import all Tuza.LineBound
public import Lean.Util.CollectAxioms

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
    `Tuza.incidence_is_triangle,
    `Tuza.cliqueCoverCost_le_twice_packing,
    `Tuza.cliqueCoverCost_add_two_le_twice_packing,
    `Tuza.exists_eulerian_closed_walk,
    `Tuza.exists_eulerian_edge_coloring,
    `Tuza.exists_odd_edge_coloring,
    `Tuza.exists_balanced_edge_coloring,
    `Tuza.exists_line_packet_packing,
    `Tuza.linePacking_lower_bound,
    `Tuza.line_monochromatic_card,
    `Tuza.line_triangleFree_cover_bound,
    `Tuza.line_eulerian_cover_bound,
    `Tuza.line_satisfiesTuza_of_components,
    `Tuza.total_packing_number_ge_edges_add_line,
    `Tuza.total_cover_upper_bound,
    `Tuza.total_exists_incident_edge_assignment,
    `Tuza.totalGraph_satisfiesTuza,
    `Tuza.lineGraph_satisfiesTuza,
    `Tuza.cubic_triangleFree_total_parameters]
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
