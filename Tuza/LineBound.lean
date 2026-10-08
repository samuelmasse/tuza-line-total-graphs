module

public import Tuza.LineConnected
public import Tuza.LineComponents
public import Tuza.LineTriangleAugment
public import Tuza.CompleteGraphPacking

@[expose] public section

/-! # Tuza's inequality for every finite simple line graph -/

namespace Tuza

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem connected_lineGraph_satisfiesTuza (hconn : G.Connected) :
    SatisfiesTuza G.lineGraph :=
  connected_line_satisfiesTuza_of_local_bounds G hconn
    cliqueCoverCost_le_twice_packing cliqueCoverCost_add_two_le_twice_packing
    (line_packing_augment_root_triangle G)

/-- No connectedness or triangle-freeness assumption is imposed on the root. -/
theorem lineGraph_satisfiesTuza : SatisfiesTuza G.lineGraph := by
  classical
  apply line_satisfiesTuza_of_components G
  intro C
  exact connected_lineGraph_satisfiesTuza C.toSimpleGraph C.connected_toSimpleGraph

end Tuza
