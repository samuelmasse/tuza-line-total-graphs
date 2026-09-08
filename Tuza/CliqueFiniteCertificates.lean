import Tuza.CliqueCertificateTools
import Tuza.CliqueArithmetic
import Mathlib.Tactic.IntervalCases

/-! # Kernel-checked witnesses for the finitely many induction bases

The listed triangles are proposed by a cyclic construction: pair vertices
in the first half and use their sum modulo its order in the second half;
then add the displayed extra triangles. Every witness is checked anew by
kernel reduction against triangle cardinalities and pairwise intersections.
The checker proves that these conditions give the stated exact packing size.
No maximum packing is computed.
-/

namespace Tuza

open Finset SimpleGraph

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def cliqueBase0 : List (Finset (Fin 0)) := []

private theorem cliqueBaseBound0 :
    cliqueCoverCost 0 + (if Even 0 ∧ 6 ≤ 0 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 0)) := by
  have hp := completePacking_list_length_le cliqueBase0 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 0) => t.card = 3) cliqueBase0) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 0 + (if Even 0 ∧ 6 ≤ 0 then 2 else 0) ≤
      2 * cliqueBase0.length := by decide +kernel
  omega

private def cliqueBase1 : List (Finset (Fin 1)) := []

private theorem cliqueBaseBound1 :
    cliqueCoverCost 1 + (if Even 1 ∧ 6 ≤ 1 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 1)) := by
  have hp := completePacking_list_length_le cliqueBase1 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 1) => t.card = 3) cliqueBase1) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 1 + (if Even 1 ∧ 6 ≤ 1 then 2 else 0) ≤
      2 * cliqueBase1.length := by decide +kernel
  omega

private def cliqueBase2 : List (Finset (Fin 2)) := []

private theorem cliqueBaseBound2 :
    cliqueCoverCost 2 + (if Even 2 ∧ 6 ≤ 2 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 2)) := by
  have hp := completePacking_list_length_le cliqueBase2 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 2) => t.card = 3) cliqueBase2) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 2 + (if Even 2 ∧ 6 ≤ 2 then 2 else 0) ≤
      2 * cliqueBase2.length := by decide +kernel
  omega

private def cliqueBase3 : List (Finset (Fin 3)) := [{2, 0, 1}]

private theorem cliqueBaseBound3 :
    cliqueCoverCost 3 + (if Even 3 ∧ 6 ≤ 3 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 3)) := by
  have hp := completePacking_list_length_le cliqueBase3 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 3) => t.card = 3) cliqueBase3) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 3 + (if Even 3 ∧ 6 ≤ 3 then 2 else 0) ≤
      2 * cliqueBase3.length := by decide +kernel
  omega

private def cliqueBase4 : List (Finset (Fin 4)) := [{0, 1, 3}]

private theorem cliqueBaseBound4 :
    cliqueCoverCost 4 + (if Even 4 ∧ 6 ≤ 4 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 4)) := by
  have hp := completePacking_list_length_le cliqueBase4 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 4) => t.card = 3) cliqueBase4) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 4 + (if Even 4 ∧ 6 ≤ 4 then 2 else 0) ≤
      2 * cliqueBase4.length := by decide +kernel
  omega

private def cliqueBase5 : List (Finset (Fin 5)) := [{0, 1, 3}, {4, 0, 2}]

private theorem cliqueBaseBound5 :
    cliqueCoverCost 5 + (if Even 5 ∧ 6 ≤ 5 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 5)) := by
  have hp := completePacking_list_length_le cliqueBase5 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 5) => t.card = 3) cliqueBase5) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 5 + (if Even 5 ∧ 6 ≤ 5 then 2 else 0) ≤
      2 * cliqueBase5.length := by decide +kernel
  omega

private def cliqueBase6 : List (Finset (Fin 6)) := [{0, 1, 4}, {0, 2, 5}, {1, 2, 3}, {3, 4, 5}]

private theorem cliqueBaseBound6 :
    cliqueCoverCost 6 + (if Even 6 ∧ 6 ≤ 6 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 6)) := by
  have hp := completePacking_list_length_le cliqueBase6 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 6) => t.card = 3) cliqueBase6) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 6 + (if Even 6 ∧ 6 ≤ 6 then 2 else 0) ≤
      2 * cliqueBase6.length := by decide +kernel
  omega

private def cliqueBase7 : List (Finset (Fin 7)) := [{0, 1, 4}, {0, 2, 5}, {1, 2, 3}, {6, 0, 3}, {6, 1, 5}, {6, 2, 4}]

private theorem cliqueBaseBound7 :
    cliqueCoverCost 7 + (if Even 7 ∧ 6 ≤ 7 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 7)) := by
  have hp := completePacking_list_length_le cliqueBase7 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 7) => t.card = 3) cliqueBase7) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 7 + (if Even 7 ∧ 6 ≤ 7 then 2 else 0) ≤
      2 * cliqueBase7.length := by decide +kernel
  omega

private def cliqueBase8 : List (Finset (Fin 8)) := [{0, 1, 5}, {0, 2, 6}, {0, 3, 7}, {1, 2, 7}, {1, 3, 4}, {2, 3, 5}, {4, 5, 6}]

private theorem cliqueBaseBound8 :
    cliqueCoverCost 8 + (if Even 8 ∧ 6 ≤ 8 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 8)) := by
  have hp := completePacking_list_length_le cliqueBase8 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 8) => t.card = 3) cliqueBase8) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 8 + (if Even 8 ∧ 6 ≤ 8 then 2 else 0) ≤
      2 * cliqueBase8.length := by decide +kernel
  omega

private def cliqueBase9 : List (Finset (Fin 9)) := [{0, 1, 5}, {0, 2, 6}, {0, 3, 7}, {1, 2, 7}, {1, 3, 4}, {2, 3, 5}, {8, 0, 4}, {8, 1, 6}]

private theorem cliqueBaseBound9 :
    cliqueCoverCost 9 + (if Even 9 ∧ 6 ≤ 9 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 9)) := by
  have hp := completePacking_list_length_le cliqueBase9 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 9) => t.card = 3) cliqueBase9) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 9 + (if Even 9 ∧ 6 ≤ 9 then 2 else 0) ≤
      2 * cliqueBase9.length := by decide +kernel
  omega

private def cliqueBase10 : List (Finset (Fin 10)) := [{0, 1, 6}, {0, 2, 7}, {0, 3, 8}, {0, 4, 9}, {1, 2, 8}, {1, 3, 9}, {1, 4, 5}, {2, 3, 5}, {2, 4, 6}, {3, 4, 7}, {5, 6, 7}]

private theorem cliqueBaseBound10 :
    cliqueCoverCost 10 + (if Even 10 ∧ 6 ≤ 10 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 10)) := by
  have hp := completePacking_list_length_le cliqueBase10 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 10) => t.card = 3) cliqueBase10) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 10 + (if Even 10 ∧ 6 ≤ 10 then 2 else 0) ≤
      2 * cliqueBase10.length := by decide +kernel
  omega

private def cliqueBase11 : List (Finset (Fin 11)) := [{0, 1, 6}, {0, 2, 7}, {0, 3, 8}, {0, 4, 9}, {1, 2, 8}, {1, 3, 9}, {1, 4, 5}, {2, 3, 5}, {2, 4, 6}, {3, 4, 7}, {10, 0, 5}, {10, 1, 7}, {10, 2, 9}, {10, 3, 6}, {10, 4, 8}]

private theorem cliqueBaseBound11 :
    cliqueCoverCost 11 + (if Even 11 ∧ 6 ≤ 11 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 11)) := by
  have hp := completePacking_list_length_le cliqueBase11 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 11) => t.card = 3) cliqueBase11) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 11 + (if Even 11 ∧ 6 ≤ 11 then 2 else 0) ≤
      2 * cliqueBase11.length := by decide +kernel
  omega

private def cliqueBase12 : List (Finset (Fin 12)) := [{0, 1, 7}, {0, 2, 8}, {0, 3, 9}, {0, 4, 10}, {0, 5, 11}, {1, 2, 9}, {1, 3, 10}, {1, 4, 11}, {1, 5, 6}, {2, 3, 11}, {2, 4, 6}, {2, 5, 7}, {3, 4, 7}, {3, 5, 8}, {4, 5, 9}, {6, 7, 8}]

private theorem cliqueBaseBound12 :
    cliqueCoverCost 12 + (if Even 12 ∧ 6 ≤ 12 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 12)) := by
  have hp := completePacking_list_length_le cliqueBase12 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 12) => t.card = 3) cliqueBase12) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 12 + (if Even 12 ∧ 6 ≤ 12 then 2 else 0) ≤
      2 * cliqueBase12.length := by decide +kernel
  omega

private def cliqueBase13 : List (Finset (Fin 13)) := [{0, 1, 7}, {0, 2, 8}, {0, 3, 9}, {0, 4, 10}, {0, 5, 11}, {1, 2, 9}, {1, 3, 10}, {1, 4, 11}, {1, 5, 6}, {2, 3, 11}, {2, 4, 6}, {2, 5, 7}, {3, 4, 7}, {3, 5, 8}, {4, 5, 9}, {12, 0, 6}, {12, 1, 8}, {12, 2, 10}]

private theorem cliqueBaseBound13 :
    cliqueCoverCost 13 + (if Even 13 ∧ 6 ≤ 13 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 13)) := by
  have hp := completePacking_list_length_le cliqueBase13 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 13) => t.card = 3) cliqueBase13) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 13 + (if Even 13 ∧ 6 ≤ 13 then 2 else 0) ≤
      2 * cliqueBase13.length := by decide +kernel
  omega

private def cliqueBase14 : List (Finset (Fin 14)) := [{0, 1, 8}, {0, 2, 9}, {0, 3, 10}, {0, 4, 11}, {0, 5, 12}, {0, 6, 13}, {1, 2, 10}, {1, 3, 11}, {1, 4, 12}, {1, 5, 13}, {1, 6, 7}, {2, 3, 12}, {2, 4, 13}, {2, 5, 7}, {2, 6, 8}, {3, 4, 7}, {3, 5, 8}, {3, 6, 9}, {4, 5, 9}, {4, 6, 10}, {5, 6, 11}, {7, 8, 9}]

private theorem cliqueBaseBound14 :
    cliqueCoverCost 14 + (if Even 14 ∧ 6 ≤ 14 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 14)) := by
  have hp := completePacking_list_length_le cliqueBase14 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 14) => t.card = 3) cliqueBase14) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 14 + (if Even 14 ∧ 6 ≤ 14 then 2 else 0) ≤
      2 * cliqueBase14.length := by decide +kernel
  omega

private def cliqueBase15 : List (Finset (Fin 15)) := [{0, 1, 8}, {0, 2, 9}, {0, 3, 10}, {0, 4, 11}, {0, 5, 12}, {0, 6, 13}, {1, 2, 10}, {1, 3, 11}, {1, 4, 12}, {1, 5, 13}, {1, 6, 7}, {2, 3, 12}, {2, 4, 13}, {2, 5, 7}, {2, 6, 8}, {3, 4, 7}, {3, 5, 8}, {3, 6, 9}, {4, 5, 9}, {4, 6, 10}, {5, 6, 11}, {14, 0, 7}, {14, 1, 9}, {14, 2, 11}, {14, 3, 13}, {14, 4, 8}, {14, 5, 10}, {14, 6, 12}]

private theorem cliqueBaseBound15 :
    cliqueCoverCost 15 + (if Even 15 ∧ 6 ≤ 15 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 15)) := by
  have hp := completePacking_list_length_le cliqueBase15 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 15) => t.card = 3) cliqueBase15) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 15 + (if Even 15 ∧ 6 ≤ 15 then 2 else 0) ≤
      2 * cliqueBase15.length := by decide +kernel
  omega

private def cliqueBase16 : List (Finset (Fin 16)) := [{0, 1, 9}, {0, 2, 10}, {0, 3, 11}, {0, 4, 12}, {0, 5, 13}, {0, 6, 14}, {0, 7, 15}, {1, 2, 11}, {1, 3, 12}, {1, 4, 13}, {1, 5, 14}, {1, 6, 15}, {1, 7, 8}, {2, 3, 13}, {2, 4, 14}, {2, 5, 15}, {2, 6, 8}, {2, 7, 9}, {3, 4, 15}, {3, 5, 8}, {3, 6, 9}, {3, 7, 10}, {4, 5, 9}, {4, 6, 10}, {4, 7, 11}, {5, 6, 11}, {5, 7, 12}, {6, 7, 13}, {8, 9, 10}]

private theorem cliqueBaseBound16 :
    cliqueCoverCost 16 + (if Even 16 ∧ 6 ≤ 16 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 16)) := by
  have hp := completePacking_list_length_le cliqueBase16 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 16) => t.card = 3) cliqueBase16) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 16 + (if Even 16 ∧ 6 ≤ 16 then 2 else 0) ≤
      2 * cliqueBase16.length := by decide +kernel
  omega

private def cliqueBase17 : List (Finset (Fin 17)) := [{0, 1, 9}, {0, 2, 10}, {0, 3, 11}, {0, 4, 12}, {0, 5, 13}, {0, 6, 14}, {0, 7, 15}, {1, 2, 11}, {1, 3, 12}, {1, 4, 13}, {1, 5, 14}, {1, 6, 15}, {1, 7, 8}, {2, 3, 13}, {2, 4, 14}, {2, 5, 15}, {2, 6, 8}, {2, 7, 9}, {3, 4, 15}, {3, 5, 8}, {3, 6, 9}, {3, 7, 10}, {4, 5, 9}, {4, 6, 10}, {4, 7, 11}, {5, 6, 11}, {5, 7, 12}, {6, 7, 13}, {16, 0, 8}, {16, 1, 10}, {16, 2, 12}, {16, 3, 14}]

private theorem cliqueBaseBound17 :
    cliqueCoverCost 17 + (if Even 17 ∧ 6 ≤ 17 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 17)) := by
  have hp := completePacking_list_length_le cliqueBase17 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 17) => t.card = 3) cliqueBase17) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 17 + (if Even 17 ∧ 6 ≤ 17 then 2 else 0) ≤
      2 * cliqueBase17.length := by decide +kernel
  omega

private def cliqueBase18 : List (Finset (Fin 18)) := [{0, 1, 10}, {0, 2, 11}, {0, 3, 12}, {0, 4, 13}, {0, 5, 14}, {0, 6, 15}, {0, 7, 16}, {0, 8, 17}, {1, 2, 12}, {1, 3, 13}, {1, 4, 14}, {1, 5, 15}, {1, 6, 16}, {1, 7, 17}, {1, 8, 9}, {2, 3, 14}, {2, 4, 15}, {2, 5, 16}, {2, 6, 17}, {2, 7, 9}, {2, 8, 10}, {3, 4, 16}, {3, 5, 17}, {3, 6, 9}, {3, 7, 10}, {3, 8, 11}, {4, 5, 9}, {4, 6, 10}, {4, 7, 11}, {4, 8, 12}, {5, 6, 11}, {5, 7, 12}, {5, 8, 13}, {6, 7, 13}, {6, 8, 14}, {7, 8, 15}, {9, 10, 11}]

private theorem cliqueBaseBound18 :
    cliqueCoverCost 18 + (if Even 18 ∧ 6 ≤ 18 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 18)) := by
  have hp := completePacking_list_length_le cliqueBase18 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 18) => t.card = 3) cliqueBase18) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 18 + (if Even 18 ∧ 6 ≤ 18 then 2 else 0) ≤
      2 * cliqueBase18.length := by decide +kernel
  omega

private def cliqueBase19 : List (Finset (Fin 19)) := [{0, 1, 10}, {0, 2, 11}, {0, 3, 12}, {0, 4, 13}, {0, 5, 14}, {0, 6, 15}, {0, 7, 16}, {0, 8, 17}, {1, 2, 12}, {1, 3, 13}, {1, 4, 14}, {1, 5, 15}, {1, 6, 16}, {1, 7, 17}, {1, 8, 9}, {2, 3, 14}, {2, 4, 15}, {2, 5, 16}, {2, 6, 17}, {2, 7, 9}, {2, 8, 10}, {3, 4, 16}, {3, 5, 17}, {3, 6, 9}, {3, 7, 10}, {3, 8, 11}, {4, 5, 9}, {4, 6, 10}, {4, 7, 11}, {4, 8, 12}, {5, 6, 11}, {5, 7, 12}, {5, 8, 13}, {6, 7, 13}, {6, 8, 14}, {7, 8, 15}, {18, 0, 9}, {18, 1, 11}, {18, 2, 13}, {18, 3, 15}, {18, 4, 17}, {18, 5, 10}, {18, 6, 12}, {18, 7, 14}, {18, 8, 16}]

private theorem cliqueBaseBound19 :
    cliqueCoverCost 19 + (if Even 19 ∧ 6 ≤ 19 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 19)) := by
  have hp := completePacking_list_length_le cliqueBase19 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 19) => t.card = 3) cliqueBase19) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 19 + (if Even 19 ∧ 6 ≤ 19 then 2 else 0) ≤
      2 * cliqueBase19.length := by decide +kernel
  omega

private def cliqueBase20 : List (Finset (Fin 20)) := [{0, 1, 11}, {0, 2, 12}, {0, 3, 13}, {0, 4, 14}, {0, 5, 15}, {0, 6, 16}, {0, 7, 17}, {0, 8, 18}, {0, 9, 19}, {1, 2, 13}, {1, 3, 14}, {1, 4, 15}, {1, 5, 16}, {1, 6, 17}, {1, 7, 18}, {1, 8, 19}, {1, 9, 10}, {2, 3, 15}, {2, 4, 16}, {2, 5, 17}, {2, 6, 18}, {2, 7, 19}, {2, 8, 10}, {2, 9, 11}, {3, 4, 17}, {3, 5, 18}, {3, 6, 19}, {3, 7, 10}, {3, 8, 11}, {3, 9, 12}, {4, 5, 19}, {4, 6, 10}, {4, 7, 11}, {4, 8, 12}, {4, 9, 13}, {5, 6, 11}, {5, 7, 12}, {5, 8, 13}, {5, 9, 14}, {6, 7, 13}, {6, 8, 14}, {6, 9, 15}, {7, 8, 15}, {7, 9, 16}, {8, 9, 17}, {10, 11, 12}]

private theorem cliqueBaseBound20 :
    cliqueCoverCost 20 + (if Even 20 ∧ 6 ≤ 20 then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin 20)) := by
  have hp := completePacking_list_length_le cliqueBase20 (by exact @of_decide_eq_true _ (List.decidableBAll (fun t : Finset (Fin 20) => t.card = 3) cliqueBase20) (by decide +kernel)) (by decide +kernel)
  have hc : cliqueCoverCost 20 + (if Even 20 ∧ 6 ≤ 20 then 2 else 0) ≤
      2 * cliqueBase20.length := by decide +kernel
  omega

theorem clique_packing_small (n : ℕ) (hn : n < 21) :
    cliqueCoverCost n + (if Even n ∧ 6 ≤ n then 2 else 0) ≤
      2 * trianglePackingNumber (completeGraph (Fin n)) := by
  interval_cases n
  · exact cliqueBaseBound0
  · exact cliqueBaseBound1
  · exact cliqueBaseBound2
  · exact cliqueBaseBound3
  · exact cliqueBaseBound4
  · exact cliqueBaseBound5
  · exact cliqueBaseBound6
  · exact cliqueBaseBound7
  · exact cliqueBaseBound8
  · exact cliqueBaseBound9
  · exact cliqueBaseBound10
  · exact cliqueBaseBound11
  · exact cliqueBaseBound12
  · exact cliqueBaseBound13
  · exact cliqueBaseBound14
  · exact cliqueBaseBound15
  · exact cliqueBaseBound16
  · exact cliqueBaseBound17
  · exact cliqueBaseBound18
  · exact cliqueBaseBound19
  · exact cliqueBaseBound20

end Tuza
