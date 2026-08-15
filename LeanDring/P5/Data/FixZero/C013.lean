/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C001

/-!
# Species-table cells, off-support emptiness certificates, chunk 12

For each `(rK, rH)` in this chunk the `H`-fixed part of `G/K` is EMPTY (while
`|H| <= |K|`, so the order bound does not apply): one batched kernel `decide` per
class scans the certified full transversal `R<rK>`, and the per-pair theorems
reflect it through `repsFixedCard` into the fixed-point count.  Feeds
`species_zero_of_fixCard_zero` (`LeanDring/P5/Certificate/Support/Stage5Core.lean`).
Auto-emitted by `python/p5_fixzero_emit.py`.
-/

namespace LeanDring.P5Presentation

open MulAction Finset LeanDring.DRing LeanDring.MonGSet

-- machine-emitted certificate: file-level heartbeat raise is intentional
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.style.longLine false

theorem fixz1_13 : ([2, 3, 4, 5, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK13) (retConj 1 (R13 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_13_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨2, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 2 (by decide)))

theorem fz1_13_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨3, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 3 (by decide)))

theorem fz1_13_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨4, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 4 (by decide)))

theorem fz1_13_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨5, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 5 (by decide)))

theorem fz1_13_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨11, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 11 (by decide)))

theorem fz1_13_12 : Fintype.card
    (fixedPoints (reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨12, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 12 (by decide)))

theorem fz1_13_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨14, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 14 (by decide)))

theorem fz1_13_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨15, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 15 (by decide)))

theorem fz1_13_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨16, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 16 (by decide)))

theorem fz1_13_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨17, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 17 (by decide)))

theorem fz1_13_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨18, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 18 (by decide)))

theorem fz1_13_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨19, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 19 (by decide)))

theorem fz1_13_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨20, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 20 (by decide)))

theorem fz1_13_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨21, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 21 (by decide)))

theorem fz1_13_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨22, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 22 (by decide)))

theorem fz1_13_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨23, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 23 (by decide)))

theorem fz1_13_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨24, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 24 (by decide)))

theorem fz1_13_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨25, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 25 (by decide)))

theorem fz1_13_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨26, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 26 (by decide)))

theorem fz1_13_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨27, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 27 (by decide)))

theorem fz1_13_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨28, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 28 (by decide)))

theorem fz1_13_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨29, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 29 (by decide)))

theorem fz1_13_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨30, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 30 (by decide)))

theorem fz1_13_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨31, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 31 (by decide)))

theorem fz1_13_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨32, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 32 (by decide)))

theorem fz1_13_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨33, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 33 (by decide)))

theorem fz1_13_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨34, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 34 (by decide)))

theorem fz1_13_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨35, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 35 (by decide)))

theorem fz1_13_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨36, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 36 (by decide)))

theorem fz1_13_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨37, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 37 (by decide)))

theorem fz1_13_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨38, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 38 (by decide)))

theorem fz1_13_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨39, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 39 (by decide)))

theorem fz1_13_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨40, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 40 (by decide)))

theorem fz1_13_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨41, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 41 (by decide)))

theorem fz1_13_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨42, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 42 (by decide)))

theorem fz1_13_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨43, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 43 (by decide)))

theorem fz1_13_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨44, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 44 (by decide)))

theorem fz1_13_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨45, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 45 (by decide)))

theorem fz1_13_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨46, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 46 (by decide)))

theorem fz1_13_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨47, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 47 (by decide)))

theorem fz1_13_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨48, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 48 (by decide)))

theorem fz1_13_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨49, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 49 (by decide)))

theorem fz1_13_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨50, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 50 (by decide)))

theorem fz1_13_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨51, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 51 (by decide)))

theorem fz1_13_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨52, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 52 (by decide)))

theorem fz1_13_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨53, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 53 (by decide)))

theorem fz1_13_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK13)) = 0 :=
  repsFixedCard rK13 ⟨54, by decide⟩ R13 hpxR13 hcardq13
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_13) 54 (by decide)))

theorem fixz2_13 : ([2, 3, 4, 5, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK13) (retConj 2 (Q2.R13_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_13_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨2, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 2 (by decide)))

theorem fz2_13_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨3, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 3 (by decide)))

theorem fz2_13_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨4, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 4 (by decide)))

theorem fz2_13_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨5, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 5 (by decide)))

theorem fz2_13_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨11, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 11 (by decide)))

theorem fz2_13_12 : Fintype.card
    (fixedPoints (Q2.reps (⟨12, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨12, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 12 (by decide)))

theorem fz2_13_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨14, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 14 (by decide)))

theorem fz2_13_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨15, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 15 (by decide)))

theorem fz2_13_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨16, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 16 (by decide)))

theorem fz2_13_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨17, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 17 (by decide)))

theorem fz2_13_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨18, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 18 (by decide)))

theorem fz2_13_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨19, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 19 (by decide)))

theorem fz2_13_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨20, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 20 (by decide)))

theorem fz2_13_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨21, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 21 (by decide)))

theorem fz2_13_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨22, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 22 (by decide)))

theorem fz2_13_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨23, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 23 (by decide)))

theorem fz2_13_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨24, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 24 (by decide)))

theorem fz2_13_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨25, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 25 (by decide)))

theorem fz2_13_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨26, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 26 (by decide)))

theorem fz2_13_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨27, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 27 (by decide)))

theorem fz2_13_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨28, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 28 (by decide)))

theorem fz2_13_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨29, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 29 (by decide)))

theorem fz2_13_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨30, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 30 (by decide)))

theorem fz2_13_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨31, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 31 (by decide)))

theorem fz2_13_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨32, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 32 (by decide)))

theorem fz2_13_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨33, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 33 (by decide)))

theorem fz2_13_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨34, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 34 (by decide)))

theorem fz2_13_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨35, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 35 (by decide)))

theorem fz2_13_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨36, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 36 (by decide)))

theorem fz2_13_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨37, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 37 (by decide)))

theorem fz2_13_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨38, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 38 (by decide)))

theorem fz2_13_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨39, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 39 (by decide)))

theorem fz2_13_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨40, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 40 (by decide)))

theorem fz2_13_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨41, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 41 (by decide)))

theorem fz2_13_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨42, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 42 (by decide)))

theorem fz2_13_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨43, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 43 (by decide)))

theorem fz2_13_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨44, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 44 (by decide)))

theorem fz2_13_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨45, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 45 (by decide)))

theorem fz2_13_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨46, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 46 (by decide)))

theorem fz2_13_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨47, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 47 (by decide)))

theorem fz2_13_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨48, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 48 (by decide)))

theorem fz2_13_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨49, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 49 (by decide)))

theorem fz2_13_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨50, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 50 (by decide)))

theorem fz2_13_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨51, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 51 (by decide)))

theorem fz2_13_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨52, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 52 (by decide)))

theorem fz2_13_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨53, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 53 (by decide)))

theorem fz2_13_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK13)) = 0 :=
  Q2.repsFixedCard2 rK13 ⟨54, by decide⟩ Q2.R13_2 Q2.hpxR13_2 Q2.hcardq13_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_13) 54 (by decide)))

end LeanDring.P5Presentation
