/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryA.C013

/-!
# Species-table cells, off-support emptiness certificates, chunk 24

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

theorem fixz1_25 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK25) (retConj 1 (R25 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_25_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨1, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 1 (by decide)))

theorem fz1_25_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨2, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 2 (by decide)))

theorem fz1_25_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨3, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 3 (by decide)))

theorem fz1_25_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨4, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 4 (by decide)))

theorem fz1_25_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨5, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 5 (by decide)))

theorem fz1_25_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨6, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 6 (by decide)))

theorem fz1_25_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨8, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 8 (by decide)))

theorem fz1_25_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨9, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 9 (by decide)))

theorem fz1_25_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨10, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 10 (by decide)))

theorem fz1_25_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨11, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 11 (by decide)))

theorem fz1_25_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨13, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 13 (by decide)))

theorem fz1_25_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨14, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 14 (by decide)))

theorem fz1_25_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨15, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 15 (by decide)))

theorem fz1_25_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨16, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 16 (by decide)))

theorem fz1_25_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨17, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 17 (by decide)))

theorem fz1_25_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨18, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 18 (by decide)))

theorem fz1_25_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨19, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 19 (by decide)))

theorem fz1_25_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨20, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 20 (by decide)))

theorem fz1_25_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨21, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 21 (by decide)))

theorem fz1_25_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨22, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 22 (by decide)))

theorem fz1_25_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨23, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 23 (by decide)))

theorem fz1_25_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨24, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 24 (by decide)))

theorem fz1_25_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨26, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 26 (by decide)))

theorem fz1_25_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨27, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 27 (by decide)))

theorem fz1_25_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨28, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 28 (by decide)))

theorem fz1_25_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨29, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 29 (by decide)))

theorem fz1_25_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨30, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 30 (by decide)))

theorem fz1_25_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨31, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 31 (by decide)))

theorem fz1_25_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨32, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 32 (by decide)))

theorem fz1_25_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨33, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 33 (by decide)))

theorem fz1_25_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨34, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 34 (by decide)))

theorem fz1_25_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨35, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 35 (by decide)))

theorem fz1_25_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨36, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 36 (by decide)))

theorem fz1_25_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨37, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 37 (by decide)))

theorem fz1_25_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨38, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 38 (by decide)))

theorem fz1_25_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨39, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 39 (by decide)))

theorem fz1_25_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨40, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 40 (by decide)))

theorem fz1_25_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨41, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 41 (by decide)))

theorem fz1_25_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨42, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 42 (by decide)))

theorem fz1_25_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨43, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 43 (by decide)))

theorem fz1_25_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨44, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 44 (by decide)))

theorem fz1_25_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨45, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 45 (by decide)))

theorem fz1_25_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨46, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 46 (by decide)))

theorem fz1_25_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨47, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 47 (by decide)))

theorem fz1_25_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨48, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 48 (by decide)))

theorem fz1_25_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨49, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 49 (by decide)))

theorem fz1_25_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨50, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 50 (by decide)))

theorem fz1_25_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨51, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 51 (by decide)))

theorem fz1_25_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨52, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 52 (by decide)))

theorem fz1_25_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨53, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 53 (by decide)))

theorem fz1_25_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK25)) = 0 :=
  repsFixedCard rK25 ⟨54, by decide⟩ R25 hpxR25 hcardq25
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_25) 54 (by decide)))

theorem fixz2_25 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 125 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK25) (retConj 2 (Q2.R25_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_25_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨1, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 1 (by decide)))

theorem fz2_25_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨2, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 2 (by decide)))

theorem fz2_25_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨3, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 3 (by decide)))

theorem fz2_25_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨4, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 4 (by decide)))

theorem fz2_25_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨5, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 5 (by decide)))

theorem fz2_25_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨6, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 6 (by decide)))

theorem fz2_25_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨8, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 8 (by decide)))

theorem fz2_25_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨9, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 9 (by decide)))

theorem fz2_25_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨10, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 10 (by decide)))

theorem fz2_25_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨11, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 11 (by decide)))

theorem fz2_25_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨13, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 13 (by decide)))

theorem fz2_25_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨14, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 14 (by decide)))

theorem fz2_25_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨15, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 15 (by decide)))

theorem fz2_25_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨16, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 16 (by decide)))

theorem fz2_25_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨17, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 17 (by decide)))

theorem fz2_25_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨18, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 18 (by decide)))

theorem fz2_25_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨19, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 19 (by decide)))

theorem fz2_25_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨20, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 20 (by decide)))

theorem fz2_25_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨21, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 21 (by decide)))

theorem fz2_25_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨22, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 22 (by decide)))

theorem fz2_25_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨23, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 23 (by decide)))

theorem fz2_25_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨24, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 24 (by decide)))

theorem fz2_25_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨26, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 26 (by decide)))

theorem fz2_25_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨27, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 27 (by decide)))

theorem fz2_25_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨28, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 28 (by decide)))

theorem fz2_25_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨29, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 29 (by decide)))

theorem fz2_25_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨30, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 30 (by decide)))

theorem fz2_25_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨31, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 31 (by decide)))

theorem fz2_25_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨32, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 32 (by decide)))

theorem fz2_25_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨33, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 33 (by decide)))

theorem fz2_25_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨34, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 34 (by decide)))

theorem fz2_25_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨35, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 35 (by decide)))

theorem fz2_25_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨36, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 36 (by decide)))

theorem fz2_25_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨37, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 37 (by decide)))

theorem fz2_25_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨38, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 38 (by decide)))

theorem fz2_25_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨39, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 39 (by decide)))

theorem fz2_25_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨40, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 40 (by decide)))

theorem fz2_25_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨41, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 41 (by decide)))

theorem fz2_25_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨42, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 42 (by decide)))

theorem fz2_25_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨43, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 43 (by decide)))

theorem fz2_25_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨44, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 44 (by decide)))

theorem fz2_25_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨45, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 45 (by decide)))

theorem fz2_25_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨46, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 46 (by decide)))

theorem fz2_25_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨47, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 47 (by decide)))

theorem fz2_25_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨48, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 48 (by decide)))

theorem fz2_25_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨49, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 49 (by decide)))

theorem fz2_25_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨50, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 50 (by decide)))

theorem fz2_25_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨51, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 51 (by decide)))

theorem fz2_25_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨52, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 52 (by decide)))

theorem fz2_25_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨53, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 53 (by decide)))

theorem fz2_25_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK25)) = 0 :=
  Q2.repsFixedCard2 rK25 ⟨54, by decide⟩ Q2.R25_2 Q2.hpxR25_2 Q2.hcardq25_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_25) 54 (by decide)))

end LeanDring.P5Presentation
