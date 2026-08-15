/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C019

/-!
# Species-table cells, off-support emptiness certificates, chunk 67

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

theorem fixz1_81 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK81) (retConj 1 (R81 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_81_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨1, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 1 (by decide)))

theorem fz1_81_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨3, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 3 (by decide)))

theorem fz1_81_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨4, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 4 (by decide)))

theorem fz1_81_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨5, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 5 (by decide)))

theorem fz1_81_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨6, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 6 (by decide)))

theorem fz1_81_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨7, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 7 (by decide)))

theorem fz1_81_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨8, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 8 (by decide)))

theorem fz1_81_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨9, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 9 (by decide)))

theorem fz1_81_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨11, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 11 (by decide)))

theorem fz1_81_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨13, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 13 (by decide)))

theorem fz1_81_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨14, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 14 (by decide)))

theorem fz1_81_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨15, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 15 (by decide)))

theorem fz1_81_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨16, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 16 (by decide)))

theorem fz1_81_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨17, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 17 (by decide)))

theorem fz1_81_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨18, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 18 (by decide)))

theorem fz1_81_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨19, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 19 (by decide)))

theorem fz1_81_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨21, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 21 (by decide)))

theorem fz1_81_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨22, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 22 (by decide)))

theorem fz1_81_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨23, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 23 (by decide)))

theorem fz1_81_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨24, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 24 (by decide)))

theorem fz1_81_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨25, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 25 (by decide)))

theorem fz1_81_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨26, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 26 (by decide)))

theorem fz1_81_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨27, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 27 (by decide)))

theorem fz1_81_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨28, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 28 (by decide)))

theorem fz1_81_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨29, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 29 (by decide)))

theorem fz1_81_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨30, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 30 (by decide)))

theorem fz1_81_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨31, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 31 (by decide)))

theorem fz1_81_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨32, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 32 (by decide)))

theorem fz1_81_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨33, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 33 (by decide)))

theorem fz1_81_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨34, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 34 (by decide)))

theorem fz1_81_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨35, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 35 (by decide)))

theorem fz1_81_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨36, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 36 (by decide)))

theorem fz1_81_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨37, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 37 (by decide)))

theorem fz1_81_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨38, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 38 (by decide)))

theorem fz1_81_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨39, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 39 (by decide)))

theorem fz1_81_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨40, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 40 (by decide)))

theorem fz1_81_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨41, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 41 (by decide)))

theorem fz1_81_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨42, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 42 (by decide)))

theorem fz1_81_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨43, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 43 (by decide)))

theorem fz1_81_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨44, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 44 (by decide)))

theorem fz1_81_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨45, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 45 (by decide)))

theorem fz1_81_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨46, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 46 (by decide)))

theorem fz1_81_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨47, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 47 (by decide)))

theorem fz1_81_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨48, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 48 (by decide)))

theorem fz1_81_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨49, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 49 (by decide)))

theorem fz1_81_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨50, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 50 (by decide)))

theorem fz1_81_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨51, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 51 (by decide)))

theorem fz1_81_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨52, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 52 (by decide)))

theorem fz1_81_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨54, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 54 (by decide)))

theorem fz1_81_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨55, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 55 (by decide)))

theorem fz1_81_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨56, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 56 (by decide)))

theorem fz1_81_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨57, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 57 (by decide)))

theorem fz1_81_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨58, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 58 (by decide)))

theorem fz1_81_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨59, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 59 (by decide)))

theorem fz1_81_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨60, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 60 (by decide)))

theorem fz1_81_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨61, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 61 (by decide)))

theorem fz1_81_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨62, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 62 (by decide)))

theorem fz1_81_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨63, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 63 (by decide)))

theorem fz1_81_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨64, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 64 (by decide)))

theorem fz1_81_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨65, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 65 (by decide)))

theorem fz1_81_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨66, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 66 (by decide)))

theorem fz1_81_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨67, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 67 (by decide)))

theorem fz1_81_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨68, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 68 (by decide)))

theorem fz1_81_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨69, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 69 (by decide)))

theorem fz1_81_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨70, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 70 (by decide)))

theorem fz1_81_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨71, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 71 (by decide)))

theorem fz1_81_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨72, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 72 (by decide)))

theorem fz1_81_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨73, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 73 (by decide)))

theorem fz1_81_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨74, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 74 (by decide)))

theorem fz1_81_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨75, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 75 (by decide)))

theorem fz1_81_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨76, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 76 (by decide)))

theorem fz1_81_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨77, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 77 (by decide)))

theorem fz1_81_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨78, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 78 (by decide)))

theorem fz1_81_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨79, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 79 (by decide)))

theorem fz1_81_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨80, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 80 (by decide)))

theorem fz1_81_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨82, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 82 (by decide)))

theorem fz1_81_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨83, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 83 (by decide)))

theorem fz1_81_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨84, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 84 (by decide)))

theorem fz1_81_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨85, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 85 (by decide)))

theorem fz1_81_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨86, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 86 (by decide)))

theorem fz1_81_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨87, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 87 (by decide)))

theorem fz1_81_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨88, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 88 (by decide)))

theorem fz1_81_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨89, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 89 (by decide)))

theorem fz1_81_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨90, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 90 (by decide)))

theorem fz1_81_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨91, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 91 (by decide)))

theorem fz1_81_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨92, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 92 (by decide)))

theorem fz1_81_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨93, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 93 (by decide)))

theorem fz1_81_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨94, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 94 (by decide)))

theorem fz1_81_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨95, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 95 (by decide)))

theorem fz1_81_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨96, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 96 (by decide)))

theorem fz1_81_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨97, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 97 (by decide)))

theorem fz1_81_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨98, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 98 (by decide)))

theorem fz1_81_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨99, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 99 (by decide)))

theorem fz1_81_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨100, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 100 (by decide)))

theorem fz1_81_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨101, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 101 (by decide)))

theorem fz1_81_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨102, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 102 (by decide)))

theorem fz1_81_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨103, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 103 (by decide)))

theorem fz1_81_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨104, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 104 (by decide)))

theorem fz1_81_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨105, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 105 (by decide)))

theorem fz1_81_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨106, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 106 (by decide)))

theorem fz1_81_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨107, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 107 (by decide)))

theorem fz1_81_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨108, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 108 (by decide)))

theorem fz1_81_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨109, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 109 (by decide)))

theorem fz1_81_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨110, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 110 (by decide)))

theorem fz1_81_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨111, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 111 (by decide)))

theorem fz1_81_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨112, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 112 (by decide)))

theorem fz1_81_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨113, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 113 (by decide)))

theorem fz1_81_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨114, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 114 (by decide)))

theorem fz1_81_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK81)) = 0 :=
  repsFixedCard rK81 ⟨115, by decide⟩ R81 hpxR81 hcardq81
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_81) 115 (by decide)))

theorem fixz2_81 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK81) (retConj 2 (Q2.R81_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_81_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨1, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 1 (by decide)))

theorem fz2_81_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨3, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 3 (by decide)))

theorem fz2_81_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨4, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 4 (by decide)))

theorem fz2_81_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨5, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 5 (by decide)))

theorem fz2_81_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨6, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 6 (by decide)))

theorem fz2_81_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨7, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 7 (by decide)))

theorem fz2_81_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨8, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 8 (by decide)))

theorem fz2_81_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨9, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 9 (by decide)))

theorem fz2_81_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨11, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 11 (by decide)))

theorem fz2_81_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨13, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 13 (by decide)))

theorem fz2_81_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨14, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 14 (by decide)))

theorem fz2_81_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨15, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 15 (by decide)))

theorem fz2_81_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨16, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 16 (by decide)))

theorem fz2_81_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨17, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 17 (by decide)))

theorem fz2_81_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨18, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 18 (by decide)))

theorem fz2_81_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨19, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 19 (by decide)))

theorem fz2_81_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨21, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 21 (by decide)))

theorem fz2_81_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨22, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 22 (by decide)))

theorem fz2_81_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨23, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 23 (by decide)))

theorem fz2_81_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨24, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 24 (by decide)))

theorem fz2_81_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨25, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 25 (by decide)))

theorem fz2_81_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨26, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 26 (by decide)))

theorem fz2_81_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨27, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 27 (by decide)))

theorem fz2_81_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨28, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 28 (by decide)))

theorem fz2_81_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨29, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 29 (by decide)))

theorem fz2_81_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨30, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 30 (by decide)))

theorem fz2_81_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨31, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 31 (by decide)))

theorem fz2_81_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨32, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 32 (by decide)))

theorem fz2_81_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨33, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 33 (by decide)))

theorem fz2_81_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨34, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 34 (by decide)))

theorem fz2_81_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨35, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 35 (by decide)))

theorem fz2_81_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨36, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 36 (by decide)))

theorem fz2_81_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨37, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 37 (by decide)))

theorem fz2_81_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨38, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 38 (by decide)))

theorem fz2_81_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨39, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 39 (by decide)))

theorem fz2_81_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨40, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 40 (by decide)))

theorem fz2_81_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨41, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 41 (by decide)))

theorem fz2_81_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨42, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 42 (by decide)))

theorem fz2_81_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨43, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 43 (by decide)))

theorem fz2_81_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨44, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 44 (by decide)))

theorem fz2_81_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨45, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 45 (by decide)))

theorem fz2_81_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨46, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 46 (by decide)))

theorem fz2_81_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨47, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 47 (by decide)))

theorem fz2_81_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨48, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 48 (by decide)))

theorem fz2_81_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨49, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 49 (by decide)))

theorem fz2_81_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨50, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 50 (by decide)))

theorem fz2_81_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨51, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 51 (by decide)))

theorem fz2_81_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨52, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 52 (by decide)))

theorem fz2_81_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨54, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 54 (by decide)))

theorem fz2_81_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨55, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 55 (by decide)))

theorem fz2_81_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨56, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 56 (by decide)))

theorem fz2_81_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨57, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 57 (by decide)))

theorem fz2_81_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨58, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 58 (by decide)))

theorem fz2_81_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨59, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 59 (by decide)))

theorem fz2_81_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨60, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 60 (by decide)))

theorem fz2_81_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨61, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 61 (by decide)))

theorem fz2_81_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨62, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 62 (by decide)))

theorem fz2_81_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨63, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 63 (by decide)))

theorem fz2_81_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨64, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 64 (by decide)))

theorem fz2_81_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨65, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 65 (by decide)))

theorem fz2_81_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨66, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 66 (by decide)))

theorem fz2_81_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨67, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 67 (by decide)))

theorem fz2_81_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨68, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 68 (by decide)))

theorem fz2_81_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨69, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 69 (by decide)))

theorem fz2_81_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨70, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 70 (by decide)))

theorem fz2_81_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨71, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 71 (by decide)))

theorem fz2_81_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨72, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 72 (by decide)))

theorem fz2_81_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨73, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 73 (by decide)))

theorem fz2_81_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨74, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 74 (by decide)))

theorem fz2_81_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨75, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 75 (by decide)))

theorem fz2_81_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨76, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 76 (by decide)))

theorem fz2_81_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨77, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 77 (by decide)))

theorem fz2_81_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨78, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 78 (by decide)))

theorem fz2_81_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨79, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 79 (by decide)))

theorem fz2_81_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨80, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 80 (by decide)))

theorem fz2_81_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨82, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 82 (by decide)))

theorem fz2_81_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨83, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 83 (by decide)))

theorem fz2_81_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨84, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 84 (by decide)))

theorem fz2_81_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨85, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 85 (by decide)))

theorem fz2_81_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨86, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 86 (by decide)))

theorem fz2_81_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨87, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 87 (by decide)))

theorem fz2_81_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨88, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 88 (by decide)))

theorem fz2_81_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨89, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 89 (by decide)))

theorem fz2_81_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨90, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 90 (by decide)))

theorem fz2_81_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨91, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 91 (by decide)))

theorem fz2_81_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨92, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 92 (by decide)))

theorem fz2_81_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨93, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 93 (by decide)))

theorem fz2_81_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨94, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 94 (by decide)))

theorem fz2_81_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨95, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 95 (by decide)))

theorem fz2_81_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨96, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 96 (by decide)))

theorem fz2_81_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨97, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 97 (by decide)))

theorem fz2_81_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨98, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 98 (by decide)))

theorem fz2_81_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨99, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 99 (by decide)))

theorem fz2_81_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨100, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 100 (by decide)))

theorem fz2_81_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨101, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 101 (by decide)))

theorem fz2_81_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨102, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 102 (by decide)))

theorem fz2_81_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨103, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 103 (by decide)))

theorem fz2_81_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨104, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 104 (by decide)))

theorem fz2_81_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨105, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 105 (by decide)))

theorem fz2_81_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨106, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 106 (by decide)))

theorem fz2_81_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨107, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 107 (by decide)))

theorem fz2_81_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨108, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 108 (by decide)))

theorem fz2_81_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨109, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 109 (by decide)))

theorem fz2_81_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨110, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 110 (by decide)))

theorem fz2_81_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨111, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 111 (by decide)))

theorem fz2_81_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨112, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 112 (by decide)))

theorem fz2_81_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨113, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 113 (by decide)))

theorem fz2_81_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨114, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 114 (by decide)))

theorem fz2_81_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK81)) = 0 :=
  Q2.repsFixedCard2 rK81 ⟨115, by decide⟩ Q2.R81_2 Q2.hpxR81_2 Q2.hcardq81_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_81) 115 (by decide)))

theorem fixz1_82 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK82) (retConj 1 (R82 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_82_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨1, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 1 (by decide)))

theorem fz1_82_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨2, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 2 (by decide)))

theorem fz1_82_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨4, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 4 (by decide)))

theorem fz1_82_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨5, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 5 (by decide)))

theorem fz1_82_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨6, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 6 (by decide)))

theorem fz1_82_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨7, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 7 (by decide)))

theorem fz1_82_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨8, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 8 (by decide)))

theorem fz1_82_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨9, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 9 (by decide)))

theorem fz1_82_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨11, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 11 (by decide)))

theorem fz1_82_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨13, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 13 (by decide)))

theorem fz1_82_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨14, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 14 (by decide)))

theorem fz1_82_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨15, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 15 (by decide)))

theorem fz1_82_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨16, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 16 (by decide)))

theorem fz1_82_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨17, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 17 (by decide)))

theorem fz1_82_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨18, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 18 (by decide)))

theorem fz1_82_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨19, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 19 (by decide)))

theorem fz1_82_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨20, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 20 (by decide)))

theorem fz1_82_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨22, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 22 (by decide)))

theorem fz1_82_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨23, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 23 (by decide)))

theorem fz1_82_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨24, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 24 (by decide)))

theorem fz1_82_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨25, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 25 (by decide)))

theorem fz1_82_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨26, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 26 (by decide)))

theorem fz1_82_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨27, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 27 (by decide)))

theorem fz1_82_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨28, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 28 (by decide)))

theorem fz1_82_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨29, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 29 (by decide)))

theorem fz1_82_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨30, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 30 (by decide)))

theorem fz1_82_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨31, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 31 (by decide)))

theorem fz1_82_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨32, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 32 (by decide)))

theorem fz1_82_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨33, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 33 (by decide)))

theorem fz1_82_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨34, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 34 (by decide)))

theorem fz1_82_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨35, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 35 (by decide)))

theorem fz1_82_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨36, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 36 (by decide)))

theorem fz1_82_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨37, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 37 (by decide)))

theorem fz1_82_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨38, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 38 (by decide)))

theorem fz1_82_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨39, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 39 (by decide)))

theorem fz1_82_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨40, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 40 (by decide)))

theorem fz1_82_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨41, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 41 (by decide)))

theorem fz1_82_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨42, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 42 (by decide)))

theorem fz1_82_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨43, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 43 (by decide)))

theorem fz1_82_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨44, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 44 (by decide)))

theorem fz1_82_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨45, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 45 (by decide)))

theorem fz1_82_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨46, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 46 (by decide)))

theorem fz1_82_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨47, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 47 (by decide)))

theorem fz1_82_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨48, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 48 (by decide)))

theorem fz1_82_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨49, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 49 (by decide)))

theorem fz1_82_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨50, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 50 (by decide)))

theorem fz1_82_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨51, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 51 (by decide)))

theorem fz1_82_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨52, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 52 (by decide)))

theorem fz1_82_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨54, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 54 (by decide)))

theorem fz1_82_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨55, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 55 (by decide)))

theorem fz1_82_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨56, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 56 (by decide)))

theorem fz1_82_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨57, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 57 (by decide)))

theorem fz1_82_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨58, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 58 (by decide)))

theorem fz1_82_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨59, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 59 (by decide)))

theorem fz1_82_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨60, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 60 (by decide)))

theorem fz1_82_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨61, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 61 (by decide)))

theorem fz1_82_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨62, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 62 (by decide)))

theorem fz1_82_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨63, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 63 (by decide)))

theorem fz1_82_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨64, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 64 (by decide)))

theorem fz1_82_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨65, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 65 (by decide)))

theorem fz1_82_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨66, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 66 (by decide)))

theorem fz1_82_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨67, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 67 (by decide)))

theorem fz1_82_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨68, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 68 (by decide)))

theorem fz1_82_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨69, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 69 (by decide)))

theorem fz1_82_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨70, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 70 (by decide)))

theorem fz1_82_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨71, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 71 (by decide)))

theorem fz1_82_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨72, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 72 (by decide)))

theorem fz1_82_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨73, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 73 (by decide)))

theorem fz1_82_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨74, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 74 (by decide)))

theorem fz1_82_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨75, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 75 (by decide)))

theorem fz1_82_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨76, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 76 (by decide)))

theorem fz1_82_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨77, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 77 (by decide)))

theorem fz1_82_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨78, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 78 (by decide)))

theorem fz1_82_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨79, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 79 (by decide)))

theorem fz1_82_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨80, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 80 (by decide)))

theorem fz1_82_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨81, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 81 (by decide)))

theorem fz1_82_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨83, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 83 (by decide)))

theorem fz1_82_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨84, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 84 (by decide)))

theorem fz1_82_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨85, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 85 (by decide)))

theorem fz1_82_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨86, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 86 (by decide)))

theorem fz1_82_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨87, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 87 (by decide)))

theorem fz1_82_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨88, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 88 (by decide)))

theorem fz1_82_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨89, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 89 (by decide)))

theorem fz1_82_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨90, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 90 (by decide)))

theorem fz1_82_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨91, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 91 (by decide)))

theorem fz1_82_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨92, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 92 (by decide)))

theorem fz1_82_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨93, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 93 (by decide)))

theorem fz1_82_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨94, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 94 (by decide)))

theorem fz1_82_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨95, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 95 (by decide)))

theorem fz1_82_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨96, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 96 (by decide)))

theorem fz1_82_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨97, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 97 (by decide)))

theorem fz1_82_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨98, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 98 (by decide)))

theorem fz1_82_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨99, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 99 (by decide)))

theorem fz1_82_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨100, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 100 (by decide)))

theorem fz1_82_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨101, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 101 (by decide)))

theorem fz1_82_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨102, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 102 (by decide)))

theorem fz1_82_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨103, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 103 (by decide)))

theorem fz1_82_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨104, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 104 (by decide)))

theorem fz1_82_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨105, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 105 (by decide)))

theorem fz1_82_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨106, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 106 (by decide)))

theorem fz1_82_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨107, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 107 (by decide)))

theorem fz1_82_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨108, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 108 (by decide)))

theorem fz1_82_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨109, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 109 (by decide)))

theorem fz1_82_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨110, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 110 (by decide)))

theorem fz1_82_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨111, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 111 (by decide)))

theorem fz1_82_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨112, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 112 (by decide)))

theorem fz1_82_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨113, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 113 (by decide)))

theorem fz1_82_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨114, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 114 (by decide)))

theorem fz1_82_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK82)) = 0 :=
  repsFixedCard rK82 ⟨115, by decide⟩ R82 hpxR82 hcardq82
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_82) 115 (by decide)))

theorem fixz2_82 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK82) (retConj 2 (Q2.R82_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_82_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨1, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 1 (by decide)))

theorem fz2_82_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨2, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 2 (by decide)))

theorem fz2_82_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨4, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 4 (by decide)))

theorem fz2_82_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨5, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 5 (by decide)))

theorem fz2_82_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨6, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 6 (by decide)))

theorem fz2_82_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨7, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 7 (by decide)))

theorem fz2_82_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨8, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 8 (by decide)))

theorem fz2_82_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨9, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 9 (by decide)))

theorem fz2_82_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨11, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 11 (by decide)))

theorem fz2_82_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨13, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 13 (by decide)))

theorem fz2_82_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨14, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 14 (by decide)))

theorem fz2_82_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨15, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 15 (by decide)))

theorem fz2_82_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨16, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 16 (by decide)))

theorem fz2_82_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨17, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 17 (by decide)))

theorem fz2_82_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨18, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 18 (by decide)))

theorem fz2_82_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨19, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 19 (by decide)))

theorem fz2_82_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨20, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 20 (by decide)))

theorem fz2_82_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨22, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 22 (by decide)))

theorem fz2_82_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨23, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 23 (by decide)))

theorem fz2_82_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨24, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 24 (by decide)))

theorem fz2_82_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨25, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 25 (by decide)))

theorem fz2_82_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨26, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 26 (by decide)))

theorem fz2_82_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨27, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 27 (by decide)))

theorem fz2_82_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨28, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 28 (by decide)))

theorem fz2_82_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨29, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 29 (by decide)))

theorem fz2_82_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨30, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 30 (by decide)))

theorem fz2_82_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨31, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 31 (by decide)))

theorem fz2_82_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨32, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 32 (by decide)))

theorem fz2_82_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨33, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 33 (by decide)))

theorem fz2_82_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨34, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 34 (by decide)))

theorem fz2_82_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨35, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 35 (by decide)))

theorem fz2_82_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨36, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 36 (by decide)))

theorem fz2_82_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨37, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 37 (by decide)))

theorem fz2_82_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨38, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 38 (by decide)))

theorem fz2_82_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨39, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 39 (by decide)))

theorem fz2_82_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨40, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 40 (by decide)))

theorem fz2_82_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨41, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 41 (by decide)))

theorem fz2_82_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨42, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 42 (by decide)))

theorem fz2_82_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨43, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 43 (by decide)))

theorem fz2_82_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨44, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 44 (by decide)))

theorem fz2_82_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨45, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 45 (by decide)))

theorem fz2_82_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨46, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 46 (by decide)))

theorem fz2_82_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨47, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 47 (by decide)))

theorem fz2_82_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨48, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 48 (by decide)))

theorem fz2_82_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨49, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 49 (by decide)))

theorem fz2_82_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨50, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 50 (by decide)))

theorem fz2_82_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨51, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 51 (by decide)))

theorem fz2_82_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨52, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 52 (by decide)))

theorem fz2_82_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨54, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 54 (by decide)))

theorem fz2_82_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨55, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 55 (by decide)))

theorem fz2_82_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨56, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 56 (by decide)))

theorem fz2_82_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨57, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 57 (by decide)))

theorem fz2_82_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨58, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 58 (by decide)))

theorem fz2_82_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨59, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 59 (by decide)))

theorem fz2_82_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨60, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 60 (by decide)))

theorem fz2_82_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨61, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 61 (by decide)))

theorem fz2_82_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨62, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 62 (by decide)))

theorem fz2_82_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨63, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 63 (by decide)))

theorem fz2_82_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨64, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 64 (by decide)))

theorem fz2_82_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨65, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 65 (by decide)))

theorem fz2_82_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨66, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 66 (by decide)))

theorem fz2_82_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨67, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 67 (by decide)))

theorem fz2_82_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨68, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 68 (by decide)))

theorem fz2_82_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨69, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 69 (by decide)))

theorem fz2_82_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨70, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 70 (by decide)))

theorem fz2_82_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨71, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 71 (by decide)))

theorem fz2_82_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨72, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 72 (by decide)))

theorem fz2_82_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨73, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 73 (by decide)))

theorem fz2_82_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨74, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 74 (by decide)))

theorem fz2_82_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨75, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 75 (by decide)))

theorem fz2_82_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨76, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 76 (by decide)))

theorem fz2_82_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨77, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 77 (by decide)))

theorem fz2_82_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨78, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 78 (by decide)))

theorem fz2_82_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨79, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 79 (by decide)))

theorem fz2_82_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨80, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 80 (by decide)))

theorem fz2_82_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨81, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 81 (by decide)))

theorem fz2_82_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨83, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 83 (by decide)))

theorem fz2_82_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨84, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 84 (by decide)))

theorem fz2_82_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨85, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 85 (by decide)))

theorem fz2_82_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨86, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 86 (by decide)))

theorem fz2_82_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨87, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 87 (by decide)))

theorem fz2_82_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨88, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 88 (by decide)))

theorem fz2_82_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨89, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 89 (by decide)))

theorem fz2_82_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨90, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 90 (by decide)))

theorem fz2_82_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨91, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 91 (by decide)))

theorem fz2_82_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨92, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 92 (by decide)))

theorem fz2_82_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨93, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 93 (by decide)))

theorem fz2_82_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨94, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 94 (by decide)))

theorem fz2_82_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨95, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 95 (by decide)))

theorem fz2_82_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨96, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 96 (by decide)))

theorem fz2_82_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨97, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 97 (by decide)))

theorem fz2_82_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨98, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 98 (by decide)))

theorem fz2_82_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨99, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 99 (by decide)))

theorem fz2_82_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨100, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 100 (by decide)))

theorem fz2_82_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨101, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 101 (by decide)))

theorem fz2_82_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨102, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 102 (by decide)))

theorem fz2_82_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨103, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 103 (by decide)))

theorem fz2_82_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨104, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 104 (by decide)))

theorem fz2_82_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨105, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 105 (by decide)))

theorem fz2_82_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨106, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 106 (by decide)))

theorem fz2_82_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨107, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 107 (by decide)))

theorem fz2_82_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨108, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 108 (by decide)))

theorem fz2_82_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨109, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 109 (by decide)))

theorem fz2_82_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨110, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 110 (by decide)))

theorem fz2_82_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨111, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 111 (by decide)))

theorem fz2_82_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨112, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 112 (by decide)))

theorem fz2_82_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨113, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 113 (by decide)))

theorem fz2_82_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨114, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 114 (by decide)))

theorem fz2_82_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK82)) = 0 :=
  Q2.repsFixedCard2 rK82 ⟨115, by decide⟩ Q2.R82_2 Q2.hpxR82_2 Q2.hcardq82_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_82) 115 (by decide)))

end LeanDring.P5Presentation
