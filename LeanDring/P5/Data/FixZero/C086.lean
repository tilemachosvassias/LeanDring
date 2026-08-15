/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C029
import LeanDring.P5.Data.EntryK.C030
import LeanDring.P5.Data.EntryK.C031
import LeanDring.P5.Data.EntryK.C032
import LeanDring.P5.Data.EntryK.C033

/-!
# Species-table cells, off-support emptiness certificates, chunk 85

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

theorem fixz1_121 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 36, 37, 38, 39, 40, 42, 43, 45, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 98, 99, 100, 101, 102, 104, 105, 107, 108, 109, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK121) (retConj 1 (R121 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_121_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨1, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 1 (by decide)))

theorem fz1_121_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨3, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 3 (by decide)))

theorem fz1_121_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨4, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 4 (by decide)))

theorem fz1_121_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨5, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 5 (by decide)))

theorem fz1_121_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨6, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 6 (by decide)))

theorem fz1_121_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨7, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 7 (by decide)))

theorem fz1_121_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨8, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 8 (by decide)))

theorem fz1_121_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨9, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 9 (by decide)))

theorem fz1_121_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨11, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 11 (by decide)))

theorem fz1_121_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨13, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 13 (by decide)))

theorem fz1_121_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨14, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 14 (by decide)))

theorem fz1_121_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨15, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 15 (by decide)))

theorem fz1_121_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨16, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 16 (by decide)))

theorem fz1_121_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨17, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 17 (by decide)))

theorem fz1_121_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨18, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 18 (by decide)))

theorem fz1_121_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨19, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 19 (by decide)))

theorem fz1_121_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨21, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 21 (by decide)))

theorem fz1_121_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨22, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 22 (by decide)))

theorem fz1_121_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨23, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 23 (by decide)))

theorem fz1_121_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨24, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 24 (by decide)))

theorem fz1_121_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨25, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 25 (by decide)))

theorem fz1_121_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨26, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 26 (by decide)))

theorem fz1_121_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨27, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 27 (by decide)))

theorem fz1_121_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨28, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 28 (by decide)))

theorem fz1_121_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨29, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 29 (by decide)))

theorem fz1_121_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨30, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 30 (by decide)))

theorem fz1_121_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨31, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 31 (by decide)))

theorem fz1_121_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨33, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 33 (by decide)))

theorem fz1_121_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨34, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 34 (by decide)))

theorem fz1_121_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨36, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 36 (by decide)))

theorem fz1_121_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨37, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 37 (by decide)))

theorem fz1_121_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨38, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 38 (by decide)))

theorem fz1_121_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨39, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 39 (by decide)))

theorem fz1_121_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨40, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 40 (by decide)))

theorem fz1_121_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨42, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 42 (by decide)))

theorem fz1_121_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨43, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 43 (by decide)))

theorem fz1_121_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨45, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 45 (by decide)))

theorem fz1_121_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨46, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 46 (by decide)))

theorem fz1_121_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨47, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 47 (by decide)))

theorem fz1_121_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨49, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 49 (by decide)))

theorem fz1_121_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨50, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 50 (by decide)))

theorem fz1_121_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨51, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 51 (by decide)))

theorem fz1_121_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨52, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 52 (by decide)))

theorem fz1_121_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨54, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 54 (by decide)))

theorem fz1_121_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨55, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 55 (by decide)))

theorem fz1_121_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨56, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 56 (by decide)))

theorem fz1_121_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨57, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 57 (by decide)))

theorem fz1_121_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨58, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 58 (by decide)))

theorem fz1_121_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨59, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 59 (by decide)))

theorem fz1_121_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨60, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 60 (by decide)))

theorem fz1_121_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨61, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 61 (by decide)))

theorem fz1_121_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨62, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 62 (by decide)))

theorem fz1_121_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨63, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 63 (by decide)))

theorem fz1_121_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨64, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 64 (by decide)))

theorem fz1_121_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨65, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 65 (by decide)))

theorem fz1_121_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨66, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 66 (by decide)))

theorem fz1_121_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨67, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 67 (by decide)))

theorem fz1_121_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨68, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 68 (by decide)))

theorem fz1_121_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨69, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 69 (by decide)))

theorem fz1_121_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨70, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 70 (by decide)))

theorem fz1_121_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨71, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 71 (by decide)))

theorem fz1_121_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨72, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 72 (by decide)))

theorem fz1_121_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨73, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 73 (by decide)))

theorem fz1_121_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨74, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 74 (by decide)))

theorem fz1_121_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨75, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 75 (by decide)))

theorem fz1_121_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨76, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 76 (by decide)))

theorem fz1_121_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨77, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 77 (by decide)))

theorem fz1_121_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨78, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 78 (by decide)))

theorem fz1_121_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨79, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 79 (by decide)))

theorem fz1_121_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨80, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 80 (by decide)))

theorem fz1_121_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨82, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 82 (by decide)))

theorem fz1_121_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨83, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 83 (by decide)))

theorem fz1_121_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨84, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 84 (by decide)))

theorem fz1_121_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨85, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 85 (by decide)))

theorem fz1_121_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨86, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 86 (by decide)))

theorem fz1_121_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨87, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 87 (by decide)))

theorem fz1_121_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨88, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 88 (by decide)))

theorem fz1_121_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨89, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 89 (by decide)))

theorem fz1_121_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨90, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 90 (by decide)))

theorem fz1_121_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨91, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 91 (by decide)))

theorem fz1_121_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨92, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 92 (by decide)))

theorem fz1_121_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨93, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 93 (by decide)))

theorem fz1_121_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨95, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 95 (by decide)))

theorem fz1_121_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨96, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 96 (by decide)))

theorem fz1_121_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨98, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 98 (by decide)))

theorem fz1_121_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨99, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 99 (by decide)))

theorem fz1_121_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨100, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 100 (by decide)))

theorem fz1_121_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨101, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 101 (by decide)))

theorem fz1_121_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨102, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 102 (by decide)))

theorem fz1_121_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨104, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 104 (by decide)))

theorem fz1_121_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨105, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 105 (by decide)))

theorem fz1_121_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨107, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 107 (by decide)))

theorem fz1_121_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨108, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 108 (by decide)))

theorem fz1_121_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨109, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 109 (by decide)))

theorem fz1_121_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨111, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 111 (by decide)))

theorem fz1_121_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨112, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 112 (by decide)))

theorem fz1_121_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨113, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 113 (by decide)))

theorem fz1_121_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨114, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 114 (by decide)))

theorem fz1_121_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨115, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 115 (by decide)))

theorem fz1_121_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨116, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 116 (by decide)))

theorem fz1_121_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨117, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 117 (by decide)))

theorem fz1_121_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨118, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 118 (by decide)))

theorem fz1_121_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨119, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 119 (by decide)))

theorem fz1_121_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨120, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 120 (by decide)))

theorem fz1_121_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨122, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 122 (by decide)))

theorem fz1_121_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨123, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 123 (by decide)))

theorem fz1_121_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨124, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 124 (by decide)))

theorem fz1_121_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨125, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 125 (by decide)))

theorem fz1_121_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨126, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 126 (by decide)))

theorem fz1_121_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨127, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 127 (by decide)))

theorem fz1_121_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨128, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 128 (by decide)))

theorem fz1_121_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨129, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 129 (by decide)))

theorem fz1_121_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨130, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 130 (by decide)))

theorem fz1_121_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨131, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 131 (by decide)))

theorem fz1_121_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨132, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 132 (by decide)))

theorem fz1_121_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨133, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 133 (by decide)))

theorem fz1_121_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨134, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 134 (by decide)))

theorem fz1_121_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨135, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 135 (by decide)))

theorem fz1_121_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨136, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 136 (by decide)))

theorem fz1_121_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨137, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 137 (by decide)))

theorem fz1_121_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨138, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 138 (by decide)))

theorem fz1_121_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨139, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 139 (by decide)))

theorem fz1_121_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨140, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 140 (by decide)))

theorem fz1_121_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨141, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 141 (by decide)))

theorem fz1_121_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨142, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 142 (by decide)))

theorem fz1_121_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨143, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 143 (by decide)))

theorem fz1_121_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨144, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 144 (by decide)))

theorem fz1_121_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨145, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 145 (by decide)))

theorem fz1_121_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK121)) = 0 :=
  repsFixedCard rK121 ⟨146, by decide⟩ R121 hpxR121 hcardq121
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_121) 146 (by decide)))

theorem fixz2_121 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 36, 37, 38, 39, 40, 42, 43, 45, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 98, 99, 100, 101, 102, 104, 105, 107, 108, 109, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK121) (retConj 2 (Q2.R121_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_121_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨1, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 1 (by decide)))

theorem fz2_121_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨3, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 3 (by decide)))

theorem fz2_121_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨4, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 4 (by decide)))

theorem fz2_121_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨5, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 5 (by decide)))

theorem fz2_121_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨6, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 6 (by decide)))

theorem fz2_121_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨7, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 7 (by decide)))

theorem fz2_121_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨8, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 8 (by decide)))

theorem fz2_121_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨9, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 9 (by decide)))

theorem fz2_121_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨11, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 11 (by decide)))

theorem fz2_121_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨13, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 13 (by decide)))

theorem fz2_121_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨14, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 14 (by decide)))

theorem fz2_121_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨15, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 15 (by decide)))

theorem fz2_121_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨16, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 16 (by decide)))

theorem fz2_121_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨17, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 17 (by decide)))

theorem fz2_121_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨18, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 18 (by decide)))

theorem fz2_121_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨19, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 19 (by decide)))

theorem fz2_121_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨21, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 21 (by decide)))

theorem fz2_121_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨22, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 22 (by decide)))

theorem fz2_121_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨23, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 23 (by decide)))

theorem fz2_121_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨24, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 24 (by decide)))

theorem fz2_121_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨25, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 25 (by decide)))

theorem fz2_121_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨26, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 26 (by decide)))

theorem fz2_121_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨27, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 27 (by decide)))

theorem fz2_121_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨28, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 28 (by decide)))

theorem fz2_121_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨29, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 29 (by decide)))

theorem fz2_121_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨30, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 30 (by decide)))

theorem fz2_121_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨31, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 31 (by decide)))

theorem fz2_121_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨33, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 33 (by decide)))

theorem fz2_121_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨34, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 34 (by decide)))

theorem fz2_121_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨36, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 36 (by decide)))

theorem fz2_121_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨37, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 37 (by decide)))

theorem fz2_121_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨38, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 38 (by decide)))

theorem fz2_121_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨39, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 39 (by decide)))

theorem fz2_121_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨40, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 40 (by decide)))

theorem fz2_121_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨42, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 42 (by decide)))

theorem fz2_121_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨43, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 43 (by decide)))

theorem fz2_121_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨45, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 45 (by decide)))

theorem fz2_121_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨46, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 46 (by decide)))

theorem fz2_121_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨47, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 47 (by decide)))

theorem fz2_121_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨49, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 49 (by decide)))

theorem fz2_121_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨50, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 50 (by decide)))

theorem fz2_121_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨51, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 51 (by decide)))

theorem fz2_121_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨52, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 52 (by decide)))

theorem fz2_121_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨54, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 54 (by decide)))

theorem fz2_121_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨55, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 55 (by decide)))

theorem fz2_121_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨56, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 56 (by decide)))

theorem fz2_121_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨57, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 57 (by decide)))

theorem fz2_121_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨58, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 58 (by decide)))

theorem fz2_121_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨59, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 59 (by decide)))

theorem fz2_121_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨60, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 60 (by decide)))

theorem fz2_121_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨61, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 61 (by decide)))

theorem fz2_121_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨62, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 62 (by decide)))

theorem fz2_121_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨63, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 63 (by decide)))

theorem fz2_121_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨64, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 64 (by decide)))

theorem fz2_121_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨65, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 65 (by decide)))

theorem fz2_121_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨66, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 66 (by decide)))

theorem fz2_121_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨67, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 67 (by decide)))

theorem fz2_121_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨68, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 68 (by decide)))

theorem fz2_121_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨69, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 69 (by decide)))

theorem fz2_121_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨70, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 70 (by decide)))

theorem fz2_121_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨71, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 71 (by decide)))

theorem fz2_121_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨72, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 72 (by decide)))

theorem fz2_121_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨73, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 73 (by decide)))

theorem fz2_121_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨74, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 74 (by decide)))

theorem fz2_121_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨75, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 75 (by decide)))

theorem fz2_121_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨76, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 76 (by decide)))

theorem fz2_121_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨77, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 77 (by decide)))

theorem fz2_121_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨78, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 78 (by decide)))

theorem fz2_121_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨79, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 79 (by decide)))

theorem fz2_121_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨80, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 80 (by decide)))

theorem fz2_121_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨82, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 82 (by decide)))

theorem fz2_121_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨83, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 83 (by decide)))

theorem fz2_121_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨84, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 84 (by decide)))

theorem fz2_121_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨85, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 85 (by decide)))

theorem fz2_121_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨86, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 86 (by decide)))

theorem fz2_121_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨87, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 87 (by decide)))

theorem fz2_121_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨88, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 88 (by decide)))

theorem fz2_121_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨89, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 89 (by decide)))

theorem fz2_121_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨90, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 90 (by decide)))

theorem fz2_121_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨91, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 91 (by decide)))

theorem fz2_121_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨92, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 92 (by decide)))

theorem fz2_121_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨93, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 93 (by decide)))

theorem fz2_121_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨95, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 95 (by decide)))

theorem fz2_121_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨96, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 96 (by decide)))

theorem fz2_121_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨98, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 98 (by decide)))

theorem fz2_121_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨99, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 99 (by decide)))

theorem fz2_121_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨100, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 100 (by decide)))

theorem fz2_121_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨101, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 101 (by decide)))

theorem fz2_121_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨102, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 102 (by decide)))

theorem fz2_121_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨104, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 104 (by decide)))

theorem fz2_121_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨105, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 105 (by decide)))

theorem fz2_121_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨107, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 107 (by decide)))

theorem fz2_121_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨108, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 108 (by decide)))

theorem fz2_121_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨109, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 109 (by decide)))

theorem fz2_121_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨111, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 111 (by decide)))

theorem fz2_121_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨112, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 112 (by decide)))

theorem fz2_121_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨113, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 113 (by decide)))

theorem fz2_121_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨114, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 114 (by decide)))

theorem fz2_121_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨115, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 115 (by decide)))

theorem fz2_121_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨116, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 116 (by decide)))

theorem fz2_121_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨117, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 117 (by decide)))

theorem fz2_121_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨118, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 118 (by decide)))

theorem fz2_121_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨119, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 119 (by decide)))

theorem fz2_121_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨120, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 120 (by decide)))

theorem fz2_121_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨122, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 122 (by decide)))

theorem fz2_121_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨123, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 123 (by decide)))

theorem fz2_121_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨124, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 124 (by decide)))

theorem fz2_121_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨125, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 125 (by decide)))

theorem fz2_121_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨126, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 126 (by decide)))

theorem fz2_121_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨127, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 127 (by decide)))

theorem fz2_121_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨128, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 128 (by decide)))

theorem fz2_121_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨129, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 129 (by decide)))

theorem fz2_121_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨130, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 130 (by decide)))

theorem fz2_121_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨131, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 131 (by decide)))

theorem fz2_121_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨132, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 132 (by decide)))

theorem fz2_121_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨133, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 133 (by decide)))

theorem fz2_121_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨134, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 134 (by decide)))

theorem fz2_121_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨135, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 135 (by decide)))

theorem fz2_121_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨136, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 136 (by decide)))

theorem fz2_121_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨137, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 137 (by decide)))

theorem fz2_121_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨138, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 138 (by decide)))

theorem fz2_121_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨139, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 139 (by decide)))

theorem fz2_121_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨140, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 140 (by decide)))

theorem fz2_121_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨141, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 141 (by decide)))

theorem fz2_121_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨142, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 142 (by decide)))

theorem fz2_121_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨143, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 143 (by decide)))

theorem fz2_121_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨144, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 144 (by decide)))

theorem fz2_121_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨145, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 145 (by decide)))

theorem fz2_121_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK121)) = 0 :=
  Q2.repsFixedCard2 rK121 ⟨146, by decide⟩ Q2.R121_2 Q2.hpxR121_2 Q2.hcardq121_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_121) 146 (by decide)))

theorem fixz1_122 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 37, 38, 39, 40, 41, 43, 44, 46, 47, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 91, 92, 93, 94, 95, 96, 97, 99, 100, 101, 102, 103, 105, 106, 108, 109, 110, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK122) (retConj 1 (R122 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_122_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨1, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 1 (by decide)))

theorem fz1_122_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨3, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 3 (by decide)))

theorem fz1_122_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨4, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 4 (by decide)))

theorem fz1_122_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨5, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 5 (by decide)))

theorem fz1_122_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨6, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 6 (by decide)))

theorem fz1_122_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨7, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 7 (by decide)))

theorem fz1_122_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨8, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 8 (by decide)))

theorem fz1_122_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨9, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 9 (by decide)))

theorem fz1_122_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨11, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 11 (by decide)))

theorem fz1_122_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨13, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 13 (by decide)))

theorem fz1_122_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨14, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 14 (by decide)))

theorem fz1_122_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨15, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 15 (by decide)))

theorem fz1_122_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨16, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 16 (by decide)))

theorem fz1_122_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨17, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 17 (by decide)))

theorem fz1_122_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨18, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 18 (by decide)))

theorem fz1_122_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨19, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 19 (by decide)))

theorem fz1_122_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨21, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 21 (by decide)))

theorem fz1_122_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨22, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 22 (by decide)))

theorem fz1_122_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨23, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 23 (by decide)))

theorem fz1_122_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨24, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 24 (by decide)))

theorem fz1_122_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨25, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 25 (by decide)))

theorem fz1_122_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨26, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 26 (by decide)))

theorem fz1_122_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨27, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 27 (by decide)))

theorem fz1_122_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨29, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 29 (by decide)))

theorem fz1_122_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨30, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 30 (by decide)))

theorem fz1_122_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨31, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 31 (by decide)))

theorem fz1_122_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨32, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 32 (by decide)))

theorem fz1_122_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨33, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 33 (by decide)))

theorem fz1_122_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨34, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 34 (by decide)))

theorem fz1_122_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨35, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 35 (by decide)))

theorem fz1_122_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨37, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 37 (by decide)))

theorem fz1_122_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨38, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 38 (by decide)))

theorem fz1_122_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨39, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 39 (by decide)))

theorem fz1_122_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨40, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 40 (by decide)))

theorem fz1_122_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨41, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 41 (by decide)))

theorem fz1_122_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨43, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 43 (by decide)))

theorem fz1_122_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨44, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 44 (by decide)))

theorem fz1_122_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨46, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 46 (by decide)))

theorem fz1_122_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨47, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 47 (by decide)))

theorem fz1_122_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨48, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 48 (by decide)))

theorem fz1_122_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨50, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 50 (by decide)))

theorem fz1_122_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨51, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 51 (by decide)))

theorem fz1_122_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨52, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 52 (by decide)))

theorem fz1_122_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨54, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 54 (by decide)))

theorem fz1_122_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨55, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 55 (by decide)))

theorem fz1_122_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨56, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 56 (by decide)))

theorem fz1_122_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨57, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 57 (by decide)))

theorem fz1_122_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨58, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 58 (by decide)))

theorem fz1_122_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨59, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 59 (by decide)))

theorem fz1_122_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨60, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 60 (by decide)))

theorem fz1_122_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨61, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 61 (by decide)))

theorem fz1_122_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨62, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 62 (by decide)))

theorem fz1_122_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨63, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 63 (by decide)))

theorem fz1_122_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨64, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 64 (by decide)))

theorem fz1_122_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨65, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 65 (by decide)))

theorem fz1_122_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨66, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 66 (by decide)))

theorem fz1_122_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨67, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 67 (by decide)))

theorem fz1_122_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨68, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 68 (by decide)))

theorem fz1_122_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨69, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 69 (by decide)))

theorem fz1_122_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨70, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 70 (by decide)))

theorem fz1_122_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨71, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 71 (by decide)))

theorem fz1_122_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨72, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 72 (by decide)))

theorem fz1_122_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨73, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 73 (by decide)))

theorem fz1_122_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨74, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 74 (by decide)))

theorem fz1_122_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨75, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 75 (by decide)))

theorem fz1_122_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨76, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 76 (by decide)))

theorem fz1_122_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨77, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 77 (by decide)))

theorem fz1_122_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨78, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 78 (by decide)))

theorem fz1_122_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨79, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 79 (by decide)))

theorem fz1_122_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨80, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 80 (by decide)))

theorem fz1_122_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨82, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 82 (by decide)))

theorem fz1_122_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨83, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 83 (by decide)))

theorem fz1_122_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨84, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 84 (by decide)))

theorem fz1_122_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨85, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 85 (by decide)))

theorem fz1_122_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨86, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 86 (by decide)))

theorem fz1_122_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨87, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 87 (by decide)))

theorem fz1_122_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨88, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 88 (by decide)))

theorem fz1_122_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨89, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 89 (by decide)))

theorem fz1_122_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨91, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 91 (by decide)))

theorem fz1_122_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨92, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 92 (by decide)))

theorem fz1_122_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨93, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 93 (by decide)))

theorem fz1_122_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨94, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 94 (by decide)))

theorem fz1_122_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨95, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 95 (by decide)))

theorem fz1_122_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨96, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 96 (by decide)))

theorem fz1_122_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨97, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 97 (by decide)))

theorem fz1_122_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨99, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 99 (by decide)))

theorem fz1_122_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨100, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 100 (by decide)))

theorem fz1_122_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨101, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 101 (by decide)))

theorem fz1_122_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨102, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 102 (by decide)))

theorem fz1_122_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨103, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 103 (by decide)))

theorem fz1_122_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨105, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 105 (by decide)))

theorem fz1_122_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨106, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 106 (by decide)))

theorem fz1_122_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨108, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 108 (by decide)))

theorem fz1_122_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨109, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 109 (by decide)))

theorem fz1_122_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨110, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 110 (by decide)))

theorem fz1_122_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨112, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 112 (by decide)))

theorem fz1_122_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨113, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 113 (by decide)))

theorem fz1_122_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨114, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 114 (by decide)))

theorem fz1_122_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨115, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 115 (by decide)))

theorem fz1_122_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨116, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 116 (by decide)))

theorem fz1_122_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨117, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 117 (by decide)))

theorem fz1_122_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨118, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 118 (by decide)))

theorem fz1_122_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨119, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 119 (by decide)))

theorem fz1_122_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨120, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 120 (by decide)))

theorem fz1_122_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨121, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 121 (by decide)))

theorem fz1_122_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨123, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 123 (by decide)))

theorem fz1_122_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨124, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 124 (by decide)))

theorem fz1_122_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨125, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 125 (by decide)))

theorem fz1_122_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨126, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 126 (by decide)))

theorem fz1_122_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨127, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 127 (by decide)))

theorem fz1_122_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨128, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 128 (by decide)))

theorem fz1_122_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨129, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 129 (by decide)))

theorem fz1_122_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨130, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 130 (by decide)))

theorem fz1_122_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨131, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 131 (by decide)))

theorem fz1_122_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨132, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 132 (by decide)))

theorem fz1_122_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨133, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 133 (by decide)))

theorem fz1_122_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨134, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 134 (by decide)))

theorem fz1_122_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨135, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 135 (by decide)))

theorem fz1_122_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨136, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 136 (by decide)))

theorem fz1_122_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨137, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 137 (by decide)))

theorem fz1_122_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨138, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 138 (by decide)))

theorem fz1_122_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨139, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 139 (by decide)))

theorem fz1_122_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨140, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 140 (by decide)))

theorem fz1_122_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨141, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 141 (by decide)))

theorem fz1_122_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨142, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 142 (by decide)))

theorem fz1_122_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨143, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 143 (by decide)))

theorem fz1_122_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨144, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 144 (by decide)))

theorem fz1_122_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨145, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 145 (by decide)))

theorem fz1_122_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK122)) = 0 :=
  repsFixedCard rK122 ⟨146, by decide⟩ R122 hpxR122 hcardq122
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_122) 146 (by decide)))

theorem fixz2_122 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 37, 38, 39, 40, 41, 43, 44, 46, 47, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 91, 92, 93, 94, 95, 96, 97, 99, 100, 101, 102, 103, 105, 106, 108, 109, 110, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK122) (retConj 2 (Q2.R122_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_122_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨1, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 1 (by decide)))

theorem fz2_122_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨3, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 3 (by decide)))

theorem fz2_122_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨4, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 4 (by decide)))

theorem fz2_122_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨5, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 5 (by decide)))

theorem fz2_122_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨6, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 6 (by decide)))

theorem fz2_122_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨7, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 7 (by decide)))

theorem fz2_122_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨8, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 8 (by decide)))

theorem fz2_122_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨9, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 9 (by decide)))

theorem fz2_122_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨11, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 11 (by decide)))

theorem fz2_122_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨13, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 13 (by decide)))

theorem fz2_122_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨14, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 14 (by decide)))

theorem fz2_122_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨15, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 15 (by decide)))

theorem fz2_122_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨16, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 16 (by decide)))

theorem fz2_122_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨17, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 17 (by decide)))

theorem fz2_122_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨18, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 18 (by decide)))

theorem fz2_122_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨19, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 19 (by decide)))

theorem fz2_122_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨21, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 21 (by decide)))

theorem fz2_122_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨22, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 22 (by decide)))

theorem fz2_122_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨23, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 23 (by decide)))

theorem fz2_122_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨24, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 24 (by decide)))

theorem fz2_122_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨25, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 25 (by decide)))

theorem fz2_122_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨26, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 26 (by decide)))

theorem fz2_122_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨27, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 27 (by decide)))

theorem fz2_122_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨29, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 29 (by decide)))

theorem fz2_122_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨30, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 30 (by decide)))

theorem fz2_122_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨31, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 31 (by decide)))

theorem fz2_122_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨32, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 32 (by decide)))

theorem fz2_122_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨33, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 33 (by decide)))

theorem fz2_122_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨34, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 34 (by decide)))

theorem fz2_122_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨35, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 35 (by decide)))

theorem fz2_122_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨37, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 37 (by decide)))

theorem fz2_122_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨38, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 38 (by decide)))

theorem fz2_122_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨39, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 39 (by decide)))

theorem fz2_122_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨40, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 40 (by decide)))

theorem fz2_122_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨41, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 41 (by decide)))

theorem fz2_122_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨43, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 43 (by decide)))

theorem fz2_122_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨44, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 44 (by decide)))

theorem fz2_122_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨46, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 46 (by decide)))

theorem fz2_122_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨47, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 47 (by decide)))

theorem fz2_122_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨48, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 48 (by decide)))

theorem fz2_122_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨50, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 50 (by decide)))

theorem fz2_122_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨51, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 51 (by decide)))

theorem fz2_122_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨52, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 52 (by decide)))

theorem fz2_122_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨54, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 54 (by decide)))

theorem fz2_122_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨55, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 55 (by decide)))

theorem fz2_122_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨56, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 56 (by decide)))

theorem fz2_122_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨57, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 57 (by decide)))

theorem fz2_122_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨58, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 58 (by decide)))

theorem fz2_122_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨59, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 59 (by decide)))

theorem fz2_122_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨60, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 60 (by decide)))

theorem fz2_122_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨61, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 61 (by decide)))

theorem fz2_122_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨62, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 62 (by decide)))

theorem fz2_122_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨63, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 63 (by decide)))

theorem fz2_122_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨64, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 64 (by decide)))

theorem fz2_122_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨65, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 65 (by decide)))

theorem fz2_122_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨66, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 66 (by decide)))

theorem fz2_122_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨67, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 67 (by decide)))

theorem fz2_122_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨68, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 68 (by decide)))

theorem fz2_122_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨69, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 69 (by decide)))

theorem fz2_122_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨70, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 70 (by decide)))

theorem fz2_122_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨71, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 71 (by decide)))

theorem fz2_122_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨72, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 72 (by decide)))

theorem fz2_122_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨73, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 73 (by decide)))

theorem fz2_122_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨74, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 74 (by decide)))

theorem fz2_122_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨75, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 75 (by decide)))

theorem fz2_122_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨76, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 76 (by decide)))

theorem fz2_122_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨77, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 77 (by decide)))

theorem fz2_122_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨78, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 78 (by decide)))

theorem fz2_122_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨79, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 79 (by decide)))

theorem fz2_122_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨80, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 80 (by decide)))

theorem fz2_122_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨82, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 82 (by decide)))

theorem fz2_122_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨83, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 83 (by decide)))

theorem fz2_122_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨84, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 84 (by decide)))

theorem fz2_122_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨85, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 85 (by decide)))

theorem fz2_122_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨86, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 86 (by decide)))

theorem fz2_122_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨87, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 87 (by decide)))

theorem fz2_122_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨88, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 88 (by decide)))

theorem fz2_122_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨89, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 89 (by decide)))

theorem fz2_122_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨91, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 91 (by decide)))

theorem fz2_122_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨92, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 92 (by decide)))

theorem fz2_122_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨93, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 93 (by decide)))

theorem fz2_122_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨94, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 94 (by decide)))

theorem fz2_122_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨95, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 95 (by decide)))

theorem fz2_122_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨96, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 96 (by decide)))

theorem fz2_122_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨97, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 97 (by decide)))

theorem fz2_122_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨99, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 99 (by decide)))

theorem fz2_122_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨100, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 100 (by decide)))

theorem fz2_122_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨101, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 101 (by decide)))

theorem fz2_122_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨102, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 102 (by decide)))

theorem fz2_122_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨103, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 103 (by decide)))

theorem fz2_122_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨105, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 105 (by decide)))

theorem fz2_122_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨106, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 106 (by decide)))

theorem fz2_122_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨108, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 108 (by decide)))

theorem fz2_122_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨109, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 109 (by decide)))

theorem fz2_122_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨110, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 110 (by decide)))

theorem fz2_122_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨112, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 112 (by decide)))

theorem fz2_122_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨113, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 113 (by decide)))

theorem fz2_122_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨114, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 114 (by decide)))

theorem fz2_122_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨115, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 115 (by decide)))

theorem fz2_122_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨116, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 116 (by decide)))

theorem fz2_122_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨117, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 117 (by decide)))

theorem fz2_122_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨118, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 118 (by decide)))

theorem fz2_122_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨119, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 119 (by decide)))

theorem fz2_122_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨120, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 120 (by decide)))

theorem fz2_122_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨121, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 121 (by decide)))

theorem fz2_122_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨123, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 123 (by decide)))

theorem fz2_122_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨124, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 124 (by decide)))

theorem fz2_122_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨125, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 125 (by decide)))

theorem fz2_122_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨126, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 126 (by decide)))

theorem fz2_122_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨127, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 127 (by decide)))

theorem fz2_122_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨128, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 128 (by decide)))

theorem fz2_122_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨129, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 129 (by decide)))

theorem fz2_122_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨130, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 130 (by decide)))

theorem fz2_122_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨131, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 131 (by decide)))

theorem fz2_122_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨132, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 132 (by decide)))

theorem fz2_122_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨133, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 133 (by decide)))

theorem fz2_122_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨134, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 134 (by decide)))

theorem fz2_122_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨135, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 135 (by decide)))

theorem fz2_122_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨136, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 136 (by decide)))

theorem fz2_122_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨137, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 137 (by decide)))

theorem fz2_122_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨138, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 138 (by decide)))

theorem fz2_122_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨139, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 139 (by decide)))

theorem fz2_122_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨140, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 140 (by decide)))

theorem fz2_122_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨141, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 141 (by decide)))

theorem fz2_122_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨142, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 142 (by decide)))

theorem fz2_122_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨143, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 143 (by decide)))

theorem fz2_122_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨144, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 144 (by decide)))

theorem fz2_122_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨145, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 145 (by decide)))

theorem fz2_122_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK122)) = 0 :=
  Q2.repsFixedCard2 rK122 ⟨146, by decide⟩ Q2.R122_2 Q2.hpxR122_2 Q2.hcardq122_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_122) 146 (by decide)))

theorem fixz1_123 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 97, 98, 101, 102, 103, 104, 105, 106, 107, 109, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK123) (retConj 1 (R123 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_123_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨1, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 1 (by decide)))

theorem fz1_123_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨3, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 3 (by decide)))

theorem fz1_123_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨4, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 4 (by decide)))

theorem fz1_123_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨5, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 5 (by decide)))

theorem fz1_123_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨6, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 6 (by decide)))

theorem fz1_123_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨7, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 7 (by decide)))

theorem fz1_123_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨8, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 8 (by decide)))

theorem fz1_123_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨9, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 9 (by decide)))

theorem fz1_123_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨11, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 11 (by decide)))

theorem fz1_123_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨13, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 13 (by decide)))

theorem fz1_123_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨14, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 14 (by decide)))

theorem fz1_123_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨15, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 15 (by decide)))

theorem fz1_123_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨16, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 16 (by decide)))

theorem fz1_123_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨17, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 17 (by decide)))

theorem fz1_123_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨18, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 18 (by decide)))

theorem fz1_123_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨19, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 19 (by decide)))

theorem fz1_123_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨21, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 21 (by decide)))

theorem fz1_123_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨22, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 22 (by decide)))

theorem fz1_123_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨23, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 23 (by decide)))

theorem fz1_123_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨24, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 24 (by decide)))

theorem fz1_123_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨25, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 25 (by decide)))

theorem fz1_123_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨26, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 26 (by decide)))

theorem fz1_123_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨27, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 27 (by decide)))

theorem fz1_123_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨28, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 28 (by decide)))

theorem fz1_123_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨30, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 30 (by decide)))

theorem fz1_123_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨31, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 31 (by decide)))

theorem fz1_123_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨32, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 32 (by decide)))

theorem fz1_123_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨33, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 33 (by decide)))

theorem fz1_123_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨34, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 34 (by decide)))

theorem fz1_123_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨35, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 35 (by decide)))

theorem fz1_123_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨36, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 36 (by decide)))

theorem fz1_123_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨39, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 39 (by decide)))

theorem fz1_123_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨40, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 40 (by decide)))

theorem fz1_123_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨41, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 41 (by decide)))

theorem fz1_123_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨42, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 42 (by decide)))

theorem fz1_123_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨43, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 43 (by decide)))

theorem fz1_123_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨44, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 44 (by decide)))

theorem fz1_123_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨45, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 45 (by decide)))

theorem fz1_123_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨47, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 47 (by decide)))

theorem fz1_123_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨48, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 48 (by decide)))

theorem fz1_123_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨49, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 49 (by decide)))

theorem fz1_123_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨51, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 51 (by decide)))

theorem fz1_123_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨52, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 52 (by decide)))

theorem fz1_123_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨54, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 54 (by decide)))

theorem fz1_123_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨55, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 55 (by decide)))

theorem fz1_123_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨56, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 56 (by decide)))

theorem fz1_123_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨57, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 57 (by decide)))

theorem fz1_123_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨58, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 58 (by decide)))

theorem fz1_123_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨59, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 59 (by decide)))

theorem fz1_123_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨60, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 60 (by decide)))

theorem fz1_123_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨61, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 61 (by decide)))

theorem fz1_123_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨62, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 62 (by decide)))

theorem fz1_123_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨63, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 63 (by decide)))

theorem fz1_123_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨64, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 64 (by decide)))

theorem fz1_123_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨65, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 65 (by decide)))

theorem fz1_123_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨66, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 66 (by decide)))

theorem fz1_123_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨67, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 67 (by decide)))

theorem fz1_123_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨68, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 68 (by decide)))

theorem fz1_123_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨69, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 69 (by decide)))

theorem fz1_123_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨70, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 70 (by decide)))

theorem fz1_123_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨71, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 71 (by decide)))

theorem fz1_123_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨72, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 72 (by decide)))

theorem fz1_123_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨73, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 73 (by decide)))

theorem fz1_123_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨74, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 74 (by decide)))

theorem fz1_123_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨75, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 75 (by decide)))

theorem fz1_123_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨76, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 76 (by decide)))

theorem fz1_123_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨77, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 77 (by decide)))

theorem fz1_123_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨78, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 78 (by decide)))

theorem fz1_123_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨79, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 79 (by decide)))

theorem fz1_123_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨80, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 80 (by decide)))

theorem fz1_123_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨82, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 82 (by decide)))

theorem fz1_123_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨83, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 83 (by decide)))

theorem fz1_123_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨84, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 84 (by decide)))

theorem fz1_123_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨85, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 85 (by decide)))

theorem fz1_123_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨86, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 86 (by decide)))

theorem fz1_123_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨87, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 87 (by decide)))

theorem fz1_123_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨88, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 88 (by decide)))

theorem fz1_123_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨89, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 89 (by decide)))

theorem fz1_123_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨90, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 90 (by decide)))

theorem fz1_123_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨92, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 92 (by decide)))

theorem fz1_123_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨93, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 93 (by decide)))

theorem fz1_123_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨94, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 94 (by decide)))

theorem fz1_123_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨95, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 95 (by decide)))

theorem fz1_123_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨96, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 96 (by decide)))

theorem fz1_123_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨97, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 97 (by decide)))

theorem fz1_123_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨98, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 98 (by decide)))

theorem fz1_123_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨101, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 101 (by decide)))

theorem fz1_123_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨102, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 102 (by decide)))

theorem fz1_123_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨103, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 103 (by decide)))

theorem fz1_123_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨104, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 104 (by decide)))

theorem fz1_123_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨105, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 105 (by decide)))

theorem fz1_123_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨106, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 106 (by decide)))

theorem fz1_123_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨107, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 107 (by decide)))

theorem fz1_123_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨109, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 109 (by decide)))

theorem fz1_123_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨110, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 110 (by decide)))

theorem fz1_123_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨111, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 111 (by decide)))

theorem fz1_123_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨113, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 113 (by decide)))

theorem fz1_123_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨114, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 114 (by decide)))

theorem fz1_123_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨115, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 115 (by decide)))

theorem fz1_123_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨116, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 116 (by decide)))

theorem fz1_123_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨117, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 117 (by decide)))

theorem fz1_123_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨118, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 118 (by decide)))

theorem fz1_123_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨119, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 119 (by decide)))

theorem fz1_123_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨120, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 120 (by decide)))

theorem fz1_123_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨121, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 121 (by decide)))

theorem fz1_123_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨122, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 122 (by decide)))

theorem fz1_123_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨124, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 124 (by decide)))

theorem fz1_123_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨125, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 125 (by decide)))

theorem fz1_123_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨126, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 126 (by decide)))

theorem fz1_123_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨127, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 127 (by decide)))

theorem fz1_123_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨128, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 128 (by decide)))

theorem fz1_123_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨129, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 129 (by decide)))

theorem fz1_123_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨130, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 130 (by decide)))

theorem fz1_123_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨131, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 131 (by decide)))

theorem fz1_123_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨132, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 132 (by decide)))

theorem fz1_123_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨133, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 133 (by decide)))

theorem fz1_123_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨134, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 134 (by decide)))

theorem fz1_123_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨135, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 135 (by decide)))

theorem fz1_123_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨136, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 136 (by decide)))

theorem fz1_123_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨137, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 137 (by decide)))

theorem fz1_123_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨138, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 138 (by decide)))

theorem fz1_123_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨139, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 139 (by decide)))

theorem fz1_123_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨140, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 140 (by decide)))

theorem fz1_123_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨141, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 141 (by decide)))

theorem fz1_123_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨142, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 142 (by decide)))

theorem fz1_123_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨143, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 143 (by decide)))

theorem fz1_123_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨144, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 144 (by decide)))

theorem fz1_123_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨145, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 145 (by decide)))

theorem fz1_123_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK123)) = 0 :=
  repsFixedCard rK123 ⟨146, by decide⟩ R123 hpxR123 hcardq123
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_123) 146 (by decide)))

theorem fixz2_123 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 97, 98, 101, 102, 103, 104, 105, 106, 107, 109, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK123) (retConj 2 (Q2.R123_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_123_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨1, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 1 (by decide)))

theorem fz2_123_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨3, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 3 (by decide)))

theorem fz2_123_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨4, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 4 (by decide)))

theorem fz2_123_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨5, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 5 (by decide)))

theorem fz2_123_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨6, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 6 (by decide)))

theorem fz2_123_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨7, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 7 (by decide)))

theorem fz2_123_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨8, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 8 (by decide)))

theorem fz2_123_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨9, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 9 (by decide)))

theorem fz2_123_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨11, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 11 (by decide)))

theorem fz2_123_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨13, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 13 (by decide)))

theorem fz2_123_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨14, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 14 (by decide)))

theorem fz2_123_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨15, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 15 (by decide)))

theorem fz2_123_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨16, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 16 (by decide)))

theorem fz2_123_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨17, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 17 (by decide)))

theorem fz2_123_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨18, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 18 (by decide)))

theorem fz2_123_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨19, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 19 (by decide)))

theorem fz2_123_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨21, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 21 (by decide)))

theorem fz2_123_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨22, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 22 (by decide)))

theorem fz2_123_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨23, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 23 (by decide)))

theorem fz2_123_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨24, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 24 (by decide)))

theorem fz2_123_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨25, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 25 (by decide)))

theorem fz2_123_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨26, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 26 (by decide)))

theorem fz2_123_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨27, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 27 (by decide)))

theorem fz2_123_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨28, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 28 (by decide)))

theorem fz2_123_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨30, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 30 (by decide)))

theorem fz2_123_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨31, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 31 (by decide)))

theorem fz2_123_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨32, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 32 (by decide)))

theorem fz2_123_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨33, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 33 (by decide)))

theorem fz2_123_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨34, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 34 (by decide)))

theorem fz2_123_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨35, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 35 (by decide)))

theorem fz2_123_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨36, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 36 (by decide)))

theorem fz2_123_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨39, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 39 (by decide)))

theorem fz2_123_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨40, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 40 (by decide)))

theorem fz2_123_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨41, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 41 (by decide)))

theorem fz2_123_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨42, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 42 (by decide)))

theorem fz2_123_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨43, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 43 (by decide)))

theorem fz2_123_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨44, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 44 (by decide)))

theorem fz2_123_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨45, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 45 (by decide)))

theorem fz2_123_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨47, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 47 (by decide)))

theorem fz2_123_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨48, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 48 (by decide)))

theorem fz2_123_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨49, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 49 (by decide)))

theorem fz2_123_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨51, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 51 (by decide)))

theorem fz2_123_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨52, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 52 (by decide)))

theorem fz2_123_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨54, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 54 (by decide)))

theorem fz2_123_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨55, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 55 (by decide)))

theorem fz2_123_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨56, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 56 (by decide)))

theorem fz2_123_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨57, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 57 (by decide)))

theorem fz2_123_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨58, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 58 (by decide)))

theorem fz2_123_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨59, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 59 (by decide)))

theorem fz2_123_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨60, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 60 (by decide)))

theorem fz2_123_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨61, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 61 (by decide)))

theorem fz2_123_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨62, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 62 (by decide)))

theorem fz2_123_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨63, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 63 (by decide)))

theorem fz2_123_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨64, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 64 (by decide)))

theorem fz2_123_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨65, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 65 (by decide)))

theorem fz2_123_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨66, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 66 (by decide)))

theorem fz2_123_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨67, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 67 (by decide)))

theorem fz2_123_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨68, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 68 (by decide)))

theorem fz2_123_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨69, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 69 (by decide)))

theorem fz2_123_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨70, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 70 (by decide)))

theorem fz2_123_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨71, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 71 (by decide)))

theorem fz2_123_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨72, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 72 (by decide)))

theorem fz2_123_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨73, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 73 (by decide)))

theorem fz2_123_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨74, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 74 (by decide)))

theorem fz2_123_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨75, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 75 (by decide)))

theorem fz2_123_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨76, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 76 (by decide)))

theorem fz2_123_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨77, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 77 (by decide)))

theorem fz2_123_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨78, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 78 (by decide)))

theorem fz2_123_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨79, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 79 (by decide)))

theorem fz2_123_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨80, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 80 (by decide)))

theorem fz2_123_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨82, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 82 (by decide)))

theorem fz2_123_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨83, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 83 (by decide)))

theorem fz2_123_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨84, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 84 (by decide)))

theorem fz2_123_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨85, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 85 (by decide)))

theorem fz2_123_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨86, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 86 (by decide)))

theorem fz2_123_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨87, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 87 (by decide)))

theorem fz2_123_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨88, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 88 (by decide)))

theorem fz2_123_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨89, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 89 (by decide)))

theorem fz2_123_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨90, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 90 (by decide)))

theorem fz2_123_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨92, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 92 (by decide)))

theorem fz2_123_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨93, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 93 (by decide)))

theorem fz2_123_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨94, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 94 (by decide)))

theorem fz2_123_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨95, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 95 (by decide)))

theorem fz2_123_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨96, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 96 (by decide)))

theorem fz2_123_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨97, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 97 (by decide)))

theorem fz2_123_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨98, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 98 (by decide)))

theorem fz2_123_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨101, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 101 (by decide)))

theorem fz2_123_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨102, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 102 (by decide)))

theorem fz2_123_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨103, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 103 (by decide)))

theorem fz2_123_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨104, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 104 (by decide)))

theorem fz2_123_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨105, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 105 (by decide)))

theorem fz2_123_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨106, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 106 (by decide)))

theorem fz2_123_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨107, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 107 (by decide)))

theorem fz2_123_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨109, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 109 (by decide)))

theorem fz2_123_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨110, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 110 (by decide)))

theorem fz2_123_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨111, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 111 (by decide)))

theorem fz2_123_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨113, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 113 (by decide)))

theorem fz2_123_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨114, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 114 (by decide)))

theorem fz2_123_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨115, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 115 (by decide)))

theorem fz2_123_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨116, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 116 (by decide)))

theorem fz2_123_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨117, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 117 (by decide)))

theorem fz2_123_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨118, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 118 (by decide)))

theorem fz2_123_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨119, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 119 (by decide)))

theorem fz2_123_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨120, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 120 (by decide)))

theorem fz2_123_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨121, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 121 (by decide)))

theorem fz2_123_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨122, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 122 (by decide)))

theorem fz2_123_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨124, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 124 (by decide)))

theorem fz2_123_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨125, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 125 (by decide)))

theorem fz2_123_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨126, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 126 (by decide)))

theorem fz2_123_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨127, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 127 (by decide)))

theorem fz2_123_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨128, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 128 (by decide)))

theorem fz2_123_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨129, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 129 (by decide)))

theorem fz2_123_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨130, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 130 (by decide)))

theorem fz2_123_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨131, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 131 (by decide)))

theorem fz2_123_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨132, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 132 (by decide)))

theorem fz2_123_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨133, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 133 (by decide)))

theorem fz2_123_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨134, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 134 (by decide)))

theorem fz2_123_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨135, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 135 (by decide)))

theorem fz2_123_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨136, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 136 (by decide)))

theorem fz2_123_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨137, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 137 (by decide)))

theorem fz2_123_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨138, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 138 (by decide)))

theorem fz2_123_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨139, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 139 (by decide)))

theorem fz2_123_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨140, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 140 (by decide)))

theorem fz2_123_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨141, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 141 (by decide)))

theorem fz2_123_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨142, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 142 (by decide)))

theorem fz2_123_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨143, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 143 (by decide)))

theorem fz2_123_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨144, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 144 (by decide)))

theorem fz2_123_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨145, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 145 (by decide)))

theorem fz2_123_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK123)) = 0 :=
  Q2.repsFixedCard2 rK123 ⟨146, by decide⟩ Q2.R123_2 Q2.hpxR123_2 Q2.hcardq123_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_123) 146 (by decide)))

theorem fixz1_124 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 93, 94, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 107, 108, 110, 111, 112, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK124) (retConj 1 (R124 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_124_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨1, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 1 (by decide)))

theorem fz1_124_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨3, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 3 (by decide)))

theorem fz1_124_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨4, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 4 (by decide)))

theorem fz1_124_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨5, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 5 (by decide)))

theorem fz1_124_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨6, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 6 (by decide)))

theorem fz1_124_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨7, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 7 (by decide)))

theorem fz1_124_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨8, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 8 (by decide)))

theorem fz1_124_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨9, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 9 (by decide)))

theorem fz1_124_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨11, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 11 (by decide)))

theorem fz1_124_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨13, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 13 (by decide)))

theorem fz1_124_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨14, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 14 (by decide)))

theorem fz1_124_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨15, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 15 (by decide)))

theorem fz1_124_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨16, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 16 (by decide)))

theorem fz1_124_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨17, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 17 (by decide)))

theorem fz1_124_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨18, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 18 (by decide)))

theorem fz1_124_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨19, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 19 (by decide)))

theorem fz1_124_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨21, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 21 (by decide)))

theorem fz1_124_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨22, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 22 (by decide)))

theorem fz1_124_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨23, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 23 (by decide)))

theorem fz1_124_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨24, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 24 (by decide)))

theorem fz1_124_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨25, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 25 (by decide)))

theorem fz1_124_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨26, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 26 (by decide)))

theorem fz1_124_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨27, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 27 (by decide)))

theorem fz1_124_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨28, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 28 (by decide)))

theorem fz1_124_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨29, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 29 (by decide)))

theorem fz1_124_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨31, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 31 (by decide)))

theorem fz1_124_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨32, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 32 (by decide)))

theorem fz1_124_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨34, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 34 (by decide)))

theorem fz1_124_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨35, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 35 (by decide)))

theorem fz1_124_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨36, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 36 (by decide)))

theorem fz1_124_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨37, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 37 (by decide)))

theorem fz1_124_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨38, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 38 (by decide)))

theorem fz1_124_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨40, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 40 (by decide)))

theorem fz1_124_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨41, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 41 (by decide)))

theorem fz1_124_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨42, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 42 (by decide)))

theorem fz1_124_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨43, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 43 (by decide)))

theorem fz1_124_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨44, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 44 (by decide)))

theorem fz1_124_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨45, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 45 (by decide)))

theorem fz1_124_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨46, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 46 (by decide)))

theorem fz1_124_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨48, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 48 (by decide)))

theorem fz1_124_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨49, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 49 (by decide)))

theorem fz1_124_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨50, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 50 (by decide)))

theorem fz1_124_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨52, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 52 (by decide)))

theorem fz1_124_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨54, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 54 (by decide)))

theorem fz1_124_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨55, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 55 (by decide)))

theorem fz1_124_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨56, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 56 (by decide)))

theorem fz1_124_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨57, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 57 (by decide)))

theorem fz1_124_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨58, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 58 (by decide)))

theorem fz1_124_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨59, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 59 (by decide)))

theorem fz1_124_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨60, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 60 (by decide)))

theorem fz1_124_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨61, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 61 (by decide)))

theorem fz1_124_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨62, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 62 (by decide)))

theorem fz1_124_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨63, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 63 (by decide)))

theorem fz1_124_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨64, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 64 (by decide)))

theorem fz1_124_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨65, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 65 (by decide)))

theorem fz1_124_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨66, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 66 (by decide)))

theorem fz1_124_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨67, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 67 (by decide)))

theorem fz1_124_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨68, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 68 (by decide)))

theorem fz1_124_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨69, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 69 (by decide)))

theorem fz1_124_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨70, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 70 (by decide)))

theorem fz1_124_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨71, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 71 (by decide)))

theorem fz1_124_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨72, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 72 (by decide)))

theorem fz1_124_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨73, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 73 (by decide)))

theorem fz1_124_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨74, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 74 (by decide)))

theorem fz1_124_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨75, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 75 (by decide)))

theorem fz1_124_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨76, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 76 (by decide)))

theorem fz1_124_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨77, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 77 (by decide)))

theorem fz1_124_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨78, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 78 (by decide)))

theorem fz1_124_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨79, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 79 (by decide)))

theorem fz1_124_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨80, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 80 (by decide)))

theorem fz1_124_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨82, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 82 (by decide)))

theorem fz1_124_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨83, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 83 (by decide)))

theorem fz1_124_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨84, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 84 (by decide)))

theorem fz1_124_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨85, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 85 (by decide)))

theorem fz1_124_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨86, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 86 (by decide)))

theorem fz1_124_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨87, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 87 (by decide)))

theorem fz1_124_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨88, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 88 (by decide)))

theorem fz1_124_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨89, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 89 (by decide)))

theorem fz1_124_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨90, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 90 (by decide)))

theorem fz1_124_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨91, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 91 (by decide)))

theorem fz1_124_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨93, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 93 (by decide)))

theorem fz1_124_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨94, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 94 (by decide)))

theorem fz1_124_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨96, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 96 (by decide)))

theorem fz1_124_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨97, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 97 (by decide)))

theorem fz1_124_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨98, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 98 (by decide)))

theorem fz1_124_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨99, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 99 (by decide)))

theorem fz1_124_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨100, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 100 (by decide)))

theorem fz1_124_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨102, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 102 (by decide)))

theorem fz1_124_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨103, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 103 (by decide)))

theorem fz1_124_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨104, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 104 (by decide)))

theorem fz1_124_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨105, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 105 (by decide)))

theorem fz1_124_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨106, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 106 (by decide)))

theorem fz1_124_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨107, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 107 (by decide)))

theorem fz1_124_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨108, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 108 (by decide)))

theorem fz1_124_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨110, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 110 (by decide)))

theorem fz1_124_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨111, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 111 (by decide)))

theorem fz1_124_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨112, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 112 (by decide)))

theorem fz1_124_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨114, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 114 (by decide)))

theorem fz1_124_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨115, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 115 (by decide)))

theorem fz1_124_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨116, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 116 (by decide)))

theorem fz1_124_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨117, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 117 (by decide)))

theorem fz1_124_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨118, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 118 (by decide)))

theorem fz1_124_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨119, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 119 (by decide)))

theorem fz1_124_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨120, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 120 (by decide)))

theorem fz1_124_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨121, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 121 (by decide)))

theorem fz1_124_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨122, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 122 (by decide)))

theorem fz1_124_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨123, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 123 (by decide)))

theorem fz1_124_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨125, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 125 (by decide)))

theorem fz1_124_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨126, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 126 (by decide)))

theorem fz1_124_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨127, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 127 (by decide)))

theorem fz1_124_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨128, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 128 (by decide)))

theorem fz1_124_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨129, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 129 (by decide)))

theorem fz1_124_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨130, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 130 (by decide)))

theorem fz1_124_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨131, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 131 (by decide)))

theorem fz1_124_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨132, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 132 (by decide)))

theorem fz1_124_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨133, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 133 (by decide)))

theorem fz1_124_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨134, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 134 (by decide)))

theorem fz1_124_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨135, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 135 (by decide)))

theorem fz1_124_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨136, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 136 (by decide)))

theorem fz1_124_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨137, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 137 (by decide)))

theorem fz1_124_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨138, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 138 (by decide)))

theorem fz1_124_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨139, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 139 (by decide)))

theorem fz1_124_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨140, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 140 (by decide)))

theorem fz1_124_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨141, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 141 (by decide)))

theorem fz1_124_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨142, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 142 (by decide)))

theorem fz1_124_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨143, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 143 (by decide)))

theorem fz1_124_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨144, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 144 (by decide)))

theorem fz1_124_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨145, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 145 (by decide)))

theorem fz1_124_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK124)) = 0 :=
  repsFixedCard rK124 ⟨146, by decide⟩ R124 hpxR124 hcardq124
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_124) 146 (by decide)))

theorem fixz2_124 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 93, 94, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 107, 108, 110, 111, 112, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK124) (retConj 2 (Q2.R124_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_124_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨1, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 1 (by decide)))

theorem fz2_124_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨3, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 3 (by decide)))

theorem fz2_124_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨4, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 4 (by decide)))

theorem fz2_124_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨5, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 5 (by decide)))

theorem fz2_124_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨6, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 6 (by decide)))

theorem fz2_124_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨7, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 7 (by decide)))

theorem fz2_124_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨8, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 8 (by decide)))

theorem fz2_124_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨9, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 9 (by decide)))

theorem fz2_124_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨11, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 11 (by decide)))

theorem fz2_124_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨13, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 13 (by decide)))

theorem fz2_124_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨14, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 14 (by decide)))

theorem fz2_124_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨15, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 15 (by decide)))

theorem fz2_124_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨16, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 16 (by decide)))

theorem fz2_124_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨17, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 17 (by decide)))

theorem fz2_124_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨18, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 18 (by decide)))

theorem fz2_124_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨19, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 19 (by decide)))

theorem fz2_124_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨21, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 21 (by decide)))

theorem fz2_124_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨22, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 22 (by decide)))

theorem fz2_124_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨23, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 23 (by decide)))

theorem fz2_124_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨24, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 24 (by decide)))

theorem fz2_124_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨25, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 25 (by decide)))

theorem fz2_124_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨26, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 26 (by decide)))

theorem fz2_124_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨27, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 27 (by decide)))

theorem fz2_124_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨28, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 28 (by decide)))

theorem fz2_124_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨29, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 29 (by decide)))

theorem fz2_124_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨31, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 31 (by decide)))

theorem fz2_124_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨32, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 32 (by decide)))

theorem fz2_124_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨34, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 34 (by decide)))

theorem fz2_124_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨35, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 35 (by decide)))

theorem fz2_124_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨36, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 36 (by decide)))

theorem fz2_124_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨37, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 37 (by decide)))

theorem fz2_124_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨38, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 38 (by decide)))

theorem fz2_124_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨40, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 40 (by decide)))

theorem fz2_124_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨41, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 41 (by decide)))

theorem fz2_124_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨42, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 42 (by decide)))

theorem fz2_124_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨43, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 43 (by decide)))

theorem fz2_124_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨44, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 44 (by decide)))

theorem fz2_124_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨45, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 45 (by decide)))

theorem fz2_124_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨46, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 46 (by decide)))

theorem fz2_124_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨48, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 48 (by decide)))

theorem fz2_124_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨49, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 49 (by decide)))

theorem fz2_124_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨50, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 50 (by decide)))

theorem fz2_124_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨52, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 52 (by decide)))

theorem fz2_124_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨54, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 54 (by decide)))

theorem fz2_124_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨55, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 55 (by decide)))

theorem fz2_124_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨56, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 56 (by decide)))

theorem fz2_124_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨57, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 57 (by decide)))

theorem fz2_124_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨58, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 58 (by decide)))

theorem fz2_124_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨59, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 59 (by decide)))

theorem fz2_124_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨60, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 60 (by decide)))

theorem fz2_124_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨61, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 61 (by decide)))

theorem fz2_124_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨62, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 62 (by decide)))

theorem fz2_124_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨63, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 63 (by decide)))

theorem fz2_124_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨64, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 64 (by decide)))

theorem fz2_124_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨65, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 65 (by decide)))

theorem fz2_124_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨66, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 66 (by decide)))

theorem fz2_124_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨67, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 67 (by decide)))

theorem fz2_124_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨68, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 68 (by decide)))

theorem fz2_124_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨69, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 69 (by decide)))

theorem fz2_124_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨70, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 70 (by decide)))

theorem fz2_124_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨71, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 71 (by decide)))

theorem fz2_124_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨72, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 72 (by decide)))

theorem fz2_124_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨73, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 73 (by decide)))

theorem fz2_124_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨74, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 74 (by decide)))

theorem fz2_124_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨75, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 75 (by decide)))

theorem fz2_124_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨76, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 76 (by decide)))

theorem fz2_124_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨77, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 77 (by decide)))

theorem fz2_124_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨78, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 78 (by decide)))

theorem fz2_124_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨79, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 79 (by decide)))

theorem fz2_124_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨80, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 80 (by decide)))

theorem fz2_124_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨82, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 82 (by decide)))

theorem fz2_124_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨83, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 83 (by decide)))

theorem fz2_124_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨84, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 84 (by decide)))

theorem fz2_124_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨85, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 85 (by decide)))

theorem fz2_124_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨86, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 86 (by decide)))

theorem fz2_124_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨87, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 87 (by decide)))

theorem fz2_124_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨88, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 88 (by decide)))

theorem fz2_124_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨89, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 89 (by decide)))

theorem fz2_124_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨90, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 90 (by decide)))

theorem fz2_124_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨91, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 91 (by decide)))

theorem fz2_124_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨93, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 93 (by decide)))

theorem fz2_124_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨94, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 94 (by decide)))

theorem fz2_124_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨96, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 96 (by decide)))

theorem fz2_124_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨97, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 97 (by decide)))

theorem fz2_124_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨98, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 98 (by decide)))

theorem fz2_124_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨99, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 99 (by decide)))

theorem fz2_124_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨100, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 100 (by decide)))

theorem fz2_124_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨102, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 102 (by decide)))

theorem fz2_124_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨103, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 103 (by decide)))

theorem fz2_124_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨104, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 104 (by decide)))

theorem fz2_124_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨105, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 105 (by decide)))

theorem fz2_124_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨106, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 106 (by decide)))

theorem fz2_124_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨107, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 107 (by decide)))

theorem fz2_124_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨108, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 108 (by decide)))

theorem fz2_124_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨110, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 110 (by decide)))

theorem fz2_124_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨111, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 111 (by decide)))

theorem fz2_124_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨112, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 112 (by decide)))

theorem fz2_124_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨114, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 114 (by decide)))

theorem fz2_124_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨115, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 115 (by decide)))

theorem fz2_124_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨116, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 116 (by decide)))

theorem fz2_124_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨117, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 117 (by decide)))

theorem fz2_124_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨118, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 118 (by decide)))

theorem fz2_124_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨119, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 119 (by decide)))

theorem fz2_124_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨120, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 120 (by decide)))

theorem fz2_124_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨121, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 121 (by decide)))

theorem fz2_124_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨122, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 122 (by decide)))

theorem fz2_124_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨123, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 123 (by decide)))

theorem fz2_124_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨125, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 125 (by decide)))

theorem fz2_124_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨126, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 126 (by decide)))

theorem fz2_124_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨127, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 127 (by decide)))

theorem fz2_124_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨128, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 128 (by decide)))

theorem fz2_124_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨129, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 129 (by decide)))

theorem fz2_124_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨130, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 130 (by decide)))

theorem fz2_124_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨131, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 131 (by decide)))

theorem fz2_124_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨132, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 132 (by decide)))

theorem fz2_124_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨133, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 133 (by decide)))

theorem fz2_124_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨134, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 134 (by decide)))

theorem fz2_124_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨135, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 135 (by decide)))

theorem fz2_124_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨136, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 136 (by decide)))

theorem fz2_124_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨137, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 137 (by decide)))

theorem fz2_124_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨138, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 138 (by decide)))

theorem fz2_124_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨139, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 139 (by decide)))

theorem fz2_124_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨140, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 140 (by decide)))

theorem fz2_124_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨141, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 141 (by decide)))

theorem fz2_124_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨142, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 142 (by decide)))

theorem fz2_124_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨143, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 143 (by decide)))

theorem fz2_124_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨144, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 144 (by decide)))

theorem fz2_124_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨145, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 145 (by decide)))

theorem fz2_124_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK124)) = 0 :=
  Q2.repsFixedCard2 rK124 ⟨146, by decide⟩ Q2.R124_2 Q2.hpxR124_2 Q2.hcardq124_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_124) 146 (by decide)))

theorem fixz1_125 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 35, 36, 37, 38, 39, 41, 42, 44, 45, 46, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 97, 98, 99, 100, 101, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK125) (retConj 1 (R125 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_125_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨1, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 1 (by decide)))

theorem fz1_125_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨3, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 3 (by decide)))

theorem fz1_125_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨4, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 4 (by decide)))

theorem fz1_125_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨5, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 5 (by decide)))

theorem fz1_125_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨6, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 6 (by decide)))

theorem fz1_125_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨7, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 7 (by decide)))

theorem fz1_125_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨8, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 8 (by decide)))

theorem fz1_125_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨9, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 9 (by decide)))

theorem fz1_125_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨11, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 11 (by decide)))

theorem fz1_125_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨13, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 13 (by decide)))

theorem fz1_125_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨14, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 14 (by decide)))

theorem fz1_125_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨15, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 15 (by decide)))

theorem fz1_125_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨16, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 16 (by decide)))

theorem fz1_125_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨17, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 17 (by decide)))

theorem fz1_125_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨18, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 18 (by decide)))

theorem fz1_125_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨19, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 19 (by decide)))

theorem fz1_125_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨21, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 21 (by decide)))

theorem fz1_125_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨22, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 22 (by decide)))

theorem fz1_125_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨23, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 23 (by decide)))

theorem fz1_125_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨24, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 24 (by decide)))

theorem fz1_125_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨25, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 25 (by decide)))

theorem fz1_125_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨26, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 26 (by decide)))

theorem fz1_125_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨27, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 27 (by decide)))

theorem fz1_125_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨28, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 28 (by decide)))

theorem fz1_125_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨29, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 29 (by decide)))

theorem fz1_125_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨30, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 30 (by decide)))

theorem fz1_125_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨32, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 32 (by decide)))

theorem fz1_125_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨33, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 33 (by decide)))

theorem fz1_125_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨35, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 35 (by decide)))

theorem fz1_125_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨36, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 36 (by decide)))

theorem fz1_125_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨37, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 37 (by decide)))

theorem fz1_125_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨38, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 38 (by decide)))

theorem fz1_125_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨39, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 39 (by decide)))

theorem fz1_125_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨41, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 41 (by decide)))

theorem fz1_125_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨42, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 42 (by decide)))

theorem fz1_125_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨44, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 44 (by decide)))

theorem fz1_125_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨45, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 45 (by decide)))

theorem fz1_125_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨46, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 46 (by decide)))

theorem fz1_125_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨47, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 47 (by decide)))

theorem fz1_125_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨48, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 48 (by decide)))

theorem fz1_125_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨49, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 49 (by decide)))

theorem fz1_125_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨50, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 50 (by decide)))

theorem fz1_125_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨51, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 51 (by decide)))

theorem fz1_125_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨54, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 54 (by decide)))

theorem fz1_125_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨55, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 55 (by decide)))

theorem fz1_125_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨56, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 56 (by decide)))

theorem fz1_125_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨57, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 57 (by decide)))

theorem fz1_125_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨58, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 58 (by decide)))

theorem fz1_125_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨59, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 59 (by decide)))

theorem fz1_125_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨60, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 60 (by decide)))

theorem fz1_125_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨61, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 61 (by decide)))

theorem fz1_125_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨62, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 62 (by decide)))

theorem fz1_125_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨63, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 63 (by decide)))

theorem fz1_125_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨64, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 64 (by decide)))

theorem fz1_125_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨65, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 65 (by decide)))

theorem fz1_125_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨66, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 66 (by decide)))

theorem fz1_125_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨67, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 67 (by decide)))

theorem fz1_125_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨68, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 68 (by decide)))

theorem fz1_125_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨69, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 69 (by decide)))

theorem fz1_125_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨70, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 70 (by decide)))

theorem fz1_125_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨71, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 71 (by decide)))

theorem fz1_125_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨72, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 72 (by decide)))

theorem fz1_125_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨73, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 73 (by decide)))

theorem fz1_125_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨74, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 74 (by decide)))

theorem fz1_125_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨75, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 75 (by decide)))

theorem fz1_125_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨76, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 76 (by decide)))

theorem fz1_125_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨77, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 77 (by decide)))

theorem fz1_125_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨78, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 78 (by decide)))

theorem fz1_125_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨79, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 79 (by decide)))

theorem fz1_125_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨80, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 80 (by decide)))

theorem fz1_125_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨82, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 82 (by decide)))

theorem fz1_125_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨83, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 83 (by decide)))

theorem fz1_125_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨84, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 84 (by decide)))

theorem fz1_125_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨85, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 85 (by decide)))

theorem fz1_125_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨86, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 86 (by decide)))

theorem fz1_125_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨87, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 87 (by decide)))

theorem fz1_125_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨88, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 88 (by decide)))

theorem fz1_125_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨89, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 89 (by decide)))

theorem fz1_125_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨90, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 90 (by decide)))

theorem fz1_125_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨91, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 91 (by decide)))

theorem fz1_125_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨92, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 92 (by decide)))

theorem fz1_125_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨94, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 94 (by decide)))

theorem fz1_125_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨95, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 95 (by decide)))

theorem fz1_125_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨97, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 97 (by decide)))

theorem fz1_125_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨98, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 98 (by decide)))

theorem fz1_125_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨99, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 99 (by decide)))

theorem fz1_125_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨100, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 100 (by decide)))

theorem fz1_125_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨101, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 101 (by decide)))

theorem fz1_125_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨103, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 103 (by decide)))

theorem fz1_125_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨104, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 104 (by decide)))

theorem fz1_125_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨106, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 106 (by decide)))

theorem fz1_125_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨107, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 107 (by decide)))

theorem fz1_125_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨108, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 108 (by decide)))

theorem fz1_125_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨109, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 109 (by decide)))

theorem fz1_125_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨110, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 110 (by decide)))

theorem fz1_125_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨111, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 111 (by decide)))

theorem fz1_125_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨112, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 112 (by decide)))

theorem fz1_125_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨113, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 113 (by decide)))

theorem fz1_125_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨115, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 115 (by decide)))

theorem fz1_125_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨116, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 116 (by decide)))

theorem fz1_125_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨117, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 117 (by decide)))

theorem fz1_125_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨118, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 118 (by decide)))

theorem fz1_125_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨119, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 119 (by decide)))

theorem fz1_125_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨120, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 120 (by decide)))

theorem fz1_125_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨121, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 121 (by decide)))

theorem fz1_125_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨122, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 122 (by decide)))

theorem fz1_125_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨123, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 123 (by decide)))

theorem fz1_125_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨124, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 124 (by decide)))

theorem fz1_125_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨126, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 126 (by decide)))

theorem fz1_125_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨127, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 127 (by decide)))

theorem fz1_125_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨128, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 128 (by decide)))

theorem fz1_125_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨129, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 129 (by decide)))

theorem fz1_125_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨130, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 130 (by decide)))

theorem fz1_125_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨131, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 131 (by decide)))

theorem fz1_125_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨132, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 132 (by decide)))

theorem fz1_125_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨133, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 133 (by decide)))

theorem fz1_125_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨134, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 134 (by decide)))

theorem fz1_125_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨135, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 135 (by decide)))

theorem fz1_125_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨136, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 136 (by decide)))

theorem fz1_125_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨137, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 137 (by decide)))

theorem fz1_125_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨138, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 138 (by decide)))

theorem fz1_125_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨139, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 139 (by decide)))

theorem fz1_125_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨140, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 140 (by decide)))

theorem fz1_125_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨141, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 141 (by decide)))

theorem fz1_125_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨142, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 142 (by decide)))

theorem fz1_125_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨143, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 143 (by decide)))

theorem fz1_125_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨144, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 144 (by decide)))

theorem fz1_125_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨145, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 145 (by decide)))

theorem fz1_125_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK125)) = 0 :=
  repsFixedCard rK125 ⟨146, by decide⟩ R125 hpxR125 hcardq125
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_125) 146 (by decide)))

theorem fixz2_125 : ([1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 35, 36, 37, 38, 39, 41, 42, 44, 45, 46, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 97, 98, 99, 100, 101, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK125) (retConj 2 (Q2.R125_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_125_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨1, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 1 (by decide)))

theorem fz2_125_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨3, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 3 (by decide)))

theorem fz2_125_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨4, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 4 (by decide)))

theorem fz2_125_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨5, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 5 (by decide)))

theorem fz2_125_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨6, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 6 (by decide)))

theorem fz2_125_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨7, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 7 (by decide)))

theorem fz2_125_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨8, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 8 (by decide)))

theorem fz2_125_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨9, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 9 (by decide)))

theorem fz2_125_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨11, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 11 (by decide)))

theorem fz2_125_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨13, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 13 (by decide)))

theorem fz2_125_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨14, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 14 (by decide)))

theorem fz2_125_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨15, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 15 (by decide)))

theorem fz2_125_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨16, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 16 (by decide)))

theorem fz2_125_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨17, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 17 (by decide)))

theorem fz2_125_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨18, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 18 (by decide)))

theorem fz2_125_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨19, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 19 (by decide)))

theorem fz2_125_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨21, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 21 (by decide)))

theorem fz2_125_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨22, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 22 (by decide)))

theorem fz2_125_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨23, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 23 (by decide)))

theorem fz2_125_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨24, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 24 (by decide)))

theorem fz2_125_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨25, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 25 (by decide)))

theorem fz2_125_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨26, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 26 (by decide)))

theorem fz2_125_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨27, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 27 (by decide)))

theorem fz2_125_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨28, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 28 (by decide)))

theorem fz2_125_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨29, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 29 (by decide)))

theorem fz2_125_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨30, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 30 (by decide)))

theorem fz2_125_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨32, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 32 (by decide)))

theorem fz2_125_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨33, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 33 (by decide)))

theorem fz2_125_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨35, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 35 (by decide)))

theorem fz2_125_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨36, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 36 (by decide)))

theorem fz2_125_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨37, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 37 (by decide)))

theorem fz2_125_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨38, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 38 (by decide)))

theorem fz2_125_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨39, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 39 (by decide)))

theorem fz2_125_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨41, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 41 (by decide)))

theorem fz2_125_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨42, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 42 (by decide)))

theorem fz2_125_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨44, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 44 (by decide)))

theorem fz2_125_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨45, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 45 (by decide)))

theorem fz2_125_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨46, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 46 (by decide)))

theorem fz2_125_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨47, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 47 (by decide)))

theorem fz2_125_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨48, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 48 (by decide)))

theorem fz2_125_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨49, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 49 (by decide)))

theorem fz2_125_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨50, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 50 (by decide)))

theorem fz2_125_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨51, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 51 (by decide)))

theorem fz2_125_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨54, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 54 (by decide)))

theorem fz2_125_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨55, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 55 (by decide)))

theorem fz2_125_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨56, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 56 (by decide)))

theorem fz2_125_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨57, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 57 (by decide)))

theorem fz2_125_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨58, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 58 (by decide)))

theorem fz2_125_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨59, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 59 (by decide)))

theorem fz2_125_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨60, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 60 (by decide)))

theorem fz2_125_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨61, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 61 (by decide)))

theorem fz2_125_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨62, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 62 (by decide)))

theorem fz2_125_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨63, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 63 (by decide)))

theorem fz2_125_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨64, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 64 (by decide)))

theorem fz2_125_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨65, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 65 (by decide)))

theorem fz2_125_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨66, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 66 (by decide)))

theorem fz2_125_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨67, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 67 (by decide)))

theorem fz2_125_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨68, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 68 (by decide)))

theorem fz2_125_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨69, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 69 (by decide)))

theorem fz2_125_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨70, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 70 (by decide)))

theorem fz2_125_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨71, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 71 (by decide)))

theorem fz2_125_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨72, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 72 (by decide)))

theorem fz2_125_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨73, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 73 (by decide)))

theorem fz2_125_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨74, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 74 (by decide)))

theorem fz2_125_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨75, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 75 (by decide)))

theorem fz2_125_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨76, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 76 (by decide)))

theorem fz2_125_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨77, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 77 (by decide)))

theorem fz2_125_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨78, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 78 (by decide)))

theorem fz2_125_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨79, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 79 (by decide)))

theorem fz2_125_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨80, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 80 (by decide)))

theorem fz2_125_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨82, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 82 (by decide)))

theorem fz2_125_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨83, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 83 (by decide)))

theorem fz2_125_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨84, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 84 (by decide)))

theorem fz2_125_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨85, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 85 (by decide)))

theorem fz2_125_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨86, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 86 (by decide)))

theorem fz2_125_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨87, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 87 (by decide)))

theorem fz2_125_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨88, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 88 (by decide)))

theorem fz2_125_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨89, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 89 (by decide)))

theorem fz2_125_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨90, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 90 (by decide)))

theorem fz2_125_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨91, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 91 (by decide)))

theorem fz2_125_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨92, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 92 (by decide)))

theorem fz2_125_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨94, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 94 (by decide)))

theorem fz2_125_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨95, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 95 (by decide)))

theorem fz2_125_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨97, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 97 (by decide)))

theorem fz2_125_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨98, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 98 (by decide)))

theorem fz2_125_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨99, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 99 (by decide)))

theorem fz2_125_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨100, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 100 (by decide)))

theorem fz2_125_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨101, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 101 (by decide)))

theorem fz2_125_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨103, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 103 (by decide)))

theorem fz2_125_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨104, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 104 (by decide)))

theorem fz2_125_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨106, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 106 (by decide)))

theorem fz2_125_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨107, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 107 (by decide)))

theorem fz2_125_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨108, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 108 (by decide)))

theorem fz2_125_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨109, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 109 (by decide)))

theorem fz2_125_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨110, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 110 (by decide)))

theorem fz2_125_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨111, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 111 (by decide)))

theorem fz2_125_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨112, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 112 (by decide)))

theorem fz2_125_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨113, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 113 (by decide)))

theorem fz2_125_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨115, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 115 (by decide)))

theorem fz2_125_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨116, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 116 (by decide)))

theorem fz2_125_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨117, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 117 (by decide)))

theorem fz2_125_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨118, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 118 (by decide)))

theorem fz2_125_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨119, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 119 (by decide)))

theorem fz2_125_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨120, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 120 (by decide)))

theorem fz2_125_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨121, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 121 (by decide)))

theorem fz2_125_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨122, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 122 (by decide)))

theorem fz2_125_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨123, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 123 (by decide)))

theorem fz2_125_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨124, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 124 (by decide)))

theorem fz2_125_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨126, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 126 (by decide)))

theorem fz2_125_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨127, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 127 (by decide)))

theorem fz2_125_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨128, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 128 (by decide)))

theorem fz2_125_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨129, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 129 (by decide)))

theorem fz2_125_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨130, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 130 (by decide)))

theorem fz2_125_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨131, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 131 (by decide)))

theorem fz2_125_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨132, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 132 (by decide)))

theorem fz2_125_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨133, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 133 (by decide)))

theorem fz2_125_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨134, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 134 (by decide)))

theorem fz2_125_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨135, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 135 (by decide)))

theorem fz2_125_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨136, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 136 (by decide)))

theorem fz2_125_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨137, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 137 (by decide)))

theorem fz2_125_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨138, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 138 (by decide)))

theorem fz2_125_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨139, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 139 (by decide)))

theorem fz2_125_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨140, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 140 (by decide)))

theorem fz2_125_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨141, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 141 (by decide)))

theorem fz2_125_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨142, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 142 (by decide)))

theorem fz2_125_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨143, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 143 (by decide)))

theorem fz2_125_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨144, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 144 (by decide)))

theorem fz2_125_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨145, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 145 (by decide)))

theorem fz2_125_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK125)) = 0 :=
  Q2.repsFixedCard2 rK125 ⟨146, by decide⟩ Q2.R125_2 Q2.hpxR125_2 Q2.hcardq125_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_125) 146 (by decide)))

theorem fixz1_126 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 38, 40, 41, 42, 43, 44, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 97, 98, 100, 102, 103, 104, 105, 106, 108, 109, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK126) (retConj 1 (R126 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_126_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨1, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 1 (by decide)))

theorem fz1_126_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨2, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 2 (by decide)))

theorem fz1_126_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨4, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 4 (by decide)))

theorem fz1_126_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨5, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 5 (by decide)))

theorem fz1_126_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨6, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 6 (by decide)))

theorem fz1_126_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨7, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 7 (by decide)))

theorem fz1_126_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨8, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 8 (by decide)))

theorem fz1_126_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨9, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 9 (by decide)))

theorem fz1_126_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨11, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 11 (by decide)))

theorem fz1_126_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨13, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 13 (by decide)))

theorem fz1_126_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨14, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 14 (by decide)))

theorem fz1_126_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨15, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 15 (by decide)))

theorem fz1_126_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨16, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 16 (by decide)))

theorem fz1_126_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨17, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 17 (by decide)))

theorem fz1_126_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨18, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 18 (by decide)))

theorem fz1_126_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨19, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 19 (by decide)))

theorem fz1_126_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨20, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 20 (by decide)))

theorem fz1_126_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨22, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 22 (by decide)))

theorem fz1_126_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨23, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 23 (by decide)))

theorem fz1_126_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨24, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 24 (by decide)))

theorem fz1_126_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨25, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 25 (by decide)))

theorem fz1_126_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨26, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 26 (by decide)))

theorem fz1_126_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨27, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 27 (by decide)))

theorem fz1_126_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨28, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 28 (by decide)))

theorem fz1_126_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨29, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 29 (by decide)))

theorem fz1_126_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨30, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 30 (by decide)))

theorem fz1_126_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨32, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 32 (by decide)))

theorem fz1_126_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨33, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 33 (by decide)))

theorem fz1_126_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨34, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 34 (by decide)))

theorem fz1_126_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨35, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 35 (by decide)))

theorem fz1_126_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨36, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 36 (by decide)))

theorem fz1_126_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨38, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 38 (by decide)))

theorem fz1_126_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨40, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 40 (by decide)))

theorem fz1_126_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨41, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 41 (by decide)))

theorem fz1_126_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨42, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 42 (by decide)))

theorem fz1_126_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨43, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 43 (by decide)))

theorem fz1_126_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨44, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 44 (by decide)))

theorem fz1_126_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨46, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 46 (by decide)))

theorem fz1_126_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨47, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 47 (by decide)))

theorem fz1_126_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨49, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 49 (by decide)))

theorem fz1_126_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨50, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 50 (by decide)))

theorem fz1_126_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨51, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 51 (by decide)))

theorem fz1_126_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨52, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 52 (by decide)))

theorem fz1_126_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨54, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 54 (by decide)))

theorem fz1_126_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨55, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 55 (by decide)))

theorem fz1_126_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨56, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 56 (by decide)))

theorem fz1_126_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨57, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 57 (by decide)))

theorem fz1_126_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨58, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 58 (by decide)))

theorem fz1_126_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨59, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 59 (by decide)))

theorem fz1_126_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨60, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 60 (by decide)))

theorem fz1_126_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨61, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 61 (by decide)))

theorem fz1_126_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨62, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 62 (by decide)))

theorem fz1_126_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨63, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 63 (by decide)))

theorem fz1_126_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨64, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 64 (by decide)))

theorem fz1_126_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨65, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 65 (by decide)))

theorem fz1_126_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨66, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 66 (by decide)))

theorem fz1_126_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨67, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 67 (by decide)))

theorem fz1_126_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨68, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 68 (by decide)))

theorem fz1_126_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨69, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 69 (by decide)))

theorem fz1_126_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨70, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 70 (by decide)))

theorem fz1_126_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨71, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 71 (by decide)))

theorem fz1_126_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨72, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 72 (by decide)))

theorem fz1_126_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨73, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 73 (by decide)))

theorem fz1_126_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨74, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 74 (by decide)))

theorem fz1_126_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨75, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 75 (by decide)))

theorem fz1_126_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨76, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 76 (by decide)))

theorem fz1_126_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨77, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 77 (by decide)))

theorem fz1_126_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨78, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 78 (by decide)))

theorem fz1_126_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨79, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 79 (by decide)))

theorem fz1_126_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨80, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 80 (by decide)))

theorem fz1_126_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨81, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 81 (by decide)))

theorem fz1_126_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨83, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 83 (by decide)))

theorem fz1_126_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨84, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 84 (by decide)))

theorem fz1_126_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨85, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 85 (by decide)))

theorem fz1_126_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨86, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 86 (by decide)))

theorem fz1_126_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨87, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 87 (by decide)))

theorem fz1_126_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨88, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 88 (by decide)))

theorem fz1_126_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨89, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 89 (by decide)))

theorem fz1_126_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨90, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 90 (by decide)))

theorem fz1_126_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨91, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 91 (by decide)))

theorem fz1_126_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨92, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 92 (by decide)))

theorem fz1_126_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨94, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 94 (by decide)))

theorem fz1_126_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨95, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 95 (by decide)))

theorem fz1_126_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨96, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 96 (by decide)))

theorem fz1_126_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨97, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 97 (by decide)))

theorem fz1_126_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨98, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 98 (by decide)))

theorem fz1_126_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨100, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 100 (by decide)))

theorem fz1_126_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨102, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 102 (by decide)))

theorem fz1_126_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨103, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 103 (by decide)))

theorem fz1_126_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨104, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 104 (by decide)))

theorem fz1_126_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨105, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 105 (by decide)))

theorem fz1_126_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨106, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 106 (by decide)))

theorem fz1_126_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨108, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 108 (by decide)))

theorem fz1_126_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨109, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 109 (by decide)))

theorem fz1_126_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨111, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 111 (by decide)))

theorem fz1_126_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨112, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 112 (by decide)))

theorem fz1_126_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨113, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 113 (by decide)))

theorem fz1_126_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨114, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 114 (by decide)))

theorem fz1_126_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨115, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 115 (by decide)))

theorem fz1_126_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨116, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 116 (by decide)))

theorem fz1_126_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨117, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 117 (by decide)))

theorem fz1_126_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨118, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 118 (by decide)))

theorem fz1_126_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨119, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 119 (by decide)))

theorem fz1_126_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨120, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 120 (by decide)))

theorem fz1_126_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨121, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 121 (by decide)))

theorem fz1_126_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨122, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 122 (by decide)))

theorem fz1_126_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨123, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 123 (by decide)))

theorem fz1_126_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨124, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 124 (by decide)))

theorem fz1_126_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨125, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 125 (by decide)))

theorem fz1_126_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨127, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 127 (by decide)))

theorem fz1_126_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨128, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 128 (by decide)))

theorem fz1_126_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨129, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 129 (by decide)))

theorem fz1_126_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨130, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 130 (by decide)))

theorem fz1_126_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨131, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 131 (by decide)))

theorem fz1_126_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨132, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 132 (by decide)))

theorem fz1_126_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨133, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 133 (by decide)))

theorem fz1_126_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨134, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 134 (by decide)))

theorem fz1_126_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨135, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 135 (by decide)))

theorem fz1_126_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨136, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 136 (by decide)))

theorem fz1_126_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨137, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 137 (by decide)))

theorem fz1_126_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨138, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 138 (by decide)))

theorem fz1_126_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨139, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 139 (by decide)))

theorem fz1_126_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨140, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 140 (by decide)))

theorem fz1_126_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨141, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 141 (by decide)))

theorem fz1_126_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨142, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 142 (by decide)))

theorem fz1_126_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨143, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 143 (by decide)))

theorem fz1_126_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨144, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 144 (by decide)))

theorem fz1_126_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨145, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 145 (by decide)))

theorem fz1_126_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK126)) = 0 :=
  repsFixedCard rK126 ⟨146, by decide⟩ R126 hpxR126 hcardq126
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_126) 146 (by decide)))

theorem fixz2_126 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 38, 40, 41, 42, 43, 44, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 97, 98, 100, 102, 103, 104, 105, 106, 108, 109, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK126) (retConj 2 (Q2.R126_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_126_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨1, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 1 (by decide)))

theorem fz2_126_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨2, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 2 (by decide)))

theorem fz2_126_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨4, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 4 (by decide)))

theorem fz2_126_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨5, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 5 (by decide)))

theorem fz2_126_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨6, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 6 (by decide)))

theorem fz2_126_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨7, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 7 (by decide)))

theorem fz2_126_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨8, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 8 (by decide)))

theorem fz2_126_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨9, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 9 (by decide)))

theorem fz2_126_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨11, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 11 (by decide)))

theorem fz2_126_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨13, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 13 (by decide)))

theorem fz2_126_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨14, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 14 (by decide)))

theorem fz2_126_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨15, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 15 (by decide)))

theorem fz2_126_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨16, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 16 (by decide)))

theorem fz2_126_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨17, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 17 (by decide)))

theorem fz2_126_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨18, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 18 (by decide)))

theorem fz2_126_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨19, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 19 (by decide)))

theorem fz2_126_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨20, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 20 (by decide)))

theorem fz2_126_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨22, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 22 (by decide)))

theorem fz2_126_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨23, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 23 (by decide)))

theorem fz2_126_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨24, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 24 (by decide)))

theorem fz2_126_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨25, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 25 (by decide)))

theorem fz2_126_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨26, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 26 (by decide)))

theorem fz2_126_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨27, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 27 (by decide)))

theorem fz2_126_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨28, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 28 (by decide)))

theorem fz2_126_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨29, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 29 (by decide)))

theorem fz2_126_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨30, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 30 (by decide)))

theorem fz2_126_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨32, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 32 (by decide)))

theorem fz2_126_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨33, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 33 (by decide)))

theorem fz2_126_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨34, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 34 (by decide)))

theorem fz2_126_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨35, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 35 (by decide)))

theorem fz2_126_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨36, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 36 (by decide)))

theorem fz2_126_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨38, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 38 (by decide)))

theorem fz2_126_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨40, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 40 (by decide)))

theorem fz2_126_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨41, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 41 (by decide)))

theorem fz2_126_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨42, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 42 (by decide)))

theorem fz2_126_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨43, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 43 (by decide)))

theorem fz2_126_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨44, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 44 (by decide)))

theorem fz2_126_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨46, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 46 (by decide)))

theorem fz2_126_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨47, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 47 (by decide)))

theorem fz2_126_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨49, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 49 (by decide)))

theorem fz2_126_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨50, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 50 (by decide)))

theorem fz2_126_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨51, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 51 (by decide)))

theorem fz2_126_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨52, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 52 (by decide)))

theorem fz2_126_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨54, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 54 (by decide)))

theorem fz2_126_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨55, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 55 (by decide)))

theorem fz2_126_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨56, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 56 (by decide)))

theorem fz2_126_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨57, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 57 (by decide)))

theorem fz2_126_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨58, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 58 (by decide)))

theorem fz2_126_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨59, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 59 (by decide)))

theorem fz2_126_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨60, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 60 (by decide)))

theorem fz2_126_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨61, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 61 (by decide)))

theorem fz2_126_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨62, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 62 (by decide)))

theorem fz2_126_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨63, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 63 (by decide)))

theorem fz2_126_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨64, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 64 (by decide)))

theorem fz2_126_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨65, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 65 (by decide)))

theorem fz2_126_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨66, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 66 (by decide)))

theorem fz2_126_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨67, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 67 (by decide)))

theorem fz2_126_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨68, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 68 (by decide)))

theorem fz2_126_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨69, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 69 (by decide)))

theorem fz2_126_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨70, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 70 (by decide)))

theorem fz2_126_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨71, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 71 (by decide)))

theorem fz2_126_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨72, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 72 (by decide)))

theorem fz2_126_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨73, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 73 (by decide)))

theorem fz2_126_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨74, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 74 (by decide)))

theorem fz2_126_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨75, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 75 (by decide)))

theorem fz2_126_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨76, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 76 (by decide)))

theorem fz2_126_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨77, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 77 (by decide)))

theorem fz2_126_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨78, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 78 (by decide)))

theorem fz2_126_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨79, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 79 (by decide)))

theorem fz2_126_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨80, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 80 (by decide)))

theorem fz2_126_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨81, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 81 (by decide)))

theorem fz2_126_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨83, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 83 (by decide)))

theorem fz2_126_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨84, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 84 (by decide)))

theorem fz2_126_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨85, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 85 (by decide)))

theorem fz2_126_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨86, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 86 (by decide)))

theorem fz2_126_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨87, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 87 (by decide)))

theorem fz2_126_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨88, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 88 (by decide)))

theorem fz2_126_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨89, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 89 (by decide)))

theorem fz2_126_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨90, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 90 (by decide)))

theorem fz2_126_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨91, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 91 (by decide)))

theorem fz2_126_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨92, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 92 (by decide)))

theorem fz2_126_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨94, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 94 (by decide)))

theorem fz2_126_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨95, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 95 (by decide)))

theorem fz2_126_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨96, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 96 (by decide)))

theorem fz2_126_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨97, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 97 (by decide)))

theorem fz2_126_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨98, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 98 (by decide)))

theorem fz2_126_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨100, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 100 (by decide)))

theorem fz2_126_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨102, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 102 (by decide)))

theorem fz2_126_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨103, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 103 (by decide)))

theorem fz2_126_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨104, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 104 (by decide)))

theorem fz2_126_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨105, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 105 (by decide)))

theorem fz2_126_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨106, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 106 (by decide)))

theorem fz2_126_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨108, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 108 (by decide)))

theorem fz2_126_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨109, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 109 (by decide)))

theorem fz2_126_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨111, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 111 (by decide)))

theorem fz2_126_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨112, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 112 (by decide)))

theorem fz2_126_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨113, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 113 (by decide)))

theorem fz2_126_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨114, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 114 (by decide)))

theorem fz2_126_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨115, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 115 (by decide)))

theorem fz2_126_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨116, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 116 (by decide)))

theorem fz2_126_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨117, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 117 (by decide)))

theorem fz2_126_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨118, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 118 (by decide)))

theorem fz2_126_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨119, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 119 (by decide)))

theorem fz2_126_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨120, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 120 (by decide)))

theorem fz2_126_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨121, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 121 (by decide)))

theorem fz2_126_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨122, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 122 (by decide)))

theorem fz2_126_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨123, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 123 (by decide)))

theorem fz2_126_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨124, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 124 (by decide)))

theorem fz2_126_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨125, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 125 (by decide)))

theorem fz2_126_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨127, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 127 (by decide)))

theorem fz2_126_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨128, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 128 (by decide)))

theorem fz2_126_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨129, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 129 (by decide)))

theorem fz2_126_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨130, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 130 (by decide)))

theorem fz2_126_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨131, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 131 (by decide)))

theorem fz2_126_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨132, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 132 (by decide)))

theorem fz2_126_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨133, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 133 (by decide)))

theorem fz2_126_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨134, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 134 (by decide)))

theorem fz2_126_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨135, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 135 (by decide)))

theorem fz2_126_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨136, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 136 (by decide)))

theorem fz2_126_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨137, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 137 (by decide)))

theorem fz2_126_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨138, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 138 (by decide)))

theorem fz2_126_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨139, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 139 (by decide)))

theorem fz2_126_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨140, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 140 (by decide)))

theorem fz2_126_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨141, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 141 (by decide)))

theorem fz2_126_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨142, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 142 (by decide)))

theorem fz2_126_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨143, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 143 (by decide)))

theorem fz2_126_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨144, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 144 (by decide)))

theorem fz2_126_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨145, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 145 (by decide)))

theorem fz2_126_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK126)) = 0 :=
  Q2.repsFixedCard2 rK126 ⟨146, by decide⟩ Q2.R126_2 Q2.hpxR126_2 Q2.hcardq126_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_126) 146 (by decide)))

theorem fixz1_127 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 47, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 96, 97, 98, 99, 100, 101, 103, 104, 105, 106, 107, 109, 110, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK127) (retConj 1 (R127 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_127_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨1, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 1 (by decide)))

theorem fz1_127_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨2, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 2 (by decide)))

theorem fz1_127_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨4, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 4 (by decide)))

theorem fz1_127_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨5, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 5 (by decide)))

theorem fz1_127_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨6, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 6 (by decide)))

theorem fz1_127_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨7, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 7 (by decide)))

theorem fz1_127_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨8, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 8 (by decide)))

theorem fz1_127_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨9, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 9 (by decide)))

theorem fz1_127_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨11, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 11 (by decide)))

theorem fz1_127_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨13, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 13 (by decide)))

theorem fz1_127_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨14, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 14 (by decide)))

theorem fz1_127_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨15, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 15 (by decide)))

theorem fz1_127_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨16, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 16 (by decide)))

theorem fz1_127_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨17, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 17 (by decide)))

theorem fz1_127_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨18, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 18 (by decide)))

theorem fz1_127_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨19, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 19 (by decide)))

theorem fz1_127_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨20, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 20 (by decide)))

theorem fz1_127_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨22, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 22 (by decide)))

theorem fz1_127_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨23, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 23 (by decide)))

theorem fz1_127_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨24, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 24 (by decide)))

theorem fz1_127_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨25, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 25 (by decide)))

theorem fz1_127_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨26, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 26 (by decide)))

theorem fz1_127_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨27, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 27 (by decide)))

theorem fz1_127_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨28, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 28 (by decide)))

theorem fz1_127_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨29, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 29 (by decide)))

theorem fz1_127_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨30, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 30 (by decide)))

theorem fz1_127_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨31, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 31 (by decide)))

theorem fz1_127_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨34, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 34 (by decide)))

theorem fz1_127_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨35, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 35 (by decide)))

theorem fz1_127_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨36, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 36 (by decide)))

theorem fz1_127_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨37, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 37 (by decide)))

theorem fz1_127_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨38, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 38 (by decide)))

theorem fz1_127_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨39, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 39 (by decide)))

theorem fz1_127_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨41, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 41 (by decide)))

theorem fz1_127_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨42, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 42 (by decide)))

theorem fz1_127_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨43, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 43 (by decide)))

theorem fz1_127_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨44, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 44 (by decide)))

theorem fz1_127_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨45, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 45 (by decide)))

theorem fz1_127_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨47, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 47 (by decide)))

theorem fz1_127_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨48, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 48 (by decide)))

theorem fz1_127_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨50, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 50 (by decide)))

theorem fz1_127_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨51, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 51 (by decide)))

theorem fz1_127_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨52, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 52 (by decide)))

theorem fz1_127_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨54, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 54 (by decide)))

theorem fz1_127_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨55, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 55 (by decide)))

theorem fz1_127_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨56, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 56 (by decide)))

theorem fz1_127_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨57, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 57 (by decide)))

theorem fz1_127_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨58, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 58 (by decide)))

theorem fz1_127_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨59, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 59 (by decide)))

theorem fz1_127_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨60, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 60 (by decide)))

theorem fz1_127_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨61, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 61 (by decide)))

theorem fz1_127_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨62, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 62 (by decide)))

theorem fz1_127_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨63, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 63 (by decide)))

theorem fz1_127_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨64, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 64 (by decide)))

theorem fz1_127_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨65, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 65 (by decide)))

theorem fz1_127_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨66, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 66 (by decide)))

theorem fz1_127_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨67, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 67 (by decide)))

theorem fz1_127_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨68, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 68 (by decide)))

theorem fz1_127_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨69, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 69 (by decide)))

theorem fz1_127_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨70, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 70 (by decide)))

theorem fz1_127_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨71, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 71 (by decide)))

theorem fz1_127_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨72, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 72 (by decide)))

theorem fz1_127_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨73, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 73 (by decide)))

theorem fz1_127_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨74, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 74 (by decide)))

theorem fz1_127_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨75, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 75 (by decide)))

theorem fz1_127_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨76, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 76 (by decide)))

theorem fz1_127_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨77, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 77 (by decide)))

theorem fz1_127_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨78, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 78 (by decide)))

theorem fz1_127_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨79, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 79 (by decide)))

theorem fz1_127_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨80, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 80 (by decide)))

theorem fz1_127_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨81, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 81 (by decide)))

theorem fz1_127_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨83, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 83 (by decide)))

theorem fz1_127_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨84, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 84 (by decide)))

theorem fz1_127_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨85, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 85 (by decide)))

theorem fz1_127_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨86, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 86 (by decide)))

theorem fz1_127_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨87, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 87 (by decide)))

theorem fz1_127_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨88, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 88 (by decide)))

theorem fz1_127_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨89, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 89 (by decide)))

theorem fz1_127_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨90, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 90 (by decide)))

theorem fz1_127_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨91, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 91 (by decide)))

theorem fz1_127_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨92, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 92 (by decide)))

theorem fz1_127_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨93, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 93 (by decide)))

theorem fz1_127_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨96, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 96 (by decide)))

theorem fz1_127_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨97, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 97 (by decide)))

theorem fz1_127_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨98, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 98 (by decide)))

theorem fz1_127_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨99, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 99 (by decide)))

theorem fz1_127_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨100, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 100 (by decide)))

theorem fz1_127_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨101, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 101 (by decide)))

theorem fz1_127_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨103, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 103 (by decide)))

theorem fz1_127_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨104, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 104 (by decide)))

theorem fz1_127_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨105, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 105 (by decide)))

theorem fz1_127_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨106, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 106 (by decide)))

theorem fz1_127_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨107, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 107 (by decide)))

theorem fz1_127_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨109, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 109 (by decide)))

theorem fz1_127_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨110, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 110 (by decide)))

theorem fz1_127_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨112, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 112 (by decide)))

theorem fz1_127_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨113, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 113 (by decide)))

theorem fz1_127_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨114, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 114 (by decide)))

theorem fz1_127_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨115, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 115 (by decide)))

theorem fz1_127_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨116, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 116 (by decide)))

theorem fz1_127_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨117, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 117 (by decide)))

theorem fz1_127_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨118, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 118 (by decide)))

theorem fz1_127_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨119, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 119 (by decide)))

theorem fz1_127_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨120, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 120 (by decide)))

theorem fz1_127_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨121, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 121 (by decide)))

theorem fz1_127_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨122, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 122 (by decide)))

theorem fz1_127_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨123, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 123 (by decide)))

theorem fz1_127_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨124, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 124 (by decide)))

theorem fz1_127_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨125, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 125 (by decide)))

theorem fz1_127_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨126, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 126 (by decide)))

theorem fz1_127_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨128, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 128 (by decide)))

theorem fz1_127_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨129, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 129 (by decide)))

theorem fz1_127_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨130, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 130 (by decide)))

theorem fz1_127_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨131, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 131 (by decide)))

theorem fz1_127_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨132, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 132 (by decide)))

theorem fz1_127_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨133, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 133 (by decide)))

theorem fz1_127_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨134, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 134 (by decide)))

theorem fz1_127_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨135, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 135 (by decide)))

theorem fz1_127_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨136, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 136 (by decide)))

theorem fz1_127_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨137, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 137 (by decide)))

theorem fz1_127_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨138, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 138 (by decide)))

theorem fz1_127_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨139, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 139 (by decide)))

theorem fz1_127_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨140, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 140 (by decide)))

theorem fz1_127_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨141, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 141 (by decide)))

theorem fz1_127_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨142, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 142 (by decide)))

theorem fz1_127_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨143, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 143 (by decide)))

theorem fz1_127_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨144, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 144 (by decide)))

theorem fz1_127_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨145, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 145 (by decide)))

theorem fz1_127_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK127)) = 0 :=
  repsFixedCard rK127 ⟨146, by decide⟩ R127 hpxR127 hcardq127
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_127) 146 (by decide)))

theorem fixz2_127 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 47, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 96, 97, 98, 99, 100, 101, 103, 104, 105, 106, 107, 109, 110, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK127) (retConj 2 (Q2.R127_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_127_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨1, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 1 (by decide)))

theorem fz2_127_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨2, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 2 (by decide)))

theorem fz2_127_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨4, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 4 (by decide)))

theorem fz2_127_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨5, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 5 (by decide)))

theorem fz2_127_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨6, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 6 (by decide)))

theorem fz2_127_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨7, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 7 (by decide)))

theorem fz2_127_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨8, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 8 (by decide)))

theorem fz2_127_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨9, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 9 (by decide)))

theorem fz2_127_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨11, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 11 (by decide)))

theorem fz2_127_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨13, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 13 (by decide)))

theorem fz2_127_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨14, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 14 (by decide)))

theorem fz2_127_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨15, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 15 (by decide)))

theorem fz2_127_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨16, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 16 (by decide)))

theorem fz2_127_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨17, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 17 (by decide)))

theorem fz2_127_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨18, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 18 (by decide)))

theorem fz2_127_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨19, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 19 (by decide)))

theorem fz2_127_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨20, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 20 (by decide)))

theorem fz2_127_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨22, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 22 (by decide)))

theorem fz2_127_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨23, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 23 (by decide)))

theorem fz2_127_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨24, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 24 (by decide)))

theorem fz2_127_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨25, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 25 (by decide)))

theorem fz2_127_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨26, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 26 (by decide)))

theorem fz2_127_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨27, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 27 (by decide)))

theorem fz2_127_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨28, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 28 (by decide)))

theorem fz2_127_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨29, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 29 (by decide)))

theorem fz2_127_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨30, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 30 (by decide)))

theorem fz2_127_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨31, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 31 (by decide)))

theorem fz2_127_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨34, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 34 (by decide)))

theorem fz2_127_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨35, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 35 (by decide)))

theorem fz2_127_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨36, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 36 (by decide)))

theorem fz2_127_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨37, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 37 (by decide)))

theorem fz2_127_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨38, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 38 (by decide)))

theorem fz2_127_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨39, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 39 (by decide)))

theorem fz2_127_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨41, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 41 (by decide)))

theorem fz2_127_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨42, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 42 (by decide)))

theorem fz2_127_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨43, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 43 (by decide)))

theorem fz2_127_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨44, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 44 (by decide)))

theorem fz2_127_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨45, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 45 (by decide)))

theorem fz2_127_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨47, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 47 (by decide)))

theorem fz2_127_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨48, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 48 (by decide)))

theorem fz2_127_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨50, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 50 (by decide)))

theorem fz2_127_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨51, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 51 (by decide)))

theorem fz2_127_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨52, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 52 (by decide)))

theorem fz2_127_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨54, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 54 (by decide)))

theorem fz2_127_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨55, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 55 (by decide)))

theorem fz2_127_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨56, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 56 (by decide)))

theorem fz2_127_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨57, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 57 (by decide)))

theorem fz2_127_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨58, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 58 (by decide)))

theorem fz2_127_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨59, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 59 (by decide)))

theorem fz2_127_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨60, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 60 (by decide)))

theorem fz2_127_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨61, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 61 (by decide)))

theorem fz2_127_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨62, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 62 (by decide)))

theorem fz2_127_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨63, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 63 (by decide)))

theorem fz2_127_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨64, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 64 (by decide)))

theorem fz2_127_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨65, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 65 (by decide)))

theorem fz2_127_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨66, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 66 (by decide)))

theorem fz2_127_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨67, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 67 (by decide)))

theorem fz2_127_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨68, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 68 (by decide)))

theorem fz2_127_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨69, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 69 (by decide)))

theorem fz2_127_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨70, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 70 (by decide)))

theorem fz2_127_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨71, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 71 (by decide)))

theorem fz2_127_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨72, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 72 (by decide)))

theorem fz2_127_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨73, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 73 (by decide)))

theorem fz2_127_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨74, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 74 (by decide)))

theorem fz2_127_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨75, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 75 (by decide)))

theorem fz2_127_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨76, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 76 (by decide)))

theorem fz2_127_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨77, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 77 (by decide)))

theorem fz2_127_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨78, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 78 (by decide)))

theorem fz2_127_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨79, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 79 (by decide)))

theorem fz2_127_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨80, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 80 (by decide)))

theorem fz2_127_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨81, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 81 (by decide)))

theorem fz2_127_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨83, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 83 (by decide)))

theorem fz2_127_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨84, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 84 (by decide)))

theorem fz2_127_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨85, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 85 (by decide)))

theorem fz2_127_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨86, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 86 (by decide)))

theorem fz2_127_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨87, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 87 (by decide)))

theorem fz2_127_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨88, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 88 (by decide)))

theorem fz2_127_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨89, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 89 (by decide)))

theorem fz2_127_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨90, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 90 (by decide)))

theorem fz2_127_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨91, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 91 (by decide)))

theorem fz2_127_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨92, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 92 (by decide)))

theorem fz2_127_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨93, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 93 (by decide)))

theorem fz2_127_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨96, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 96 (by decide)))

theorem fz2_127_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨97, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 97 (by decide)))

theorem fz2_127_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨98, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 98 (by decide)))

theorem fz2_127_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨99, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 99 (by decide)))

theorem fz2_127_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨100, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 100 (by decide)))

theorem fz2_127_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨101, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 101 (by decide)))

theorem fz2_127_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨103, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 103 (by decide)))

theorem fz2_127_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨104, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 104 (by decide)))

theorem fz2_127_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨105, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 105 (by decide)))

theorem fz2_127_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨106, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 106 (by decide)))

theorem fz2_127_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨107, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 107 (by decide)))

theorem fz2_127_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨109, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 109 (by decide)))

theorem fz2_127_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨110, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 110 (by decide)))

theorem fz2_127_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨112, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 112 (by decide)))

theorem fz2_127_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨113, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 113 (by decide)))

theorem fz2_127_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨114, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 114 (by decide)))

theorem fz2_127_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨115, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 115 (by decide)))

theorem fz2_127_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨116, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 116 (by decide)))

theorem fz2_127_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨117, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 117 (by decide)))

theorem fz2_127_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨118, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 118 (by decide)))

theorem fz2_127_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨119, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 119 (by decide)))

theorem fz2_127_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨120, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 120 (by decide)))

theorem fz2_127_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨121, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 121 (by decide)))

theorem fz2_127_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨122, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 122 (by decide)))

theorem fz2_127_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨123, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 123 (by decide)))

theorem fz2_127_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨124, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 124 (by decide)))

theorem fz2_127_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨125, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 125 (by decide)))

theorem fz2_127_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨126, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 126 (by decide)))

theorem fz2_127_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨128, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 128 (by decide)))

theorem fz2_127_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨129, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 129 (by decide)))

theorem fz2_127_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨130, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 130 (by decide)))

theorem fz2_127_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨131, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 131 (by decide)))

theorem fz2_127_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨132, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 132 (by decide)))

theorem fz2_127_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨133, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 133 (by decide)))

theorem fz2_127_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨134, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 134 (by decide)))

theorem fz2_127_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨135, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 135 (by decide)))

theorem fz2_127_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨136, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 136 (by decide)))

theorem fz2_127_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨137, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 137 (by decide)))

theorem fz2_127_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨138, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 138 (by decide)))

theorem fz2_127_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨139, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 139 (by decide)))

theorem fz2_127_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨140, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 140 (by decide)))

theorem fz2_127_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨141, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 141 (by decide)))

theorem fz2_127_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨142, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 142 (by decide)))

theorem fz2_127_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨143, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 143 (by decide)))

theorem fz2_127_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨144, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 144 (by decide)))

theorem fz2_127_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨145, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 145 (by decide)))

theorem fz2_127_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK127)) = 0 :=
  Q2.repsFixedCard2 rK127 ⟨146, by decide⟩ Q2.R127_2 Q2.hpxR127_2 Q2.hcardq127_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_127) 146 (by decide)))

theorem fixz1_128 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 91, 92, 93, 94, 95, 97, 98, 99, 100, 101, 102, 104, 105, 106, 107, 108, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK128) (retConj 1 (R128 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_128_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨1, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 1 (by decide)))

theorem fz1_128_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨2, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 2 (by decide)))

theorem fz1_128_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨4, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 4 (by decide)))

theorem fz1_128_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨5, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 5 (by decide)))

theorem fz1_128_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨6, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 6 (by decide)))

theorem fz1_128_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨7, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 7 (by decide)))

theorem fz1_128_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨8, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 8 (by decide)))

theorem fz1_128_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨9, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 9 (by decide)))

theorem fz1_128_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨11, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 11 (by decide)))

theorem fz1_128_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨13, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 13 (by decide)))

theorem fz1_128_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨14, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 14 (by decide)))

theorem fz1_128_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨15, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 15 (by decide)))

theorem fz1_128_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨16, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 16 (by decide)))

theorem fz1_128_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨17, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 17 (by decide)))

theorem fz1_128_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨18, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 18 (by decide)))

theorem fz1_128_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨19, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 19 (by decide)))

theorem fz1_128_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨20, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 20 (by decide)))

theorem fz1_128_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨22, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 22 (by decide)))

theorem fz1_128_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨23, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 23 (by decide)))

theorem fz1_128_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨24, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 24 (by decide)))

theorem fz1_128_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨25, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 25 (by decide)))

theorem fz1_128_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨26, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 26 (by decide)))

theorem fz1_128_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨27, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 27 (by decide)))

theorem fz1_128_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨29, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 29 (by decide)))

theorem fz1_128_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨30, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 30 (by decide)))

theorem fz1_128_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨31, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 31 (by decide)))

theorem fz1_128_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨32, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 32 (by decide)))

theorem fz1_128_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨33, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 33 (by decide)))

theorem fz1_128_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨35, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 35 (by decide)))

theorem fz1_128_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨36, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 36 (by decide)))

theorem fz1_128_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨37, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 37 (by decide)))

theorem fz1_128_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨38, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 38 (by decide)))

theorem fz1_128_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨39, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 39 (by decide)))

theorem fz1_128_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨40, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 40 (by decide)))

theorem fz1_128_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨42, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 42 (by decide)))

theorem fz1_128_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨43, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 43 (by decide)))

theorem fz1_128_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨44, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 44 (by decide)))

theorem fz1_128_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨45, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 45 (by decide)))

theorem fz1_128_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨46, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 46 (by decide)))

theorem fz1_128_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨48, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 48 (by decide)))

theorem fz1_128_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨49, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 49 (by decide)))

theorem fz1_128_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨51, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 51 (by decide)))

theorem fz1_128_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨52, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 52 (by decide)))

theorem fz1_128_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨54, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 54 (by decide)))

theorem fz1_128_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨55, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 55 (by decide)))

theorem fz1_128_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨56, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 56 (by decide)))

theorem fz1_128_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨57, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 57 (by decide)))

theorem fz1_128_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨58, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 58 (by decide)))

theorem fz1_128_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨59, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 59 (by decide)))

theorem fz1_128_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨60, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 60 (by decide)))

theorem fz1_128_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨61, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 61 (by decide)))

theorem fz1_128_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨62, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 62 (by decide)))

theorem fz1_128_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨63, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 63 (by decide)))

theorem fz1_128_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨64, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 64 (by decide)))

theorem fz1_128_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨65, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 65 (by decide)))

theorem fz1_128_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨66, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 66 (by decide)))

theorem fz1_128_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨67, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 67 (by decide)))

theorem fz1_128_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨68, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 68 (by decide)))

theorem fz1_128_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨69, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 69 (by decide)))

theorem fz1_128_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨70, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 70 (by decide)))

theorem fz1_128_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨71, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 71 (by decide)))

theorem fz1_128_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨72, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 72 (by decide)))

theorem fz1_128_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨73, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 73 (by decide)))

theorem fz1_128_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨74, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 74 (by decide)))

theorem fz1_128_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨75, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 75 (by decide)))

theorem fz1_128_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨76, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 76 (by decide)))

theorem fz1_128_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨77, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 77 (by decide)))

theorem fz1_128_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨78, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 78 (by decide)))

theorem fz1_128_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨79, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 79 (by decide)))

theorem fz1_128_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨80, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 80 (by decide)))

theorem fz1_128_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨81, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 81 (by decide)))

theorem fz1_128_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨83, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 83 (by decide)))

theorem fz1_128_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨84, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 84 (by decide)))

theorem fz1_128_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨85, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 85 (by decide)))

theorem fz1_128_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨86, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 86 (by decide)))

theorem fz1_128_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨87, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 87 (by decide)))

theorem fz1_128_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨88, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 88 (by decide)))

theorem fz1_128_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨89, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 89 (by decide)))

theorem fz1_128_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨91, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 91 (by decide)))

theorem fz1_128_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨92, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 92 (by decide)))

theorem fz1_128_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨93, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 93 (by decide)))

theorem fz1_128_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨94, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 94 (by decide)))

theorem fz1_128_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨95, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 95 (by decide)))

theorem fz1_128_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨97, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 97 (by decide)))

theorem fz1_128_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨98, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 98 (by decide)))

theorem fz1_128_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨99, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 99 (by decide)))

theorem fz1_128_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨100, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 100 (by decide)))

theorem fz1_128_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨101, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 101 (by decide)))

theorem fz1_128_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨102, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 102 (by decide)))

theorem fz1_128_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨104, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 104 (by decide)))

theorem fz1_128_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨105, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 105 (by decide)))

theorem fz1_128_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨106, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 106 (by decide)))

theorem fz1_128_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨107, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 107 (by decide)))

theorem fz1_128_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨108, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 108 (by decide)))

theorem fz1_128_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨110, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 110 (by decide)))

theorem fz1_128_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨111, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 111 (by decide)))

theorem fz1_128_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨113, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 113 (by decide)))

theorem fz1_128_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨114, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 114 (by decide)))

theorem fz1_128_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨115, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 115 (by decide)))

theorem fz1_128_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨116, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 116 (by decide)))

theorem fz1_128_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨117, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 117 (by decide)))

theorem fz1_128_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨118, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 118 (by decide)))

theorem fz1_128_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨119, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 119 (by decide)))

theorem fz1_128_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨120, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 120 (by decide)))

theorem fz1_128_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨121, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 121 (by decide)))

theorem fz1_128_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨122, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 122 (by decide)))

theorem fz1_128_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨123, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 123 (by decide)))

theorem fz1_128_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨124, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 124 (by decide)))

theorem fz1_128_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨125, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 125 (by decide)))

theorem fz1_128_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨126, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 126 (by decide)))

theorem fz1_128_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨127, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 127 (by decide)))

theorem fz1_128_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨129, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 129 (by decide)))

theorem fz1_128_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨130, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 130 (by decide)))

theorem fz1_128_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨131, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 131 (by decide)))

theorem fz1_128_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨132, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 132 (by decide)))

theorem fz1_128_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨133, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 133 (by decide)))

theorem fz1_128_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨134, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 134 (by decide)))

theorem fz1_128_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨135, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 135 (by decide)))

theorem fz1_128_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨136, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 136 (by decide)))

theorem fz1_128_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨137, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 137 (by decide)))

theorem fz1_128_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨138, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 138 (by decide)))

theorem fz1_128_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨139, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 139 (by decide)))

theorem fz1_128_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨140, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 140 (by decide)))

theorem fz1_128_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨141, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 141 (by decide)))

theorem fz1_128_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨142, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 142 (by decide)))

theorem fz1_128_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨143, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 143 (by decide)))

theorem fz1_128_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨144, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 144 (by decide)))

theorem fz1_128_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨145, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 145 (by decide)))

theorem fz1_128_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK128)) = 0 :=
  repsFixedCard rK128 ⟨146, by decide⟩ R128 hpxR128 hcardq128
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_128) 146 (by decide)))

theorem fixz2_128 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 91, 92, 93, 94, 95, 97, 98, 99, 100, 101, 102, 104, 105, 106, 107, 108, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK128) (retConj 2 (Q2.R128_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_128_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨1, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 1 (by decide)))

theorem fz2_128_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨2, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 2 (by decide)))

theorem fz2_128_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨4, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 4 (by decide)))

theorem fz2_128_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨5, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 5 (by decide)))

theorem fz2_128_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨6, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 6 (by decide)))

theorem fz2_128_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨7, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 7 (by decide)))

theorem fz2_128_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨8, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 8 (by decide)))

theorem fz2_128_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨9, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 9 (by decide)))

theorem fz2_128_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨11, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 11 (by decide)))

theorem fz2_128_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨13, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 13 (by decide)))

theorem fz2_128_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨14, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 14 (by decide)))

theorem fz2_128_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨15, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 15 (by decide)))

theorem fz2_128_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨16, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 16 (by decide)))

theorem fz2_128_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨17, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 17 (by decide)))

theorem fz2_128_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨18, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 18 (by decide)))

theorem fz2_128_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨19, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 19 (by decide)))

theorem fz2_128_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨20, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 20 (by decide)))

theorem fz2_128_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨22, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 22 (by decide)))

theorem fz2_128_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨23, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 23 (by decide)))

theorem fz2_128_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨24, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 24 (by decide)))

theorem fz2_128_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨25, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 25 (by decide)))

theorem fz2_128_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨26, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 26 (by decide)))

theorem fz2_128_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨27, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 27 (by decide)))

theorem fz2_128_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨29, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 29 (by decide)))

theorem fz2_128_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨30, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 30 (by decide)))

theorem fz2_128_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨31, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 31 (by decide)))

theorem fz2_128_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨32, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 32 (by decide)))

theorem fz2_128_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨33, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 33 (by decide)))

theorem fz2_128_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨35, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 35 (by decide)))

theorem fz2_128_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨36, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 36 (by decide)))

theorem fz2_128_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨37, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 37 (by decide)))

theorem fz2_128_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨38, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 38 (by decide)))

theorem fz2_128_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨39, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 39 (by decide)))

theorem fz2_128_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨40, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 40 (by decide)))

theorem fz2_128_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨42, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 42 (by decide)))

theorem fz2_128_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨43, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 43 (by decide)))

theorem fz2_128_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨44, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 44 (by decide)))

theorem fz2_128_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨45, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 45 (by decide)))

theorem fz2_128_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨46, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 46 (by decide)))

theorem fz2_128_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨48, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 48 (by decide)))

theorem fz2_128_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨49, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 49 (by decide)))

theorem fz2_128_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨51, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 51 (by decide)))

theorem fz2_128_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨52, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 52 (by decide)))

theorem fz2_128_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨54, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 54 (by decide)))

theorem fz2_128_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨55, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 55 (by decide)))

theorem fz2_128_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨56, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 56 (by decide)))

theorem fz2_128_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨57, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 57 (by decide)))

theorem fz2_128_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨58, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 58 (by decide)))

theorem fz2_128_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨59, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 59 (by decide)))

theorem fz2_128_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨60, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 60 (by decide)))

theorem fz2_128_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨61, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 61 (by decide)))

theorem fz2_128_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨62, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 62 (by decide)))

theorem fz2_128_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨63, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 63 (by decide)))

theorem fz2_128_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨64, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 64 (by decide)))

theorem fz2_128_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨65, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 65 (by decide)))

theorem fz2_128_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨66, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 66 (by decide)))

theorem fz2_128_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨67, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 67 (by decide)))

theorem fz2_128_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨68, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 68 (by decide)))

theorem fz2_128_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨69, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 69 (by decide)))

theorem fz2_128_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨70, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 70 (by decide)))

theorem fz2_128_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨71, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 71 (by decide)))

theorem fz2_128_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨72, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 72 (by decide)))

theorem fz2_128_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨73, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 73 (by decide)))

theorem fz2_128_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨74, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 74 (by decide)))

theorem fz2_128_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨75, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 75 (by decide)))

theorem fz2_128_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨76, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 76 (by decide)))

theorem fz2_128_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨77, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 77 (by decide)))

theorem fz2_128_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨78, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 78 (by decide)))

theorem fz2_128_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨79, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 79 (by decide)))

theorem fz2_128_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨80, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 80 (by decide)))

theorem fz2_128_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨81, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 81 (by decide)))

theorem fz2_128_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨83, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 83 (by decide)))

theorem fz2_128_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨84, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 84 (by decide)))

theorem fz2_128_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨85, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 85 (by decide)))

theorem fz2_128_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨86, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 86 (by decide)))

theorem fz2_128_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨87, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 87 (by decide)))

theorem fz2_128_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨88, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 88 (by decide)))

theorem fz2_128_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨89, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 89 (by decide)))

theorem fz2_128_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨91, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 91 (by decide)))

theorem fz2_128_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨92, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 92 (by decide)))

theorem fz2_128_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨93, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 93 (by decide)))

theorem fz2_128_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨94, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 94 (by decide)))

theorem fz2_128_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨95, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 95 (by decide)))

theorem fz2_128_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨97, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 97 (by decide)))

theorem fz2_128_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨98, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 98 (by decide)))

theorem fz2_128_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨99, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 99 (by decide)))

theorem fz2_128_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨100, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 100 (by decide)))

theorem fz2_128_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨101, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 101 (by decide)))

theorem fz2_128_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨102, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 102 (by decide)))

theorem fz2_128_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨104, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 104 (by decide)))

theorem fz2_128_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨105, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 105 (by decide)))

theorem fz2_128_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨106, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 106 (by decide)))

theorem fz2_128_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨107, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 107 (by decide)))

theorem fz2_128_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨108, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 108 (by decide)))

theorem fz2_128_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨110, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 110 (by decide)))

theorem fz2_128_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨111, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 111 (by decide)))

theorem fz2_128_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨113, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 113 (by decide)))

theorem fz2_128_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨114, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 114 (by decide)))

theorem fz2_128_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨115, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 115 (by decide)))

theorem fz2_128_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨116, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 116 (by decide)))

theorem fz2_128_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨117, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 117 (by decide)))

theorem fz2_128_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨118, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 118 (by decide)))

theorem fz2_128_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨119, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 119 (by decide)))

theorem fz2_128_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨120, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 120 (by decide)))

theorem fz2_128_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨121, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 121 (by decide)))

theorem fz2_128_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨122, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 122 (by decide)))

theorem fz2_128_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨123, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 123 (by decide)))

theorem fz2_128_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨124, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 124 (by decide)))

theorem fz2_128_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨125, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 125 (by decide)))

theorem fz2_128_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨126, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 126 (by decide)))

theorem fz2_128_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨127, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 127 (by decide)))

theorem fz2_128_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨129, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 129 (by decide)))

theorem fz2_128_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨130, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 130 (by decide)))

theorem fz2_128_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨131, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 131 (by decide)))

theorem fz2_128_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨132, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 132 (by decide)))

theorem fz2_128_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨133, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 133 (by decide)))

theorem fz2_128_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨134, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 134 (by decide)))

theorem fz2_128_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨135, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 135 (by decide)))

theorem fz2_128_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨136, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 136 (by decide)))

theorem fz2_128_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨137, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 137 (by decide)))

theorem fz2_128_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨138, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 138 (by decide)))

theorem fz2_128_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨139, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 139 (by decide)))

theorem fz2_128_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨140, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 140 (by decide)))

theorem fz2_128_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨141, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 141 (by decide)))

theorem fz2_128_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨142, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 142 (by decide)))

theorem fz2_128_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨143, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 143 (by decide)))

theorem fz2_128_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨144, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 144 (by decide)))

theorem fz2_128_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨145, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 145 (by decide)))

theorem fz2_128_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK128)) = 0 :=
  Q2.repsFixedCard2 rK128 ⟨146, by decide⟩ Q2.R128_2 Q2.hpxR128_2 Q2.hcardq128_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_128) 146 (by decide)))

theorem fixz1_129 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 41, 44, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 98, 99, 100, 101, 102, 103, 106, 107, 108, 109, 110, 111, 112, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK129) (retConj 1 (R129 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_129_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨1, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 1 (by decide)))

theorem fz1_129_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨2, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 2 (by decide)))

theorem fz1_129_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨4, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 4 (by decide)))

theorem fz1_129_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨5, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 5 (by decide)))

theorem fz1_129_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨6, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 6 (by decide)))

theorem fz1_129_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨7, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 7 (by decide)))

theorem fz1_129_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨8, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 8 (by decide)))

theorem fz1_129_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨9, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 9 (by decide)))

theorem fz1_129_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨11, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 11 (by decide)))

theorem fz1_129_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨13, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 13 (by decide)))

theorem fz1_129_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨14, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 14 (by decide)))

theorem fz1_129_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨15, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 15 (by decide)))

theorem fz1_129_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨16, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 16 (by decide)))

theorem fz1_129_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨17, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 17 (by decide)))

theorem fz1_129_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨18, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 18 (by decide)))

theorem fz1_129_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨19, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 19 (by decide)))

theorem fz1_129_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨20, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 20 (by decide)))

theorem fz1_129_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨22, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 22 (by decide)))

theorem fz1_129_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨23, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 23 (by decide)))

theorem fz1_129_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨24, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 24 (by decide)))

theorem fz1_129_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨25, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 25 (by decide)))

theorem fz1_129_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨26, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 26 (by decide)))

theorem fz1_129_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨27, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 27 (by decide)))

theorem fz1_129_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨28, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 28 (by decide)))

theorem fz1_129_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨30, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 30 (by decide)))

theorem fz1_129_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨31, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 31 (by decide)))

theorem fz1_129_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨32, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 32 (by decide)))

theorem fz1_129_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨33, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 33 (by decide)))

theorem fz1_129_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨34, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 34 (by decide)))

theorem fz1_129_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨36, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 36 (by decide)))

theorem fz1_129_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨37, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 37 (by decide)))

theorem fz1_129_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨38, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 38 (by decide)))

theorem fz1_129_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨39, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 39 (by decide)))

theorem fz1_129_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨40, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 40 (by decide)))

theorem fz1_129_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨41, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 41 (by decide)))

theorem fz1_129_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨44, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 44 (by decide)))

theorem fz1_129_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨45, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 45 (by decide)))

theorem fz1_129_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨46, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 46 (by decide)))

theorem fz1_129_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨47, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 47 (by decide)))

theorem fz1_129_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨48, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 48 (by decide)))

theorem fz1_129_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨49, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 49 (by decide)))

theorem fz1_129_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨50, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 50 (by decide)))

theorem fz1_129_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨52, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 52 (by decide)))

theorem fz1_129_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨54, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 54 (by decide)))

theorem fz1_129_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨55, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 55 (by decide)))

theorem fz1_129_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨56, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 56 (by decide)))

theorem fz1_129_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨57, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 57 (by decide)))

theorem fz1_129_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨58, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 58 (by decide)))

theorem fz1_129_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨59, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 59 (by decide)))

theorem fz1_129_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨60, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 60 (by decide)))

theorem fz1_129_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨61, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 61 (by decide)))

theorem fz1_129_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨62, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 62 (by decide)))

theorem fz1_129_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨63, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 63 (by decide)))

theorem fz1_129_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨64, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 64 (by decide)))

theorem fz1_129_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨65, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 65 (by decide)))

theorem fz1_129_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨66, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 66 (by decide)))

theorem fz1_129_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨67, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 67 (by decide)))

theorem fz1_129_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨68, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 68 (by decide)))

theorem fz1_129_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨69, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 69 (by decide)))

theorem fz1_129_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨70, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 70 (by decide)))

theorem fz1_129_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨71, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 71 (by decide)))

theorem fz1_129_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨72, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 72 (by decide)))

theorem fz1_129_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨73, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 73 (by decide)))

theorem fz1_129_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨74, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 74 (by decide)))

theorem fz1_129_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨75, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 75 (by decide)))

theorem fz1_129_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨76, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 76 (by decide)))

theorem fz1_129_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨77, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 77 (by decide)))

theorem fz1_129_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨78, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 78 (by decide)))

theorem fz1_129_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨79, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 79 (by decide)))

theorem fz1_129_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨80, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 80 (by decide)))

theorem fz1_129_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨81, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 81 (by decide)))

theorem fz1_129_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨83, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 83 (by decide)))

theorem fz1_129_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨84, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 84 (by decide)))

theorem fz1_129_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨85, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 85 (by decide)))

theorem fz1_129_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨86, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 86 (by decide)))

theorem fz1_129_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨87, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 87 (by decide)))

theorem fz1_129_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨88, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 88 (by decide)))

theorem fz1_129_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨89, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 89 (by decide)))

theorem fz1_129_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨90, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 90 (by decide)))

theorem fz1_129_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨92, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 92 (by decide)))

theorem fz1_129_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨93, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 93 (by decide)))

theorem fz1_129_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨94, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 94 (by decide)))

theorem fz1_129_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨95, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 95 (by decide)))

theorem fz1_129_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨96, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 96 (by decide)))

theorem fz1_129_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨98, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 98 (by decide)))

theorem fz1_129_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨99, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 99 (by decide)))

theorem fz1_129_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨100, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 100 (by decide)))

theorem fz1_129_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨101, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 101 (by decide)))

theorem fz1_129_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨102, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 102 (by decide)))

theorem fz1_129_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨103, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 103 (by decide)))

theorem fz1_129_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨106, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 106 (by decide)))

theorem fz1_129_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨107, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 107 (by decide)))

theorem fz1_129_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨108, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 108 (by decide)))

theorem fz1_129_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨109, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 109 (by decide)))

theorem fz1_129_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨110, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 110 (by decide)))

theorem fz1_129_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨111, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 111 (by decide)))

theorem fz1_129_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨112, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 112 (by decide)))

theorem fz1_129_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨114, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 114 (by decide)))

theorem fz1_129_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨115, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 115 (by decide)))

theorem fz1_129_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨116, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 116 (by decide)))

theorem fz1_129_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨117, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 117 (by decide)))

theorem fz1_129_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨118, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 118 (by decide)))

theorem fz1_129_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨119, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 119 (by decide)))

theorem fz1_129_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨120, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 120 (by decide)))

theorem fz1_129_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨121, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 121 (by decide)))

theorem fz1_129_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨122, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 122 (by decide)))

theorem fz1_129_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨123, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 123 (by decide)))

theorem fz1_129_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨124, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 124 (by decide)))

theorem fz1_129_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨125, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 125 (by decide)))

theorem fz1_129_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨126, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 126 (by decide)))

theorem fz1_129_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨127, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 127 (by decide)))

theorem fz1_129_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨128, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 128 (by decide)))

theorem fz1_129_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨130, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 130 (by decide)))

theorem fz1_129_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨131, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 131 (by decide)))

theorem fz1_129_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨132, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 132 (by decide)))

theorem fz1_129_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨133, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 133 (by decide)))

theorem fz1_129_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨134, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 134 (by decide)))

theorem fz1_129_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨135, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 135 (by decide)))

theorem fz1_129_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨136, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 136 (by decide)))

theorem fz1_129_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨137, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 137 (by decide)))

theorem fz1_129_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨138, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 138 (by decide)))

theorem fz1_129_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨139, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 139 (by decide)))

theorem fz1_129_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨140, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 140 (by decide)))

theorem fz1_129_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨141, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 141 (by decide)))

theorem fz1_129_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨142, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 142 (by decide)))

theorem fz1_129_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨143, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 143 (by decide)))

theorem fz1_129_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨144, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 144 (by decide)))

theorem fz1_129_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨145, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 145 (by decide)))

theorem fz1_129_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK129)) = 0 :=
  repsFixedCard rK129 ⟨146, by decide⟩ R129 hpxR129 hcardq129
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_129) 146 (by decide)))

theorem fixz2_129 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 41, 44, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 98, 99, 100, 101, 102, 103, 106, 107, 108, 109, 110, 111, 112, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK129) (retConj 2 (Q2.R129_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_129_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨1, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 1 (by decide)))

theorem fz2_129_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨2, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 2 (by decide)))

theorem fz2_129_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨4, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 4 (by decide)))

theorem fz2_129_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨5, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 5 (by decide)))

theorem fz2_129_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨6, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 6 (by decide)))

theorem fz2_129_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨7, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 7 (by decide)))

theorem fz2_129_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨8, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 8 (by decide)))

theorem fz2_129_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨9, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 9 (by decide)))

theorem fz2_129_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨11, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 11 (by decide)))

theorem fz2_129_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨13, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 13 (by decide)))

theorem fz2_129_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨14, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 14 (by decide)))

theorem fz2_129_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨15, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 15 (by decide)))

theorem fz2_129_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨16, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 16 (by decide)))

theorem fz2_129_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨17, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 17 (by decide)))

theorem fz2_129_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨18, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 18 (by decide)))

theorem fz2_129_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨19, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 19 (by decide)))

theorem fz2_129_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨20, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 20 (by decide)))

theorem fz2_129_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨22, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 22 (by decide)))

theorem fz2_129_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨23, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 23 (by decide)))

theorem fz2_129_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨24, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 24 (by decide)))

theorem fz2_129_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨25, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 25 (by decide)))

theorem fz2_129_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨26, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 26 (by decide)))

theorem fz2_129_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨27, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 27 (by decide)))

theorem fz2_129_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨28, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 28 (by decide)))

theorem fz2_129_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨30, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 30 (by decide)))

theorem fz2_129_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨31, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 31 (by decide)))

theorem fz2_129_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨32, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 32 (by decide)))

theorem fz2_129_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨33, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 33 (by decide)))

theorem fz2_129_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨34, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 34 (by decide)))

theorem fz2_129_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨36, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 36 (by decide)))

theorem fz2_129_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨37, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 37 (by decide)))

theorem fz2_129_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨38, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 38 (by decide)))

theorem fz2_129_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨39, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 39 (by decide)))

theorem fz2_129_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨40, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 40 (by decide)))

theorem fz2_129_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨41, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 41 (by decide)))

theorem fz2_129_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨44, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 44 (by decide)))

theorem fz2_129_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨45, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 45 (by decide)))

theorem fz2_129_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨46, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 46 (by decide)))

theorem fz2_129_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨47, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 47 (by decide)))

theorem fz2_129_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨48, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 48 (by decide)))

theorem fz2_129_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨49, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 49 (by decide)))

theorem fz2_129_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨50, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 50 (by decide)))

theorem fz2_129_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨52, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 52 (by decide)))

theorem fz2_129_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨54, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 54 (by decide)))

theorem fz2_129_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨55, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 55 (by decide)))

theorem fz2_129_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨56, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 56 (by decide)))

theorem fz2_129_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨57, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 57 (by decide)))

theorem fz2_129_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨58, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 58 (by decide)))

theorem fz2_129_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨59, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 59 (by decide)))

theorem fz2_129_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨60, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 60 (by decide)))

theorem fz2_129_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨61, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 61 (by decide)))

theorem fz2_129_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨62, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 62 (by decide)))

theorem fz2_129_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨63, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 63 (by decide)))

theorem fz2_129_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨64, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 64 (by decide)))

theorem fz2_129_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨65, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 65 (by decide)))

theorem fz2_129_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨66, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 66 (by decide)))

theorem fz2_129_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨67, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 67 (by decide)))

theorem fz2_129_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨68, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 68 (by decide)))

theorem fz2_129_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨69, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 69 (by decide)))

theorem fz2_129_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨70, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 70 (by decide)))

theorem fz2_129_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨71, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 71 (by decide)))

theorem fz2_129_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨72, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 72 (by decide)))

theorem fz2_129_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨73, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 73 (by decide)))

theorem fz2_129_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨74, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 74 (by decide)))

theorem fz2_129_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨75, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 75 (by decide)))

theorem fz2_129_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨76, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 76 (by decide)))

theorem fz2_129_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨77, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 77 (by decide)))

theorem fz2_129_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨78, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 78 (by decide)))

theorem fz2_129_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨79, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 79 (by decide)))

theorem fz2_129_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨80, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 80 (by decide)))

theorem fz2_129_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨81, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 81 (by decide)))

theorem fz2_129_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨83, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 83 (by decide)))

theorem fz2_129_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨84, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 84 (by decide)))

theorem fz2_129_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨85, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 85 (by decide)))

theorem fz2_129_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨86, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 86 (by decide)))

theorem fz2_129_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨87, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 87 (by decide)))

theorem fz2_129_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨88, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 88 (by decide)))

theorem fz2_129_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨89, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 89 (by decide)))

theorem fz2_129_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨90, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 90 (by decide)))

theorem fz2_129_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨92, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 92 (by decide)))

theorem fz2_129_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨93, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 93 (by decide)))

theorem fz2_129_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨94, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 94 (by decide)))

theorem fz2_129_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨95, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 95 (by decide)))

theorem fz2_129_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨96, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 96 (by decide)))

theorem fz2_129_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨98, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 98 (by decide)))

theorem fz2_129_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨99, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 99 (by decide)))

theorem fz2_129_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨100, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 100 (by decide)))

theorem fz2_129_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨101, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 101 (by decide)))

theorem fz2_129_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨102, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 102 (by decide)))

theorem fz2_129_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨103, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 103 (by decide)))

theorem fz2_129_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨106, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 106 (by decide)))

theorem fz2_129_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨107, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 107 (by decide)))

theorem fz2_129_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨108, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 108 (by decide)))

theorem fz2_129_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨109, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 109 (by decide)))

theorem fz2_129_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨110, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 110 (by decide)))

theorem fz2_129_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨111, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 111 (by decide)))

theorem fz2_129_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨112, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 112 (by decide)))

theorem fz2_129_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨114, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 114 (by decide)))

theorem fz2_129_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨115, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 115 (by decide)))

theorem fz2_129_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨116, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 116 (by decide)))

theorem fz2_129_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨117, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 117 (by decide)))

theorem fz2_129_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨118, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 118 (by decide)))

theorem fz2_129_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨119, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 119 (by decide)))

theorem fz2_129_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨120, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 120 (by decide)))

theorem fz2_129_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨121, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 121 (by decide)))

theorem fz2_129_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨122, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 122 (by decide)))

theorem fz2_129_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨123, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 123 (by decide)))

theorem fz2_129_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨124, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 124 (by decide)))

theorem fz2_129_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨125, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 125 (by decide)))

theorem fz2_129_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨126, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 126 (by decide)))

theorem fz2_129_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨127, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 127 (by decide)))

theorem fz2_129_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨128, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 128 (by decide)))

theorem fz2_129_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨130, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 130 (by decide)))

theorem fz2_129_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨131, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 131 (by decide)))

theorem fz2_129_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨132, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 132 (by decide)))

theorem fz2_129_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨133, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 133 (by decide)))

theorem fz2_129_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨134, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 134 (by decide)))

theorem fz2_129_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨135, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 135 (by decide)))

theorem fz2_129_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨136, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 136 (by decide)))

theorem fz2_129_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨137, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 137 (by decide)))

theorem fz2_129_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨138, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 138 (by decide)))

theorem fz2_129_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨139, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 139 (by decide)))

theorem fz2_129_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨140, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 140 (by decide)))

theorem fz2_129_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨141, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 141 (by decide)))

theorem fz2_129_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨142, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 142 (by decide)))

theorem fz2_129_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨143, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 143 (by decide)))

theorem fz2_129_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨144, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 144 (by decide)))

theorem fz2_129_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨145, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 145 (by decide)))

theorem fz2_129_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK129)) = 0 :=
  Q2.repsFixedCard2 rK129 ⟨146, by decide⟩ Q2.R129_2 Q2.hpxR129_2 Q2.hcardq129_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_129) 146 (by decide)))

end LeanDring.P5Presentation
