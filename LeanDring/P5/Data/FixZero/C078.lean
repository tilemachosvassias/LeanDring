/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C023

/-!
# Species-table cells, off-support emptiness certificates, chunk 77

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

theorem fixz1_101 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK101) (retConj 1 (R101 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_101_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨1, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 1 (by decide)))

theorem fz1_101_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨2, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 2 (by decide)))

theorem fz1_101_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨3, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 3 (by decide)))

theorem fz1_101_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨4, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 4 (by decide)))

theorem fz1_101_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨5, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 5 (by decide)))

theorem fz1_101_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨6, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 6 (by decide)))

theorem fz1_101_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨7, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 7 (by decide)))

theorem fz1_101_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨8, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 8 (by decide)))

theorem fz1_101_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨9, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 9 (by decide)))

theorem fz1_101_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨11, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 11 (by decide)))

theorem fz1_101_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨13, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 13 (by decide)))

theorem fz1_101_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨14, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 14 (by decide)))

theorem fz1_101_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨15, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 15 (by decide)))

theorem fz1_101_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨16, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 16 (by decide)))

theorem fz1_101_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨17, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 17 (by decide)))

theorem fz1_101_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨18, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 18 (by decide)))

theorem fz1_101_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨19, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 19 (by decide)))

theorem fz1_101_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨20, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 20 (by decide)))

theorem fz1_101_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨21, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 21 (by decide)))

theorem fz1_101_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨22, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 22 (by decide)))

theorem fz1_101_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨23, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 23 (by decide)))

theorem fz1_101_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨24, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 24 (by decide)))

theorem fz1_101_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨25, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 25 (by decide)))

theorem fz1_101_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨26, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 26 (by decide)))

theorem fz1_101_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨27, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 27 (by decide)))

theorem fz1_101_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨28, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 28 (by decide)))

theorem fz1_101_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨29, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 29 (by decide)))

theorem fz1_101_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨30, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 30 (by decide)))

theorem fz1_101_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨31, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 31 (by decide)))

theorem fz1_101_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨32, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 32 (by decide)))

theorem fz1_101_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨33, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 33 (by decide)))

theorem fz1_101_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨34, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 34 (by decide)))

theorem fz1_101_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨35, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 35 (by decide)))

theorem fz1_101_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨36, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 36 (by decide)))

theorem fz1_101_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨37, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 37 (by decide)))

theorem fz1_101_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨38, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 38 (by decide)))

theorem fz1_101_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨40, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 40 (by decide)))

theorem fz1_101_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨41, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 41 (by decide)))

theorem fz1_101_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨42, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 42 (by decide)))

theorem fz1_101_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨43, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 43 (by decide)))

theorem fz1_101_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨44, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 44 (by decide)))

theorem fz1_101_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨45, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 45 (by decide)))

theorem fz1_101_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨46, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 46 (by decide)))

theorem fz1_101_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨47, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 47 (by decide)))

theorem fz1_101_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨48, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 48 (by decide)))

theorem fz1_101_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨49, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 49 (by decide)))

theorem fz1_101_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨50, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 50 (by decide)))

theorem fz1_101_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨51, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 51 (by decide)))

theorem fz1_101_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨52, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 52 (by decide)))

theorem fz1_101_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨54, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 54 (by decide)))

theorem fz1_101_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨55, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 55 (by decide)))

theorem fz1_101_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨56, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 56 (by decide)))

theorem fz1_101_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨57, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 57 (by decide)))

theorem fz1_101_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨58, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 58 (by decide)))

theorem fz1_101_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨59, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 59 (by decide)))

theorem fz1_101_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨60, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 60 (by decide)))

theorem fz1_101_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨61, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 61 (by decide)))

theorem fz1_101_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨62, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 62 (by decide)))

theorem fz1_101_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨63, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 63 (by decide)))

theorem fz1_101_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨64, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 64 (by decide)))

theorem fz1_101_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨65, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 65 (by decide)))

theorem fz1_101_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨66, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 66 (by decide)))

theorem fz1_101_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨67, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 67 (by decide)))

theorem fz1_101_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨68, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 68 (by decide)))

theorem fz1_101_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨69, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 69 (by decide)))

theorem fz1_101_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨70, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 70 (by decide)))

theorem fz1_101_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨71, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 71 (by decide)))

theorem fz1_101_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨72, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 72 (by decide)))

theorem fz1_101_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨73, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 73 (by decide)))

theorem fz1_101_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨74, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 74 (by decide)))

theorem fz1_101_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨75, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 75 (by decide)))

theorem fz1_101_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨76, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 76 (by decide)))

theorem fz1_101_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨77, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 77 (by decide)))

theorem fz1_101_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨78, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 78 (by decide)))

theorem fz1_101_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨79, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 79 (by decide)))

theorem fz1_101_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨80, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 80 (by decide)))

theorem fz1_101_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨81, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 81 (by decide)))

theorem fz1_101_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨82, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 82 (by decide)))

theorem fz1_101_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨83, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 83 (by decide)))

theorem fz1_101_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨84, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 84 (by decide)))

theorem fz1_101_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨85, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 85 (by decide)))

theorem fz1_101_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨86, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 86 (by decide)))

theorem fz1_101_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨87, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 87 (by decide)))

theorem fz1_101_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨88, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 88 (by decide)))

theorem fz1_101_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨89, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 89 (by decide)))

theorem fz1_101_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨90, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 90 (by decide)))

theorem fz1_101_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨91, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 91 (by decide)))

theorem fz1_101_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨92, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 92 (by decide)))

theorem fz1_101_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨93, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 93 (by decide)))

theorem fz1_101_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨94, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 94 (by decide)))

theorem fz1_101_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨95, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 95 (by decide)))

theorem fz1_101_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨96, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 96 (by decide)))

theorem fz1_101_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨97, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 97 (by decide)))

theorem fz1_101_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨98, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 98 (by decide)))

theorem fz1_101_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨99, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 99 (by decide)))

theorem fz1_101_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨100, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 100 (by decide)))

theorem fz1_101_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨102, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 102 (by decide)))

theorem fz1_101_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨103, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 103 (by decide)))

theorem fz1_101_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨104, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 104 (by decide)))

theorem fz1_101_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨105, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 105 (by decide)))

theorem fz1_101_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨106, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 106 (by decide)))

theorem fz1_101_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨107, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 107 (by decide)))

theorem fz1_101_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨108, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 108 (by decide)))

theorem fz1_101_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨109, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 109 (by decide)))

theorem fz1_101_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨110, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 110 (by decide)))

theorem fz1_101_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨111, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 111 (by decide)))

theorem fz1_101_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨112, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 112 (by decide)))

theorem fz1_101_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨113, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 113 (by decide)))

theorem fz1_101_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨114, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 114 (by decide)))

theorem fz1_101_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK101)) = 0 :=
  repsFixedCard rK101 ⟨115, by decide⟩ R101 hpxR101 hcardq101
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_101) 115 (by decide)))

theorem fixz2_101 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK101) (retConj 2 (Q2.R101_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_101_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨1, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 1 (by decide)))

theorem fz2_101_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨2, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 2 (by decide)))

theorem fz2_101_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨3, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 3 (by decide)))

theorem fz2_101_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨4, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 4 (by decide)))

theorem fz2_101_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨5, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 5 (by decide)))

theorem fz2_101_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨6, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 6 (by decide)))

theorem fz2_101_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨7, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 7 (by decide)))

theorem fz2_101_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨8, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 8 (by decide)))

theorem fz2_101_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨9, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 9 (by decide)))

theorem fz2_101_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨11, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 11 (by decide)))

theorem fz2_101_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨13, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 13 (by decide)))

theorem fz2_101_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨14, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 14 (by decide)))

theorem fz2_101_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨15, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 15 (by decide)))

theorem fz2_101_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨16, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 16 (by decide)))

theorem fz2_101_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨17, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 17 (by decide)))

theorem fz2_101_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨18, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 18 (by decide)))

theorem fz2_101_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨19, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 19 (by decide)))

theorem fz2_101_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨20, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 20 (by decide)))

theorem fz2_101_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨21, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 21 (by decide)))

theorem fz2_101_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨22, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 22 (by decide)))

theorem fz2_101_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨23, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 23 (by decide)))

theorem fz2_101_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨24, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 24 (by decide)))

theorem fz2_101_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨25, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 25 (by decide)))

theorem fz2_101_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨26, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 26 (by decide)))

theorem fz2_101_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨27, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 27 (by decide)))

theorem fz2_101_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨28, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 28 (by decide)))

theorem fz2_101_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨29, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 29 (by decide)))

theorem fz2_101_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨30, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 30 (by decide)))

theorem fz2_101_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨31, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 31 (by decide)))

theorem fz2_101_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨32, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 32 (by decide)))

theorem fz2_101_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨33, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 33 (by decide)))

theorem fz2_101_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨34, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 34 (by decide)))

theorem fz2_101_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨35, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 35 (by decide)))

theorem fz2_101_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨36, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 36 (by decide)))

theorem fz2_101_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨37, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 37 (by decide)))

theorem fz2_101_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨38, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 38 (by decide)))

theorem fz2_101_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨40, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 40 (by decide)))

theorem fz2_101_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨41, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 41 (by decide)))

theorem fz2_101_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨42, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 42 (by decide)))

theorem fz2_101_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨43, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 43 (by decide)))

theorem fz2_101_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨44, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 44 (by decide)))

theorem fz2_101_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨45, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 45 (by decide)))

theorem fz2_101_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨46, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 46 (by decide)))

theorem fz2_101_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨47, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 47 (by decide)))

theorem fz2_101_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨48, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 48 (by decide)))

theorem fz2_101_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨49, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 49 (by decide)))

theorem fz2_101_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨50, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 50 (by decide)))

theorem fz2_101_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨51, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 51 (by decide)))

theorem fz2_101_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨52, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 52 (by decide)))

theorem fz2_101_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨54, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 54 (by decide)))

theorem fz2_101_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨55, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 55 (by decide)))

theorem fz2_101_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨56, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 56 (by decide)))

theorem fz2_101_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨57, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 57 (by decide)))

theorem fz2_101_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨58, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 58 (by decide)))

theorem fz2_101_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨59, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 59 (by decide)))

theorem fz2_101_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨60, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 60 (by decide)))

theorem fz2_101_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨61, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 61 (by decide)))

theorem fz2_101_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨62, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 62 (by decide)))

theorem fz2_101_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨63, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 63 (by decide)))

theorem fz2_101_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨64, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 64 (by decide)))

theorem fz2_101_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨65, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 65 (by decide)))

theorem fz2_101_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨66, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 66 (by decide)))

theorem fz2_101_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨67, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 67 (by decide)))

theorem fz2_101_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨68, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 68 (by decide)))

theorem fz2_101_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨69, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 69 (by decide)))

theorem fz2_101_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨70, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 70 (by decide)))

theorem fz2_101_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨71, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 71 (by decide)))

theorem fz2_101_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨72, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 72 (by decide)))

theorem fz2_101_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨73, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 73 (by decide)))

theorem fz2_101_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨74, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 74 (by decide)))

theorem fz2_101_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨75, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 75 (by decide)))

theorem fz2_101_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨76, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 76 (by decide)))

theorem fz2_101_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨77, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 77 (by decide)))

theorem fz2_101_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨78, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 78 (by decide)))

theorem fz2_101_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨79, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 79 (by decide)))

theorem fz2_101_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨80, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 80 (by decide)))

theorem fz2_101_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨81, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 81 (by decide)))

theorem fz2_101_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨82, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 82 (by decide)))

theorem fz2_101_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨83, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 83 (by decide)))

theorem fz2_101_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨84, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 84 (by decide)))

theorem fz2_101_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨85, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 85 (by decide)))

theorem fz2_101_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨86, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 86 (by decide)))

theorem fz2_101_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨87, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 87 (by decide)))

theorem fz2_101_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨88, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 88 (by decide)))

theorem fz2_101_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨89, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 89 (by decide)))

theorem fz2_101_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨90, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 90 (by decide)))

theorem fz2_101_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨91, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 91 (by decide)))

theorem fz2_101_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨92, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 92 (by decide)))

theorem fz2_101_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨93, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 93 (by decide)))

theorem fz2_101_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨94, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 94 (by decide)))

theorem fz2_101_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨95, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 95 (by decide)))

theorem fz2_101_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨96, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 96 (by decide)))

theorem fz2_101_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨97, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 97 (by decide)))

theorem fz2_101_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨98, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 98 (by decide)))

theorem fz2_101_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨99, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 99 (by decide)))

theorem fz2_101_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨100, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 100 (by decide)))

theorem fz2_101_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨102, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 102 (by decide)))

theorem fz2_101_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨103, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 103 (by decide)))

theorem fz2_101_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨104, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 104 (by decide)))

theorem fz2_101_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨105, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 105 (by decide)))

theorem fz2_101_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨106, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 106 (by decide)))

theorem fz2_101_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨107, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 107 (by decide)))

theorem fz2_101_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨108, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 108 (by decide)))

theorem fz2_101_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨109, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 109 (by decide)))

theorem fz2_101_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨110, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 110 (by decide)))

theorem fz2_101_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨111, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 111 (by decide)))

theorem fz2_101_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨112, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 112 (by decide)))

theorem fz2_101_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨113, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 113 (by decide)))

theorem fz2_101_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨114, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 114 (by decide)))

theorem fz2_101_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK101)) = 0 :=
  Q2.repsFixedCard2 rK101 ⟨115, by decide⟩ Q2.R101_2 Q2.hpxR101_2 Q2.hcardq101_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_101) 115 (by decide)))

theorem fixz1_102 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK102) (retConj 1 (R102 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_102_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨1, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 1 (by decide)))

theorem fz1_102_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨2, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 2 (by decide)))

theorem fz1_102_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨3, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 3 (by decide)))

theorem fz1_102_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨4, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 4 (by decide)))

theorem fz1_102_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨5, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 5 (by decide)))

theorem fz1_102_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨6, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 6 (by decide)))

theorem fz1_102_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨7, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 7 (by decide)))

theorem fz1_102_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨8, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 8 (by decide)))

theorem fz1_102_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨9, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 9 (by decide)))

theorem fz1_102_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨11, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 11 (by decide)))

theorem fz1_102_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨13, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 13 (by decide)))

theorem fz1_102_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨14, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 14 (by decide)))

theorem fz1_102_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨15, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 15 (by decide)))

theorem fz1_102_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨16, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 16 (by decide)))

theorem fz1_102_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨17, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 17 (by decide)))

theorem fz1_102_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨18, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 18 (by decide)))

theorem fz1_102_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨19, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 19 (by decide)))

theorem fz1_102_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨20, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 20 (by decide)))

theorem fz1_102_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨21, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 21 (by decide)))

theorem fz1_102_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨22, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 22 (by decide)))

theorem fz1_102_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨23, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 23 (by decide)))

theorem fz1_102_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨24, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 24 (by decide)))

theorem fz1_102_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨25, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 25 (by decide)))

theorem fz1_102_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨26, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 26 (by decide)))

theorem fz1_102_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨27, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 27 (by decide)))

theorem fz1_102_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨28, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 28 (by decide)))

theorem fz1_102_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨29, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 29 (by decide)))

theorem fz1_102_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨30, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 30 (by decide)))

theorem fz1_102_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨31, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 31 (by decide)))

theorem fz1_102_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨32, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 32 (by decide)))

theorem fz1_102_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨33, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 33 (by decide)))

theorem fz1_102_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨34, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 34 (by decide)))

theorem fz1_102_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨35, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 35 (by decide)))

theorem fz1_102_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨36, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 36 (by decide)))

theorem fz1_102_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨37, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 37 (by decide)))

theorem fz1_102_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨38, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 38 (by decide)))

theorem fz1_102_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨39, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 39 (by decide)))

theorem fz1_102_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨41, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 41 (by decide)))

theorem fz1_102_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨42, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 42 (by decide)))

theorem fz1_102_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨43, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 43 (by decide)))

theorem fz1_102_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨44, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 44 (by decide)))

theorem fz1_102_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨45, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 45 (by decide)))

theorem fz1_102_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨46, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 46 (by decide)))

theorem fz1_102_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨47, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 47 (by decide)))

theorem fz1_102_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨48, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 48 (by decide)))

theorem fz1_102_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨49, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 49 (by decide)))

theorem fz1_102_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨50, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 50 (by decide)))

theorem fz1_102_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨51, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 51 (by decide)))

theorem fz1_102_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨52, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 52 (by decide)))

theorem fz1_102_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨54, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 54 (by decide)))

theorem fz1_102_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨55, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 55 (by decide)))

theorem fz1_102_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨56, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 56 (by decide)))

theorem fz1_102_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨57, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 57 (by decide)))

theorem fz1_102_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨58, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 58 (by decide)))

theorem fz1_102_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨59, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 59 (by decide)))

theorem fz1_102_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨60, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 60 (by decide)))

theorem fz1_102_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨61, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 61 (by decide)))

theorem fz1_102_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨62, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 62 (by decide)))

theorem fz1_102_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨63, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 63 (by decide)))

theorem fz1_102_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨64, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 64 (by decide)))

theorem fz1_102_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨65, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 65 (by decide)))

theorem fz1_102_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨66, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 66 (by decide)))

theorem fz1_102_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨67, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 67 (by decide)))

theorem fz1_102_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨68, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 68 (by decide)))

theorem fz1_102_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨69, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 69 (by decide)))

theorem fz1_102_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨70, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 70 (by decide)))

theorem fz1_102_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨71, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 71 (by decide)))

theorem fz1_102_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨72, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 72 (by decide)))

theorem fz1_102_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨73, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 73 (by decide)))

theorem fz1_102_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨74, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 74 (by decide)))

theorem fz1_102_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨75, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 75 (by decide)))

theorem fz1_102_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨76, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 76 (by decide)))

theorem fz1_102_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨77, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 77 (by decide)))

theorem fz1_102_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨78, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 78 (by decide)))

theorem fz1_102_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨79, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 79 (by decide)))

theorem fz1_102_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨80, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 80 (by decide)))

theorem fz1_102_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨81, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 81 (by decide)))

theorem fz1_102_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨82, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 82 (by decide)))

theorem fz1_102_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨83, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 83 (by decide)))

theorem fz1_102_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨84, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 84 (by decide)))

theorem fz1_102_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨85, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 85 (by decide)))

theorem fz1_102_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨86, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 86 (by decide)))

theorem fz1_102_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨87, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 87 (by decide)))

theorem fz1_102_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨88, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 88 (by decide)))

theorem fz1_102_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨89, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 89 (by decide)))

theorem fz1_102_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨90, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 90 (by decide)))

theorem fz1_102_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨91, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 91 (by decide)))

theorem fz1_102_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨92, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 92 (by decide)))

theorem fz1_102_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨93, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 93 (by decide)))

theorem fz1_102_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨94, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 94 (by decide)))

theorem fz1_102_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨95, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 95 (by decide)))

theorem fz1_102_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨96, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 96 (by decide)))

theorem fz1_102_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨97, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 97 (by decide)))

theorem fz1_102_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨98, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 98 (by decide)))

theorem fz1_102_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨99, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 99 (by decide)))

theorem fz1_102_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨100, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 100 (by decide)))

theorem fz1_102_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨101, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 101 (by decide)))

theorem fz1_102_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨103, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 103 (by decide)))

theorem fz1_102_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨104, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 104 (by decide)))

theorem fz1_102_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨105, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 105 (by decide)))

theorem fz1_102_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨106, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 106 (by decide)))

theorem fz1_102_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨107, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 107 (by decide)))

theorem fz1_102_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨108, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 108 (by decide)))

theorem fz1_102_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨109, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 109 (by decide)))

theorem fz1_102_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨110, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 110 (by decide)))

theorem fz1_102_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨111, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 111 (by decide)))

theorem fz1_102_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨112, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 112 (by decide)))

theorem fz1_102_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨113, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 113 (by decide)))

theorem fz1_102_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨114, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 114 (by decide)))

theorem fz1_102_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK102)) = 0 :=
  repsFixedCard rK102 ⟨115, by decide⟩ R102 hpxR102 hcardq102
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_102) 115 (by decide)))

theorem fixz2_102 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK102) (retConj 2 (Q2.R102_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_102_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨1, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 1 (by decide)))

theorem fz2_102_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨2, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 2 (by decide)))

theorem fz2_102_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨3, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 3 (by decide)))

theorem fz2_102_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨4, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 4 (by decide)))

theorem fz2_102_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨5, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 5 (by decide)))

theorem fz2_102_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨6, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 6 (by decide)))

theorem fz2_102_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨7, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 7 (by decide)))

theorem fz2_102_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨8, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 8 (by decide)))

theorem fz2_102_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨9, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 9 (by decide)))

theorem fz2_102_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨11, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 11 (by decide)))

theorem fz2_102_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨13, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 13 (by decide)))

theorem fz2_102_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨14, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 14 (by decide)))

theorem fz2_102_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨15, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 15 (by decide)))

theorem fz2_102_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨16, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 16 (by decide)))

theorem fz2_102_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨17, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 17 (by decide)))

theorem fz2_102_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨18, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 18 (by decide)))

theorem fz2_102_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨19, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 19 (by decide)))

theorem fz2_102_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨20, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 20 (by decide)))

theorem fz2_102_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨21, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 21 (by decide)))

theorem fz2_102_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨22, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 22 (by decide)))

theorem fz2_102_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨23, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 23 (by decide)))

theorem fz2_102_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨24, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 24 (by decide)))

theorem fz2_102_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨25, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 25 (by decide)))

theorem fz2_102_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨26, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 26 (by decide)))

theorem fz2_102_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨27, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 27 (by decide)))

theorem fz2_102_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨28, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 28 (by decide)))

theorem fz2_102_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨29, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 29 (by decide)))

theorem fz2_102_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨30, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 30 (by decide)))

theorem fz2_102_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨31, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 31 (by decide)))

theorem fz2_102_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨32, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 32 (by decide)))

theorem fz2_102_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨33, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 33 (by decide)))

theorem fz2_102_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨34, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 34 (by decide)))

theorem fz2_102_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨35, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 35 (by decide)))

theorem fz2_102_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨36, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 36 (by decide)))

theorem fz2_102_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨37, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 37 (by decide)))

theorem fz2_102_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨38, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 38 (by decide)))

theorem fz2_102_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨39, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 39 (by decide)))

theorem fz2_102_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨41, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 41 (by decide)))

theorem fz2_102_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨42, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 42 (by decide)))

theorem fz2_102_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨43, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 43 (by decide)))

theorem fz2_102_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨44, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 44 (by decide)))

theorem fz2_102_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨45, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 45 (by decide)))

theorem fz2_102_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨46, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 46 (by decide)))

theorem fz2_102_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨47, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 47 (by decide)))

theorem fz2_102_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨48, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 48 (by decide)))

theorem fz2_102_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨49, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 49 (by decide)))

theorem fz2_102_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨50, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 50 (by decide)))

theorem fz2_102_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨51, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 51 (by decide)))

theorem fz2_102_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨52, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 52 (by decide)))

theorem fz2_102_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨54, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 54 (by decide)))

theorem fz2_102_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨55, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 55 (by decide)))

theorem fz2_102_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨56, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 56 (by decide)))

theorem fz2_102_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨57, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 57 (by decide)))

theorem fz2_102_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨58, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 58 (by decide)))

theorem fz2_102_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨59, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 59 (by decide)))

theorem fz2_102_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨60, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 60 (by decide)))

theorem fz2_102_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨61, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 61 (by decide)))

theorem fz2_102_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨62, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 62 (by decide)))

theorem fz2_102_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨63, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 63 (by decide)))

theorem fz2_102_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨64, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 64 (by decide)))

theorem fz2_102_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨65, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 65 (by decide)))

theorem fz2_102_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨66, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 66 (by decide)))

theorem fz2_102_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨67, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 67 (by decide)))

theorem fz2_102_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨68, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 68 (by decide)))

theorem fz2_102_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨69, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 69 (by decide)))

theorem fz2_102_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨70, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 70 (by decide)))

theorem fz2_102_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨71, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 71 (by decide)))

theorem fz2_102_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨72, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 72 (by decide)))

theorem fz2_102_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨73, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 73 (by decide)))

theorem fz2_102_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨74, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 74 (by decide)))

theorem fz2_102_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨75, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 75 (by decide)))

theorem fz2_102_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨76, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 76 (by decide)))

theorem fz2_102_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨77, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 77 (by decide)))

theorem fz2_102_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨78, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 78 (by decide)))

theorem fz2_102_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨79, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 79 (by decide)))

theorem fz2_102_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨80, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 80 (by decide)))

theorem fz2_102_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨81, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 81 (by decide)))

theorem fz2_102_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨82, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 82 (by decide)))

theorem fz2_102_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨83, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 83 (by decide)))

theorem fz2_102_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨84, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 84 (by decide)))

theorem fz2_102_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨85, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 85 (by decide)))

theorem fz2_102_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨86, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 86 (by decide)))

theorem fz2_102_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨87, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 87 (by decide)))

theorem fz2_102_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨88, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 88 (by decide)))

theorem fz2_102_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨89, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 89 (by decide)))

theorem fz2_102_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨90, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 90 (by decide)))

theorem fz2_102_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨91, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 91 (by decide)))

theorem fz2_102_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨92, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 92 (by decide)))

theorem fz2_102_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨93, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 93 (by decide)))

theorem fz2_102_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨94, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 94 (by decide)))

theorem fz2_102_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨95, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 95 (by decide)))

theorem fz2_102_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨96, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 96 (by decide)))

theorem fz2_102_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨97, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 97 (by decide)))

theorem fz2_102_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨98, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 98 (by decide)))

theorem fz2_102_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨99, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 99 (by decide)))

theorem fz2_102_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨100, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 100 (by decide)))

theorem fz2_102_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨101, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 101 (by decide)))

theorem fz2_102_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨103, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 103 (by decide)))

theorem fz2_102_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨104, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 104 (by decide)))

theorem fz2_102_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨105, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 105 (by decide)))

theorem fz2_102_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨106, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 106 (by decide)))

theorem fz2_102_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨107, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 107 (by decide)))

theorem fz2_102_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨108, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 108 (by decide)))

theorem fz2_102_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨109, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 109 (by decide)))

theorem fz2_102_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨110, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 110 (by decide)))

theorem fz2_102_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨111, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 111 (by decide)))

theorem fz2_102_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨112, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 112 (by decide)))

theorem fz2_102_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨113, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 113 (by decide)))

theorem fz2_102_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨114, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 114 (by decide)))

theorem fz2_102_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK102)) = 0 :=
  Q2.repsFixedCard2 rK102 ⟨115, by decide⟩ Q2.R102_2 Q2.hpxR102_2 Q2.hcardq102_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_102) 115 (by decide)))

end LeanDring.P5Presentation
