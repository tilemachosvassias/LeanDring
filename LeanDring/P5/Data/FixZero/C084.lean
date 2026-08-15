/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C024

/-!
# Species-table cells, off-support emptiness certificates, chunk 83

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

theorem fixz1_113 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK113) (retConj 1 (R113 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_113_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨1, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 1 (by decide)))

theorem fz1_113_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨2, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 2 (by decide)))

theorem fz1_113_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨3, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 3 (by decide)))

theorem fz1_113_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨4, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 4 (by decide)))

theorem fz1_113_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨5, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 5 (by decide)))

theorem fz1_113_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨6, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 6 (by decide)))

theorem fz1_113_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨7, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 7 (by decide)))

theorem fz1_113_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨8, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 8 (by decide)))

theorem fz1_113_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨9, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 9 (by decide)))

theorem fz1_113_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨11, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 11 (by decide)))

theorem fz1_113_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨13, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 13 (by decide)))

theorem fz1_113_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨14, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 14 (by decide)))

theorem fz1_113_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨15, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 15 (by decide)))

theorem fz1_113_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨16, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 16 (by decide)))

theorem fz1_113_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨17, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 17 (by decide)))

theorem fz1_113_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨18, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 18 (by decide)))

theorem fz1_113_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨19, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 19 (by decide)))

theorem fz1_113_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨20, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 20 (by decide)))

theorem fz1_113_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨21, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 21 (by decide)))

theorem fz1_113_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨22, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 22 (by decide)))

theorem fz1_113_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨23, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 23 (by decide)))

theorem fz1_113_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨24, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 24 (by decide)))

theorem fz1_113_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨25, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 25 (by decide)))

theorem fz1_113_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨26, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 26 (by decide)))

theorem fz1_113_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨27, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 27 (by decide)))

theorem fz1_113_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨28, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 28 (by decide)))

theorem fz1_113_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨29, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 29 (by decide)))

theorem fz1_113_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨30, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 30 (by decide)))

theorem fz1_113_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨31, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 31 (by decide)))

theorem fz1_113_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨32, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 32 (by decide)))

theorem fz1_113_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨33, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 33 (by decide)))

theorem fz1_113_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨34, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 34 (by decide)))

theorem fz1_113_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨35, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 35 (by decide)))

theorem fz1_113_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨36, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 36 (by decide)))

theorem fz1_113_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨37, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 37 (by decide)))

theorem fz1_113_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨38, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 38 (by decide)))

theorem fz1_113_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨39, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 39 (by decide)))

theorem fz1_113_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨40, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 40 (by decide)))

theorem fz1_113_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨41, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 41 (by decide)))

theorem fz1_113_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨42, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 42 (by decide)))

theorem fz1_113_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨43, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 43 (by decide)))

theorem fz1_113_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨44, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 44 (by decide)))

theorem fz1_113_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨45, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 45 (by decide)))

theorem fz1_113_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨46, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 46 (by decide)))

theorem fz1_113_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨47, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 47 (by decide)))

theorem fz1_113_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨48, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 48 (by decide)))

theorem fz1_113_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨49, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 49 (by decide)))

theorem fz1_113_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨50, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 50 (by decide)))

theorem fz1_113_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨52, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 52 (by decide)))

theorem fz1_113_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨54, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 54 (by decide)))

theorem fz1_113_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨55, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 55 (by decide)))

theorem fz1_113_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨56, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 56 (by decide)))

theorem fz1_113_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨57, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 57 (by decide)))

theorem fz1_113_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨58, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 58 (by decide)))

theorem fz1_113_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨59, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 59 (by decide)))

theorem fz1_113_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨60, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 60 (by decide)))

theorem fz1_113_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨61, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 61 (by decide)))

theorem fz1_113_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨62, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 62 (by decide)))

theorem fz1_113_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨63, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 63 (by decide)))

theorem fz1_113_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨64, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 64 (by decide)))

theorem fz1_113_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨65, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 65 (by decide)))

theorem fz1_113_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨66, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 66 (by decide)))

theorem fz1_113_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨67, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 67 (by decide)))

theorem fz1_113_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨68, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 68 (by decide)))

theorem fz1_113_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨69, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 69 (by decide)))

theorem fz1_113_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨70, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 70 (by decide)))

theorem fz1_113_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨71, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 71 (by decide)))

theorem fz1_113_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨72, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 72 (by decide)))

theorem fz1_113_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨73, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 73 (by decide)))

theorem fz1_113_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨74, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 74 (by decide)))

theorem fz1_113_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨75, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 75 (by decide)))

theorem fz1_113_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨76, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 76 (by decide)))

theorem fz1_113_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨77, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 77 (by decide)))

theorem fz1_113_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨78, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 78 (by decide)))

theorem fz1_113_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨79, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 79 (by decide)))

theorem fz1_113_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨80, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 80 (by decide)))

theorem fz1_113_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨81, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 81 (by decide)))

theorem fz1_113_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨82, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 82 (by decide)))

theorem fz1_113_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨83, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 83 (by decide)))

theorem fz1_113_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨84, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 84 (by decide)))

theorem fz1_113_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨85, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 85 (by decide)))

theorem fz1_113_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨86, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 86 (by decide)))

theorem fz1_113_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨87, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 87 (by decide)))

theorem fz1_113_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨88, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 88 (by decide)))

theorem fz1_113_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨89, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 89 (by decide)))

theorem fz1_113_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨90, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 90 (by decide)))

theorem fz1_113_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨91, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 91 (by decide)))

theorem fz1_113_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨92, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 92 (by decide)))

theorem fz1_113_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨93, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 93 (by decide)))

theorem fz1_113_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨94, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 94 (by decide)))

theorem fz1_113_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨95, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 95 (by decide)))

theorem fz1_113_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨96, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 96 (by decide)))

theorem fz1_113_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨97, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 97 (by decide)))

theorem fz1_113_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨98, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 98 (by decide)))

theorem fz1_113_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨99, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 99 (by decide)))

theorem fz1_113_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨100, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 100 (by decide)))

theorem fz1_113_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨101, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 101 (by decide)))

theorem fz1_113_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨102, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 102 (by decide)))

theorem fz1_113_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨103, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 103 (by decide)))

theorem fz1_113_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨104, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 104 (by decide)))

theorem fz1_113_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨105, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 105 (by decide)))

theorem fz1_113_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨106, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 106 (by decide)))

theorem fz1_113_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨107, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 107 (by decide)))

theorem fz1_113_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨108, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 108 (by decide)))

theorem fz1_113_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨109, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 109 (by decide)))

theorem fz1_113_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨110, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 110 (by decide)))

theorem fz1_113_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨111, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 111 (by decide)))

theorem fz1_113_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨112, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 112 (by decide)))

theorem fz1_113_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨114, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 114 (by decide)))

theorem fz1_113_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK113)) = 0 :=
  repsFixedCard rK113 ⟨115, by decide⟩ R113 hpxR113 hcardq113
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_113) 115 (by decide)))

theorem fixz2_113 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK113) (retConj 2 (Q2.R113_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_113_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨1, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 1 (by decide)))

theorem fz2_113_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨2, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 2 (by decide)))

theorem fz2_113_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨3, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 3 (by decide)))

theorem fz2_113_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨4, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 4 (by decide)))

theorem fz2_113_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨5, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 5 (by decide)))

theorem fz2_113_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨6, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 6 (by decide)))

theorem fz2_113_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨7, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 7 (by decide)))

theorem fz2_113_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨8, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 8 (by decide)))

theorem fz2_113_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨9, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 9 (by decide)))

theorem fz2_113_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨11, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 11 (by decide)))

theorem fz2_113_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨13, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 13 (by decide)))

theorem fz2_113_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨14, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 14 (by decide)))

theorem fz2_113_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨15, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 15 (by decide)))

theorem fz2_113_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨16, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 16 (by decide)))

theorem fz2_113_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨17, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 17 (by decide)))

theorem fz2_113_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨18, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 18 (by decide)))

theorem fz2_113_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨19, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 19 (by decide)))

theorem fz2_113_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨20, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 20 (by decide)))

theorem fz2_113_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨21, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 21 (by decide)))

theorem fz2_113_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨22, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 22 (by decide)))

theorem fz2_113_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨23, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 23 (by decide)))

theorem fz2_113_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨24, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 24 (by decide)))

theorem fz2_113_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨25, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 25 (by decide)))

theorem fz2_113_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨26, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 26 (by decide)))

theorem fz2_113_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨27, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 27 (by decide)))

theorem fz2_113_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨28, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 28 (by decide)))

theorem fz2_113_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨29, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 29 (by decide)))

theorem fz2_113_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨30, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 30 (by decide)))

theorem fz2_113_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨31, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 31 (by decide)))

theorem fz2_113_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨32, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 32 (by decide)))

theorem fz2_113_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨33, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 33 (by decide)))

theorem fz2_113_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨34, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 34 (by decide)))

theorem fz2_113_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨35, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 35 (by decide)))

theorem fz2_113_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨36, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 36 (by decide)))

theorem fz2_113_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨37, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 37 (by decide)))

theorem fz2_113_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨38, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 38 (by decide)))

theorem fz2_113_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨39, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 39 (by decide)))

theorem fz2_113_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨40, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 40 (by decide)))

theorem fz2_113_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨41, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 41 (by decide)))

theorem fz2_113_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨42, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 42 (by decide)))

theorem fz2_113_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨43, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 43 (by decide)))

theorem fz2_113_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨44, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 44 (by decide)))

theorem fz2_113_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨45, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 45 (by decide)))

theorem fz2_113_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨46, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 46 (by decide)))

theorem fz2_113_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨47, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 47 (by decide)))

theorem fz2_113_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨48, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 48 (by decide)))

theorem fz2_113_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨49, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 49 (by decide)))

theorem fz2_113_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨50, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 50 (by decide)))

theorem fz2_113_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨52, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 52 (by decide)))

theorem fz2_113_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨54, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 54 (by decide)))

theorem fz2_113_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨55, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 55 (by decide)))

theorem fz2_113_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨56, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 56 (by decide)))

theorem fz2_113_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨57, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 57 (by decide)))

theorem fz2_113_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨58, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 58 (by decide)))

theorem fz2_113_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨59, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 59 (by decide)))

theorem fz2_113_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨60, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 60 (by decide)))

theorem fz2_113_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨61, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 61 (by decide)))

theorem fz2_113_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨62, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 62 (by decide)))

theorem fz2_113_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨63, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 63 (by decide)))

theorem fz2_113_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨64, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 64 (by decide)))

theorem fz2_113_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨65, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 65 (by decide)))

theorem fz2_113_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨66, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 66 (by decide)))

theorem fz2_113_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨67, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 67 (by decide)))

theorem fz2_113_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨68, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 68 (by decide)))

theorem fz2_113_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨69, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 69 (by decide)))

theorem fz2_113_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨70, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 70 (by decide)))

theorem fz2_113_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨71, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 71 (by decide)))

theorem fz2_113_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨72, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 72 (by decide)))

theorem fz2_113_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨73, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 73 (by decide)))

theorem fz2_113_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨74, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 74 (by decide)))

theorem fz2_113_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨75, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 75 (by decide)))

theorem fz2_113_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨76, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 76 (by decide)))

theorem fz2_113_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨77, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 77 (by decide)))

theorem fz2_113_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨78, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 78 (by decide)))

theorem fz2_113_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨79, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 79 (by decide)))

theorem fz2_113_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨80, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 80 (by decide)))

theorem fz2_113_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨81, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 81 (by decide)))

theorem fz2_113_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨82, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 82 (by decide)))

theorem fz2_113_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨83, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 83 (by decide)))

theorem fz2_113_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨84, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 84 (by decide)))

theorem fz2_113_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨85, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 85 (by decide)))

theorem fz2_113_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨86, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 86 (by decide)))

theorem fz2_113_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨87, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 87 (by decide)))

theorem fz2_113_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨88, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 88 (by decide)))

theorem fz2_113_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨89, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 89 (by decide)))

theorem fz2_113_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨90, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 90 (by decide)))

theorem fz2_113_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨91, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 91 (by decide)))

theorem fz2_113_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨92, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 92 (by decide)))

theorem fz2_113_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨93, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 93 (by decide)))

theorem fz2_113_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨94, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 94 (by decide)))

theorem fz2_113_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨95, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 95 (by decide)))

theorem fz2_113_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨96, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 96 (by decide)))

theorem fz2_113_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨97, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 97 (by decide)))

theorem fz2_113_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨98, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 98 (by decide)))

theorem fz2_113_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨99, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 99 (by decide)))

theorem fz2_113_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨100, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 100 (by decide)))

theorem fz2_113_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨101, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 101 (by decide)))

theorem fz2_113_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨102, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 102 (by decide)))

theorem fz2_113_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨103, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 103 (by decide)))

theorem fz2_113_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨104, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 104 (by decide)))

theorem fz2_113_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨105, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 105 (by decide)))

theorem fz2_113_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨106, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 106 (by decide)))

theorem fz2_113_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨107, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 107 (by decide)))

theorem fz2_113_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨108, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 108 (by decide)))

theorem fz2_113_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨109, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 109 (by decide)))

theorem fz2_113_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨110, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 110 (by decide)))

theorem fz2_113_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨111, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 111 (by decide)))

theorem fz2_113_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨112, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 112 (by decide)))

theorem fz2_113_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨114, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 114 (by decide)))

theorem fz2_113_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK113)) = 0 :=
  Q2.repsFixedCard2 rK113 ⟨115, by decide⟩ Q2.R113_2 Q2.hpxR113_2 Q2.hcardq113_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_113) 115 (by decide)))

theorem fixz1_114 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK114) (retConj 1 (R114 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_114_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨1, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 1 (by decide)))

theorem fz1_114_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨2, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 2 (by decide)))

theorem fz1_114_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨3, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 3 (by decide)))

theorem fz1_114_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨4, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 4 (by decide)))

theorem fz1_114_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨5, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 5 (by decide)))

theorem fz1_114_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨6, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 6 (by decide)))

theorem fz1_114_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨7, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 7 (by decide)))

theorem fz1_114_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨8, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 8 (by decide)))

theorem fz1_114_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨9, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 9 (by decide)))

theorem fz1_114_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨11, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 11 (by decide)))

theorem fz1_114_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨13, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 13 (by decide)))

theorem fz1_114_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨14, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 14 (by decide)))

theorem fz1_114_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨15, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 15 (by decide)))

theorem fz1_114_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨16, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 16 (by decide)))

theorem fz1_114_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨17, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 17 (by decide)))

theorem fz1_114_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨18, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 18 (by decide)))

theorem fz1_114_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨19, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 19 (by decide)))

theorem fz1_114_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨20, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 20 (by decide)))

theorem fz1_114_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨21, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 21 (by decide)))

theorem fz1_114_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨22, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 22 (by decide)))

theorem fz1_114_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨23, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 23 (by decide)))

theorem fz1_114_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨24, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 24 (by decide)))

theorem fz1_114_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨25, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 25 (by decide)))

theorem fz1_114_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨26, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 26 (by decide)))

theorem fz1_114_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨27, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 27 (by decide)))

theorem fz1_114_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨28, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 28 (by decide)))

theorem fz1_114_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨29, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 29 (by decide)))

theorem fz1_114_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨30, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 30 (by decide)))

theorem fz1_114_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨31, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 31 (by decide)))

theorem fz1_114_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨32, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 32 (by decide)))

theorem fz1_114_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨33, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 33 (by decide)))

theorem fz1_114_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨34, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 34 (by decide)))

theorem fz1_114_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨35, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 35 (by decide)))

theorem fz1_114_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨36, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 36 (by decide)))

theorem fz1_114_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨37, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 37 (by decide)))

theorem fz1_114_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨38, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 38 (by decide)))

theorem fz1_114_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨39, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 39 (by decide)))

theorem fz1_114_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨40, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 40 (by decide)))

theorem fz1_114_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨41, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 41 (by decide)))

theorem fz1_114_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨42, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 42 (by decide)))

theorem fz1_114_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨43, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 43 (by decide)))

theorem fz1_114_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨44, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 44 (by decide)))

theorem fz1_114_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨45, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 45 (by decide)))

theorem fz1_114_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨46, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 46 (by decide)))

theorem fz1_114_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨47, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 47 (by decide)))

theorem fz1_114_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨48, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 48 (by decide)))

theorem fz1_114_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨49, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 49 (by decide)))

theorem fz1_114_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨50, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 50 (by decide)))

theorem fz1_114_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨51, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 51 (by decide)))

theorem fz1_114_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨54, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 54 (by decide)))

theorem fz1_114_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨55, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 55 (by decide)))

theorem fz1_114_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨56, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 56 (by decide)))

theorem fz1_114_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨57, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 57 (by decide)))

theorem fz1_114_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨58, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 58 (by decide)))

theorem fz1_114_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨59, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 59 (by decide)))

theorem fz1_114_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨60, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 60 (by decide)))

theorem fz1_114_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨61, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 61 (by decide)))

theorem fz1_114_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨62, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 62 (by decide)))

theorem fz1_114_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨63, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 63 (by decide)))

theorem fz1_114_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨64, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 64 (by decide)))

theorem fz1_114_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨65, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 65 (by decide)))

theorem fz1_114_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨66, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 66 (by decide)))

theorem fz1_114_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨67, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 67 (by decide)))

theorem fz1_114_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨68, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 68 (by decide)))

theorem fz1_114_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨69, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 69 (by decide)))

theorem fz1_114_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨70, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 70 (by decide)))

theorem fz1_114_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨71, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 71 (by decide)))

theorem fz1_114_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨72, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 72 (by decide)))

theorem fz1_114_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨73, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 73 (by decide)))

theorem fz1_114_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨74, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 74 (by decide)))

theorem fz1_114_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨75, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 75 (by decide)))

theorem fz1_114_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨76, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 76 (by decide)))

theorem fz1_114_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨77, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 77 (by decide)))

theorem fz1_114_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨78, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 78 (by decide)))

theorem fz1_114_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨79, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 79 (by decide)))

theorem fz1_114_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨80, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 80 (by decide)))

theorem fz1_114_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨81, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 81 (by decide)))

theorem fz1_114_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨82, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 82 (by decide)))

theorem fz1_114_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨83, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 83 (by decide)))

theorem fz1_114_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨84, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 84 (by decide)))

theorem fz1_114_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨85, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 85 (by decide)))

theorem fz1_114_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨86, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 86 (by decide)))

theorem fz1_114_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨87, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 87 (by decide)))

theorem fz1_114_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨88, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 88 (by decide)))

theorem fz1_114_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨89, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 89 (by decide)))

theorem fz1_114_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨90, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 90 (by decide)))

theorem fz1_114_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨91, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 91 (by decide)))

theorem fz1_114_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨92, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 92 (by decide)))

theorem fz1_114_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨93, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 93 (by decide)))

theorem fz1_114_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨94, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 94 (by decide)))

theorem fz1_114_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨95, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 95 (by decide)))

theorem fz1_114_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨96, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 96 (by decide)))

theorem fz1_114_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨97, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 97 (by decide)))

theorem fz1_114_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨98, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 98 (by decide)))

theorem fz1_114_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨99, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 99 (by decide)))

theorem fz1_114_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨100, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 100 (by decide)))

theorem fz1_114_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨101, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 101 (by decide)))

theorem fz1_114_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨102, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 102 (by decide)))

theorem fz1_114_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨103, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 103 (by decide)))

theorem fz1_114_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨104, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 104 (by decide)))

theorem fz1_114_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨105, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 105 (by decide)))

theorem fz1_114_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨106, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 106 (by decide)))

theorem fz1_114_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨107, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 107 (by decide)))

theorem fz1_114_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨108, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 108 (by decide)))

theorem fz1_114_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨109, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 109 (by decide)))

theorem fz1_114_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨110, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 110 (by decide)))

theorem fz1_114_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨111, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 111 (by decide)))

theorem fz1_114_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨112, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 112 (by decide)))

theorem fz1_114_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨113, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 113 (by decide)))

theorem fz1_114_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK114)) = 0 :=
  repsFixedCard rK114 ⟨115, by decide⟩ R114 hpxR114 hcardq114
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_114) 115 (by decide)))

theorem fixz2_114 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK114) (retConj 2 (Q2.R114_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_114_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨1, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 1 (by decide)))

theorem fz2_114_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨2, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 2 (by decide)))

theorem fz2_114_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨3, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 3 (by decide)))

theorem fz2_114_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨4, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 4 (by decide)))

theorem fz2_114_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨5, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 5 (by decide)))

theorem fz2_114_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨6, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 6 (by decide)))

theorem fz2_114_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨7, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 7 (by decide)))

theorem fz2_114_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨8, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 8 (by decide)))

theorem fz2_114_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨9, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 9 (by decide)))

theorem fz2_114_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨11, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 11 (by decide)))

theorem fz2_114_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨13, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 13 (by decide)))

theorem fz2_114_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨14, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 14 (by decide)))

theorem fz2_114_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨15, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 15 (by decide)))

theorem fz2_114_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨16, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 16 (by decide)))

theorem fz2_114_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨17, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 17 (by decide)))

theorem fz2_114_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨18, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 18 (by decide)))

theorem fz2_114_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨19, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 19 (by decide)))

theorem fz2_114_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨20, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 20 (by decide)))

theorem fz2_114_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨21, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 21 (by decide)))

theorem fz2_114_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨22, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 22 (by decide)))

theorem fz2_114_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨23, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 23 (by decide)))

theorem fz2_114_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨24, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 24 (by decide)))

theorem fz2_114_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨25, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 25 (by decide)))

theorem fz2_114_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨26, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 26 (by decide)))

theorem fz2_114_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨27, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 27 (by decide)))

theorem fz2_114_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨28, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 28 (by decide)))

theorem fz2_114_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨29, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 29 (by decide)))

theorem fz2_114_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨30, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 30 (by decide)))

theorem fz2_114_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨31, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 31 (by decide)))

theorem fz2_114_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨32, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 32 (by decide)))

theorem fz2_114_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨33, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 33 (by decide)))

theorem fz2_114_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨34, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 34 (by decide)))

theorem fz2_114_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨35, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 35 (by decide)))

theorem fz2_114_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨36, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 36 (by decide)))

theorem fz2_114_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨37, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 37 (by decide)))

theorem fz2_114_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨38, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 38 (by decide)))

theorem fz2_114_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨39, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 39 (by decide)))

theorem fz2_114_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨40, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 40 (by decide)))

theorem fz2_114_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨41, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 41 (by decide)))

theorem fz2_114_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨42, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 42 (by decide)))

theorem fz2_114_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨43, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 43 (by decide)))

theorem fz2_114_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨44, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 44 (by decide)))

theorem fz2_114_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨45, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 45 (by decide)))

theorem fz2_114_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨46, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 46 (by decide)))

theorem fz2_114_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨47, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 47 (by decide)))

theorem fz2_114_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨48, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 48 (by decide)))

theorem fz2_114_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨49, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 49 (by decide)))

theorem fz2_114_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨50, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 50 (by decide)))

theorem fz2_114_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨51, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 51 (by decide)))

theorem fz2_114_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨54, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 54 (by decide)))

theorem fz2_114_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨55, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 55 (by decide)))

theorem fz2_114_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨56, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 56 (by decide)))

theorem fz2_114_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨57, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 57 (by decide)))

theorem fz2_114_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨58, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 58 (by decide)))

theorem fz2_114_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨59, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 59 (by decide)))

theorem fz2_114_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨60, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 60 (by decide)))

theorem fz2_114_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨61, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 61 (by decide)))

theorem fz2_114_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨62, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 62 (by decide)))

theorem fz2_114_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨63, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 63 (by decide)))

theorem fz2_114_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨64, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 64 (by decide)))

theorem fz2_114_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨65, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 65 (by decide)))

theorem fz2_114_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨66, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 66 (by decide)))

theorem fz2_114_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨67, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 67 (by decide)))

theorem fz2_114_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨68, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 68 (by decide)))

theorem fz2_114_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨69, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 69 (by decide)))

theorem fz2_114_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨70, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 70 (by decide)))

theorem fz2_114_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨71, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 71 (by decide)))

theorem fz2_114_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨72, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 72 (by decide)))

theorem fz2_114_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨73, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 73 (by decide)))

theorem fz2_114_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨74, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 74 (by decide)))

theorem fz2_114_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨75, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 75 (by decide)))

theorem fz2_114_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨76, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 76 (by decide)))

theorem fz2_114_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨77, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 77 (by decide)))

theorem fz2_114_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨78, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 78 (by decide)))

theorem fz2_114_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨79, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 79 (by decide)))

theorem fz2_114_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨80, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 80 (by decide)))

theorem fz2_114_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨81, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 81 (by decide)))

theorem fz2_114_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨82, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 82 (by decide)))

theorem fz2_114_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨83, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 83 (by decide)))

theorem fz2_114_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨84, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 84 (by decide)))

theorem fz2_114_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨85, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 85 (by decide)))

theorem fz2_114_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨86, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 86 (by decide)))

theorem fz2_114_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨87, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 87 (by decide)))

theorem fz2_114_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨88, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 88 (by decide)))

theorem fz2_114_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨89, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 89 (by decide)))

theorem fz2_114_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨90, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 90 (by decide)))

theorem fz2_114_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨91, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 91 (by decide)))

theorem fz2_114_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨92, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 92 (by decide)))

theorem fz2_114_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨93, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 93 (by decide)))

theorem fz2_114_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨94, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 94 (by decide)))

theorem fz2_114_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨95, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 95 (by decide)))

theorem fz2_114_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨96, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 96 (by decide)))

theorem fz2_114_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨97, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 97 (by decide)))

theorem fz2_114_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨98, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 98 (by decide)))

theorem fz2_114_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨99, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 99 (by decide)))

theorem fz2_114_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨100, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 100 (by decide)))

theorem fz2_114_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨101, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 101 (by decide)))

theorem fz2_114_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨102, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 102 (by decide)))

theorem fz2_114_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨103, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 103 (by decide)))

theorem fz2_114_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨104, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 104 (by decide)))

theorem fz2_114_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨105, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 105 (by decide)))

theorem fz2_114_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨106, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 106 (by decide)))

theorem fz2_114_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨107, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 107 (by decide)))

theorem fz2_114_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨108, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 108 (by decide)))

theorem fz2_114_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨109, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 109 (by decide)))

theorem fz2_114_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨110, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 110 (by decide)))

theorem fz2_114_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨111, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 111 (by decide)))

theorem fz2_114_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨112, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 112 (by decide)))

theorem fz2_114_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨113, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 113 (by decide)))

theorem fz2_114_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK114)) = 0 :=
  Q2.repsFixedCard2 rK114 ⟨115, by decide⟩ Q2.R114_2 Q2.hpxR114_2 Q2.hcardq114_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_114) 115 (by decide)))

end LeanDring.P5Presentation
