/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C024

/-!
# Species-table cells, off-support emptiness certificates, chunk 81

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

theorem fixz1_109 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK109) (retConj 1 (R109 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_109_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨1, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 1 (by decide)))

theorem fz1_109_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨2, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 2 (by decide)))

theorem fz1_109_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨3, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 3 (by decide)))

theorem fz1_109_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨4, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 4 (by decide)))

theorem fz1_109_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨5, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 5 (by decide)))

theorem fz1_109_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨6, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 6 (by decide)))

theorem fz1_109_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨7, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 7 (by decide)))

theorem fz1_109_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨8, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 8 (by decide)))

theorem fz1_109_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨9, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 9 (by decide)))

theorem fz1_109_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨11, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 11 (by decide)))

theorem fz1_109_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨13, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 13 (by decide)))

theorem fz1_109_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨14, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 14 (by decide)))

theorem fz1_109_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨15, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 15 (by decide)))

theorem fz1_109_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨16, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 16 (by decide)))

theorem fz1_109_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨17, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 17 (by decide)))

theorem fz1_109_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨18, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 18 (by decide)))

theorem fz1_109_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨19, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 19 (by decide)))

theorem fz1_109_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨20, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 20 (by decide)))

theorem fz1_109_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨21, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 21 (by decide)))

theorem fz1_109_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨22, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 22 (by decide)))

theorem fz1_109_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨23, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 23 (by decide)))

theorem fz1_109_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨24, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 24 (by decide)))

theorem fz1_109_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨25, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 25 (by decide)))

theorem fz1_109_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨26, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 26 (by decide)))

theorem fz1_109_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨27, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 27 (by decide)))

theorem fz1_109_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨28, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 28 (by decide)))

theorem fz1_109_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨29, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 29 (by decide)))

theorem fz1_109_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨30, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 30 (by decide)))

theorem fz1_109_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨31, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 31 (by decide)))

theorem fz1_109_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨32, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 32 (by decide)))

theorem fz1_109_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨33, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 33 (by decide)))

theorem fz1_109_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨34, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 34 (by decide)))

theorem fz1_109_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨35, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 35 (by decide)))

theorem fz1_109_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨36, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 36 (by decide)))

theorem fz1_109_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨37, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 37 (by decide)))

theorem fz1_109_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨38, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 38 (by decide)))

theorem fz1_109_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨39, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 39 (by decide)))

theorem fz1_109_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨40, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 40 (by decide)))

theorem fz1_109_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨41, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 41 (by decide)))

theorem fz1_109_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨42, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 42 (by decide)))

theorem fz1_109_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨43, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 43 (by decide)))

theorem fz1_109_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨44, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 44 (by decide)))

theorem fz1_109_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨45, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 45 (by decide)))

theorem fz1_109_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨46, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 46 (by decide)))

theorem fz1_109_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨48, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 48 (by decide)))

theorem fz1_109_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨49, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 49 (by decide)))

theorem fz1_109_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨50, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 50 (by decide)))

theorem fz1_109_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨51, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 51 (by decide)))

theorem fz1_109_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨52, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 52 (by decide)))

theorem fz1_109_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨54, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 54 (by decide)))

theorem fz1_109_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨55, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 55 (by decide)))

theorem fz1_109_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨56, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 56 (by decide)))

theorem fz1_109_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨57, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 57 (by decide)))

theorem fz1_109_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨58, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 58 (by decide)))

theorem fz1_109_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨59, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 59 (by decide)))

theorem fz1_109_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨60, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 60 (by decide)))

theorem fz1_109_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨61, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 61 (by decide)))

theorem fz1_109_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨62, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 62 (by decide)))

theorem fz1_109_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨63, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 63 (by decide)))

theorem fz1_109_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨64, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 64 (by decide)))

theorem fz1_109_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨65, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 65 (by decide)))

theorem fz1_109_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨66, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 66 (by decide)))

theorem fz1_109_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨67, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 67 (by decide)))

theorem fz1_109_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨68, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 68 (by decide)))

theorem fz1_109_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨69, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 69 (by decide)))

theorem fz1_109_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨70, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 70 (by decide)))

theorem fz1_109_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨71, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 71 (by decide)))

theorem fz1_109_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨72, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 72 (by decide)))

theorem fz1_109_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨73, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 73 (by decide)))

theorem fz1_109_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨74, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 74 (by decide)))

theorem fz1_109_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨75, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 75 (by decide)))

theorem fz1_109_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨76, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 76 (by decide)))

theorem fz1_109_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨77, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 77 (by decide)))

theorem fz1_109_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨78, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 78 (by decide)))

theorem fz1_109_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨79, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 79 (by decide)))

theorem fz1_109_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨80, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 80 (by decide)))

theorem fz1_109_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨81, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 81 (by decide)))

theorem fz1_109_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨82, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 82 (by decide)))

theorem fz1_109_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨83, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 83 (by decide)))

theorem fz1_109_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨84, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 84 (by decide)))

theorem fz1_109_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨85, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 85 (by decide)))

theorem fz1_109_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨86, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 86 (by decide)))

theorem fz1_109_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨87, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 87 (by decide)))

theorem fz1_109_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨88, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 88 (by decide)))

theorem fz1_109_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨89, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 89 (by decide)))

theorem fz1_109_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨90, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 90 (by decide)))

theorem fz1_109_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨91, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 91 (by decide)))

theorem fz1_109_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨92, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 92 (by decide)))

theorem fz1_109_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨93, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 93 (by decide)))

theorem fz1_109_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨94, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 94 (by decide)))

theorem fz1_109_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨95, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 95 (by decide)))

theorem fz1_109_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨96, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 96 (by decide)))

theorem fz1_109_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨97, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 97 (by decide)))

theorem fz1_109_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨98, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 98 (by decide)))

theorem fz1_109_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨99, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 99 (by decide)))

theorem fz1_109_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨100, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 100 (by decide)))

theorem fz1_109_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨101, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 101 (by decide)))

theorem fz1_109_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨102, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 102 (by decide)))

theorem fz1_109_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨103, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 103 (by decide)))

theorem fz1_109_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨104, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 104 (by decide)))

theorem fz1_109_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨105, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 105 (by decide)))

theorem fz1_109_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨106, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 106 (by decide)))

theorem fz1_109_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨107, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 107 (by decide)))

theorem fz1_109_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨108, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 108 (by decide)))

theorem fz1_109_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨110, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 110 (by decide)))

theorem fz1_109_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨111, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 111 (by decide)))

theorem fz1_109_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨112, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 112 (by decide)))

theorem fz1_109_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨113, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 113 (by decide)))

theorem fz1_109_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨114, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 114 (by decide)))

theorem fz1_109_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK109)) = 0 :=
  repsFixedCard rK109 ⟨115, by decide⟩ R109 hpxR109 hcardq109
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_109) 115 (by decide)))

theorem fixz2_109 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK109) (retConj 2 (Q2.R109_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_109_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨1, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 1 (by decide)))

theorem fz2_109_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨2, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 2 (by decide)))

theorem fz2_109_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨3, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 3 (by decide)))

theorem fz2_109_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨4, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 4 (by decide)))

theorem fz2_109_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨5, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 5 (by decide)))

theorem fz2_109_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨6, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 6 (by decide)))

theorem fz2_109_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨7, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 7 (by decide)))

theorem fz2_109_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨8, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 8 (by decide)))

theorem fz2_109_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨9, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 9 (by decide)))

theorem fz2_109_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨11, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 11 (by decide)))

theorem fz2_109_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨13, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 13 (by decide)))

theorem fz2_109_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨14, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 14 (by decide)))

theorem fz2_109_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨15, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 15 (by decide)))

theorem fz2_109_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨16, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 16 (by decide)))

theorem fz2_109_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨17, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 17 (by decide)))

theorem fz2_109_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨18, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 18 (by decide)))

theorem fz2_109_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨19, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 19 (by decide)))

theorem fz2_109_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨20, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 20 (by decide)))

theorem fz2_109_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨21, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 21 (by decide)))

theorem fz2_109_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨22, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 22 (by decide)))

theorem fz2_109_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨23, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 23 (by decide)))

theorem fz2_109_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨24, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 24 (by decide)))

theorem fz2_109_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨25, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 25 (by decide)))

theorem fz2_109_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨26, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 26 (by decide)))

theorem fz2_109_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨27, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 27 (by decide)))

theorem fz2_109_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨28, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 28 (by decide)))

theorem fz2_109_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨29, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 29 (by decide)))

theorem fz2_109_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨30, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 30 (by decide)))

theorem fz2_109_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨31, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 31 (by decide)))

theorem fz2_109_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨32, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 32 (by decide)))

theorem fz2_109_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨33, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 33 (by decide)))

theorem fz2_109_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨34, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 34 (by decide)))

theorem fz2_109_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨35, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 35 (by decide)))

theorem fz2_109_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨36, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 36 (by decide)))

theorem fz2_109_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨37, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 37 (by decide)))

theorem fz2_109_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨38, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 38 (by decide)))

theorem fz2_109_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨39, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 39 (by decide)))

theorem fz2_109_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨40, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 40 (by decide)))

theorem fz2_109_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨41, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 41 (by decide)))

theorem fz2_109_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨42, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 42 (by decide)))

theorem fz2_109_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨43, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 43 (by decide)))

theorem fz2_109_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨44, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 44 (by decide)))

theorem fz2_109_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨45, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 45 (by decide)))

theorem fz2_109_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨46, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 46 (by decide)))

theorem fz2_109_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨48, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 48 (by decide)))

theorem fz2_109_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨49, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 49 (by decide)))

theorem fz2_109_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨50, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 50 (by decide)))

theorem fz2_109_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨51, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 51 (by decide)))

theorem fz2_109_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨52, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 52 (by decide)))

theorem fz2_109_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨54, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 54 (by decide)))

theorem fz2_109_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨55, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 55 (by decide)))

theorem fz2_109_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨56, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 56 (by decide)))

theorem fz2_109_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨57, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 57 (by decide)))

theorem fz2_109_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨58, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 58 (by decide)))

theorem fz2_109_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨59, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 59 (by decide)))

theorem fz2_109_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨60, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 60 (by decide)))

theorem fz2_109_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨61, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 61 (by decide)))

theorem fz2_109_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨62, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 62 (by decide)))

theorem fz2_109_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨63, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 63 (by decide)))

theorem fz2_109_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨64, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 64 (by decide)))

theorem fz2_109_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨65, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 65 (by decide)))

theorem fz2_109_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨66, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 66 (by decide)))

theorem fz2_109_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨67, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 67 (by decide)))

theorem fz2_109_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨68, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 68 (by decide)))

theorem fz2_109_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨69, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 69 (by decide)))

theorem fz2_109_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨70, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 70 (by decide)))

theorem fz2_109_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨71, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 71 (by decide)))

theorem fz2_109_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨72, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 72 (by decide)))

theorem fz2_109_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨73, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 73 (by decide)))

theorem fz2_109_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨74, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 74 (by decide)))

theorem fz2_109_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨75, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 75 (by decide)))

theorem fz2_109_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨76, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 76 (by decide)))

theorem fz2_109_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨77, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 77 (by decide)))

theorem fz2_109_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨78, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 78 (by decide)))

theorem fz2_109_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨79, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 79 (by decide)))

theorem fz2_109_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨80, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 80 (by decide)))

theorem fz2_109_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨81, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 81 (by decide)))

theorem fz2_109_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨82, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 82 (by decide)))

theorem fz2_109_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨83, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 83 (by decide)))

theorem fz2_109_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨84, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 84 (by decide)))

theorem fz2_109_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨85, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 85 (by decide)))

theorem fz2_109_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨86, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 86 (by decide)))

theorem fz2_109_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨87, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 87 (by decide)))

theorem fz2_109_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨88, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 88 (by decide)))

theorem fz2_109_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨89, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 89 (by decide)))

theorem fz2_109_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨90, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 90 (by decide)))

theorem fz2_109_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨91, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 91 (by decide)))

theorem fz2_109_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨92, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 92 (by decide)))

theorem fz2_109_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨93, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 93 (by decide)))

theorem fz2_109_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨94, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 94 (by decide)))

theorem fz2_109_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨95, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 95 (by decide)))

theorem fz2_109_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨96, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 96 (by decide)))

theorem fz2_109_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨97, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 97 (by decide)))

theorem fz2_109_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨98, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 98 (by decide)))

theorem fz2_109_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨99, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 99 (by decide)))

theorem fz2_109_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨100, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 100 (by decide)))

theorem fz2_109_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨101, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 101 (by decide)))

theorem fz2_109_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨102, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 102 (by decide)))

theorem fz2_109_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨103, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 103 (by decide)))

theorem fz2_109_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨104, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 104 (by decide)))

theorem fz2_109_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨105, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 105 (by decide)))

theorem fz2_109_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨106, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 106 (by decide)))

theorem fz2_109_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨107, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 107 (by decide)))

theorem fz2_109_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨108, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 108 (by decide)))

theorem fz2_109_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨110, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 110 (by decide)))

theorem fz2_109_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨111, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 111 (by decide)))

theorem fz2_109_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨112, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 112 (by decide)))

theorem fz2_109_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨113, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 113 (by decide)))

theorem fz2_109_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨114, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 114 (by decide)))

theorem fz2_109_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK109)) = 0 :=
  Q2.repsFixedCard2 rK109 ⟨115, by decide⟩ Q2.R109_2 Q2.hpxR109_2 Q2.hcardq109_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_109) 115 (by decide)))

theorem fixz1_110 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK110) (retConj 1 (R110 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_110_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨1, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 1 (by decide)))

theorem fz1_110_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨2, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 2 (by decide)))

theorem fz1_110_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨3, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 3 (by decide)))

theorem fz1_110_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨4, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 4 (by decide)))

theorem fz1_110_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨5, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 5 (by decide)))

theorem fz1_110_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨6, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 6 (by decide)))

theorem fz1_110_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨7, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 7 (by decide)))

theorem fz1_110_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨8, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 8 (by decide)))

theorem fz1_110_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨9, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 9 (by decide)))

theorem fz1_110_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨11, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 11 (by decide)))

theorem fz1_110_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨13, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 13 (by decide)))

theorem fz1_110_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨14, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 14 (by decide)))

theorem fz1_110_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨15, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 15 (by decide)))

theorem fz1_110_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨16, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 16 (by decide)))

theorem fz1_110_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨17, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 17 (by decide)))

theorem fz1_110_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨18, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 18 (by decide)))

theorem fz1_110_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨19, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 19 (by decide)))

theorem fz1_110_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨20, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 20 (by decide)))

theorem fz1_110_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨21, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 21 (by decide)))

theorem fz1_110_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨22, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 22 (by decide)))

theorem fz1_110_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨23, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 23 (by decide)))

theorem fz1_110_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨24, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 24 (by decide)))

theorem fz1_110_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨25, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 25 (by decide)))

theorem fz1_110_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨26, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 26 (by decide)))

theorem fz1_110_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨27, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 27 (by decide)))

theorem fz1_110_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨28, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 28 (by decide)))

theorem fz1_110_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨29, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 29 (by decide)))

theorem fz1_110_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨30, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 30 (by decide)))

theorem fz1_110_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨31, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 31 (by decide)))

theorem fz1_110_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨32, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 32 (by decide)))

theorem fz1_110_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨33, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 33 (by decide)))

theorem fz1_110_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨34, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 34 (by decide)))

theorem fz1_110_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨35, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 35 (by decide)))

theorem fz1_110_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨36, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 36 (by decide)))

theorem fz1_110_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨37, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 37 (by decide)))

theorem fz1_110_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨38, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 38 (by decide)))

theorem fz1_110_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨39, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 39 (by decide)))

theorem fz1_110_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨40, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 40 (by decide)))

theorem fz1_110_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨41, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 41 (by decide)))

theorem fz1_110_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨42, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 42 (by decide)))

theorem fz1_110_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨43, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 43 (by decide)))

theorem fz1_110_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨44, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 44 (by decide)))

theorem fz1_110_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨45, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 45 (by decide)))

theorem fz1_110_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨46, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 46 (by decide)))

theorem fz1_110_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨47, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 47 (by decide)))

theorem fz1_110_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨49, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 49 (by decide)))

theorem fz1_110_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨50, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 50 (by decide)))

theorem fz1_110_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨51, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 51 (by decide)))

theorem fz1_110_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨52, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 52 (by decide)))

theorem fz1_110_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨54, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 54 (by decide)))

theorem fz1_110_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨55, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 55 (by decide)))

theorem fz1_110_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨56, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 56 (by decide)))

theorem fz1_110_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨57, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 57 (by decide)))

theorem fz1_110_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨58, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 58 (by decide)))

theorem fz1_110_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨59, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 59 (by decide)))

theorem fz1_110_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨60, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 60 (by decide)))

theorem fz1_110_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨61, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 61 (by decide)))

theorem fz1_110_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨62, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 62 (by decide)))

theorem fz1_110_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨63, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 63 (by decide)))

theorem fz1_110_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨64, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 64 (by decide)))

theorem fz1_110_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨65, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 65 (by decide)))

theorem fz1_110_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨66, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 66 (by decide)))

theorem fz1_110_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨67, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 67 (by decide)))

theorem fz1_110_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨68, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 68 (by decide)))

theorem fz1_110_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨69, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 69 (by decide)))

theorem fz1_110_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨70, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 70 (by decide)))

theorem fz1_110_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨71, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 71 (by decide)))

theorem fz1_110_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨72, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 72 (by decide)))

theorem fz1_110_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨73, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 73 (by decide)))

theorem fz1_110_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨74, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 74 (by decide)))

theorem fz1_110_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨75, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 75 (by decide)))

theorem fz1_110_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨76, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 76 (by decide)))

theorem fz1_110_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨77, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 77 (by decide)))

theorem fz1_110_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨78, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 78 (by decide)))

theorem fz1_110_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨79, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 79 (by decide)))

theorem fz1_110_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨80, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 80 (by decide)))

theorem fz1_110_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨81, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 81 (by decide)))

theorem fz1_110_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨82, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 82 (by decide)))

theorem fz1_110_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨83, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 83 (by decide)))

theorem fz1_110_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨84, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 84 (by decide)))

theorem fz1_110_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨85, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 85 (by decide)))

theorem fz1_110_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨86, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 86 (by decide)))

theorem fz1_110_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨87, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 87 (by decide)))

theorem fz1_110_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨88, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 88 (by decide)))

theorem fz1_110_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨89, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 89 (by decide)))

theorem fz1_110_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨90, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 90 (by decide)))

theorem fz1_110_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨91, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 91 (by decide)))

theorem fz1_110_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨92, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 92 (by decide)))

theorem fz1_110_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨93, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 93 (by decide)))

theorem fz1_110_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨94, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 94 (by decide)))

theorem fz1_110_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨95, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 95 (by decide)))

theorem fz1_110_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨96, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 96 (by decide)))

theorem fz1_110_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨97, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 97 (by decide)))

theorem fz1_110_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨98, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 98 (by decide)))

theorem fz1_110_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨99, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 99 (by decide)))

theorem fz1_110_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨100, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 100 (by decide)))

theorem fz1_110_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨101, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 101 (by decide)))

theorem fz1_110_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨102, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 102 (by decide)))

theorem fz1_110_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨103, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 103 (by decide)))

theorem fz1_110_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨104, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 104 (by decide)))

theorem fz1_110_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨105, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 105 (by decide)))

theorem fz1_110_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨106, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 106 (by decide)))

theorem fz1_110_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨107, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 107 (by decide)))

theorem fz1_110_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨108, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 108 (by decide)))

theorem fz1_110_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨109, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 109 (by decide)))

theorem fz1_110_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨111, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 111 (by decide)))

theorem fz1_110_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨112, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 112 (by decide)))

theorem fz1_110_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨113, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 113 (by decide)))

theorem fz1_110_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨114, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 114 (by decide)))

theorem fz1_110_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK110)) = 0 :=
  repsFixedCard rK110 ⟨115, by decide⟩ R110 hpxR110 hcardq110
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_110) 115 (by decide)))

theorem fixz2_110 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK110) (retConj 2 (Q2.R110_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_110_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨1, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 1 (by decide)))

theorem fz2_110_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨2, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 2 (by decide)))

theorem fz2_110_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨3, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 3 (by decide)))

theorem fz2_110_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨4, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 4 (by decide)))

theorem fz2_110_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨5, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 5 (by decide)))

theorem fz2_110_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨6, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 6 (by decide)))

theorem fz2_110_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨7, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 7 (by decide)))

theorem fz2_110_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨8, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 8 (by decide)))

theorem fz2_110_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨9, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 9 (by decide)))

theorem fz2_110_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨11, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 11 (by decide)))

theorem fz2_110_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨13, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 13 (by decide)))

theorem fz2_110_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨14, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 14 (by decide)))

theorem fz2_110_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨15, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 15 (by decide)))

theorem fz2_110_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨16, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 16 (by decide)))

theorem fz2_110_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨17, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 17 (by decide)))

theorem fz2_110_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨18, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 18 (by decide)))

theorem fz2_110_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨19, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 19 (by decide)))

theorem fz2_110_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨20, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 20 (by decide)))

theorem fz2_110_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨21, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 21 (by decide)))

theorem fz2_110_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨22, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 22 (by decide)))

theorem fz2_110_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨23, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 23 (by decide)))

theorem fz2_110_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨24, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 24 (by decide)))

theorem fz2_110_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨25, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 25 (by decide)))

theorem fz2_110_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨26, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 26 (by decide)))

theorem fz2_110_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨27, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 27 (by decide)))

theorem fz2_110_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨28, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 28 (by decide)))

theorem fz2_110_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨29, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 29 (by decide)))

theorem fz2_110_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨30, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 30 (by decide)))

theorem fz2_110_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨31, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 31 (by decide)))

theorem fz2_110_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨32, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 32 (by decide)))

theorem fz2_110_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨33, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 33 (by decide)))

theorem fz2_110_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨34, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 34 (by decide)))

theorem fz2_110_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨35, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 35 (by decide)))

theorem fz2_110_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨36, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 36 (by decide)))

theorem fz2_110_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨37, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 37 (by decide)))

theorem fz2_110_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨38, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 38 (by decide)))

theorem fz2_110_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨39, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 39 (by decide)))

theorem fz2_110_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨40, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 40 (by decide)))

theorem fz2_110_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨41, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 41 (by decide)))

theorem fz2_110_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨42, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 42 (by decide)))

theorem fz2_110_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨43, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 43 (by decide)))

theorem fz2_110_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨44, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 44 (by decide)))

theorem fz2_110_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨45, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 45 (by decide)))

theorem fz2_110_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨46, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 46 (by decide)))

theorem fz2_110_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨47, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 47 (by decide)))

theorem fz2_110_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨49, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 49 (by decide)))

theorem fz2_110_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨50, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 50 (by decide)))

theorem fz2_110_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨51, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 51 (by decide)))

theorem fz2_110_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨52, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 52 (by decide)))

theorem fz2_110_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨54, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 54 (by decide)))

theorem fz2_110_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨55, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 55 (by decide)))

theorem fz2_110_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨56, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 56 (by decide)))

theorem fz2_110_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨57, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 57 (by decide)))

theorem fz2_110_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨58, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 58 (by decide)))

theorem fz2_110_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨59, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 59 (by decide)))

theorem fz2_110_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨60, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 60 (by decide)))

theorem fz2_110_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨61, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 61 (by decide)))

theorem fz2_110_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨62, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 62 (by decide)))

theorem fz2_110_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨63, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 63 (by decide)))

theorem fz2_110_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨64, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 64 (by decide)))

theorem fz2_110_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨65, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 65 (by decide)))

theorem fz2_110_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨66, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 66 (by decide)))

theorem fz2_110_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨67, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 67 (by decide)))

theorem fz2_110_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨68, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 68 (by decide)))

theorem fz2_110_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨69, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 69 (by decide)))

theorem fz2_110_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨70, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 70 (by decide)))

theorem fz2_110_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨71, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 71 (by decide)))

theorem fz2_110_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨72, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 72 (by decide)))

theorem fz2_110_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨73, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 73 (by decide)))

theorem fz2_110_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨74, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 74 (by decide)))

theorem fz2_110_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨75, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 75 (by decide)))

theorem fz2_110_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨76, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 76 (by decide)))

theorem fz2_110_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨77, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 77 (by decide)))

theorem fz2_110_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨78, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 78 (by decide)))

theorem fz2_110_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨79, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 79 (by decide)))

theorem fz2_110_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨80, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 80 (by decide)))

theorem fz2_110_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨81, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 81 (by decide)))

theorem fz2_110_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨82, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 82 (by decide)))

theorem fz2_110_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨83, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 83 (by decide)))

theorem fz2_110_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨84, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 84 (by decide)))

theorem fz2_110_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨85, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 85 (by decide)))

theorem fz2_110_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨86, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 86 (by decide)))

theorem fz2_110_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨87, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 87 (by decide)))

theorem fz2_110_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨88, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 88 (by decide)))

theorem fz2_110_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨89, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 89 (by decide)))

theorem fz2_110_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨90, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 90 (by decide)))

theorem fz2_110_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨91, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 91 (by decide)))

theorem fz2_110_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨92, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 92 (by decide)))

theorem fz2_110_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨93, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 93 (by decide)))

theorem fz2_110_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨94, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 94 (by decide)))

theorem fz2_110_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨95, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 95 (by decide)))

theorem fz2_110_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨96, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 96 (by decide)))

theorem fz2_110_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨97, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 97 (by decide)))

theorem fz2_110_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨98, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 98 (by decide)))

theorem fz2_110_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨99, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 99 (by decide)))

theorem fz2_110_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨100, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 100 (by decide)))

theorem fz2_110_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨101, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 101 (by decide)))

theorem fz2_110_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨102, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 102 (by decide)))

theorem fz2_110_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨103, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 103 (by decide)))

theorem fz2_110_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨104, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 104 (by decide)))

theorem fz2_110_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨105, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 105 (by decide)))

theorem fz2_110_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨106, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 106 (by decide)))

theorem fz2_110_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨107, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 107 (by decide)))

theorem fz2_110_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨108, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 108 (by decide)))

theorem fz2_110_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨109, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 109 (by decide)))

theorem fz2_110_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨111, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 111 (by decide)))

theorem fz2_110_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨112, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 112 (by decide)))

theorem fz2_110_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨113, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 113 (by decide)))

theorem fz2_110_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨114, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 114 (by decide)))

theorem fz2_110_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK110)) = 0 :=
  Q2.repsFixedCard2 rK110 ⟨115, by decide⟩ Q2.R110_2 Q2.hpxR110_2 Q2.hcardq110_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_110) 115 (by decide)))

end LeanDring.P5Presentation
