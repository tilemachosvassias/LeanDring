/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C022

/-!
# Species-table cells, off-support emptiness certificates, chunk 75

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

theorem fixz1_97 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK97) (retConj 1 (R97 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_97_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨1, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 1 (by decide)))

theorem fz1_97_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨2, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 2 (by decide)))

theorem fz1_97_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨3, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 3 (by decide)))

theorem fz1_97_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨4, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 4 (by decide)))

theorem fz1_97_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨5, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 5 (by decide)))

theorem fz1_97_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨6, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 6 (by decide)))

theorem fz1_97_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨7, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 7 (by decide)))

theorem fz1_97_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨8, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 8 (by decide)))

theorem fz1_97_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨9, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 9 (by decide)))

theorem fz1_97_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨11, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 11 (by decide)))

theorem fz1_97_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨13, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 13 (by decide)))

theorem fz1_97_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨14, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 14 (by decide)))

theorem fz1_97_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨15, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 15 (by decide)))

theorem fz1_97_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨16, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 16 (by decide)))

theorem fz1_97_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨17, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 17 (by decide)))

theorem fz1_97_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨18, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 18 (by decide)))

theorem fz1_97_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨19, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 19 (by decide)))

theorem fz1_97_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨20, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 20 (by decide)))

theorem fz1_97_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨21, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 21 (by decide)))

theorem fz1_97_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨22, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 22 (by decide)))

theorem fz1_97_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨23, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 23 (by decide)))

theorem fz1_97_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨24, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 24 (by decide)))

theorem fz1_97_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨25, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 25 (by decide)))

theorem fz1_97_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨26, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 26 (by decide)))

theorem fz1_97_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨27, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 27 (by decide)))

theorem fz1_97_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨28, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 28 (by decide)))

theorem fz1_97_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨29, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 29 (by decide)))

theorem fz1_97_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨30, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 30 (by decide)))

theorem fz1_97_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨31, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 31 (by decide)))

theorem fz1_97_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨32, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 32 (by decide)))

theorem fz1_97_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨33, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 33 (by decide)))

theorem fz1_97_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨34, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 34 (by decide)))

theorem fz1_97_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨36, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 36 (by decide)))

theorem fz1_97_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨37, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 37 (by decide)))

theorem fz1_97_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨38, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 38 (by decide)))

theorem fz1_97_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨39, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 39 (by decide)))

theorem fz1_97_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨40, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 40 (by decide)))

theorem fz1_97_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨41, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 41 (by decide)))

theorem fz1_97_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨42, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 42 (by decide)))

theorem fz1_97_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨43, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 43 (by decide)))

theorem fz1_97_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨44, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 44 (by decide)))

theorem fz1_97_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨45, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 45 (by decide)))

theorem fz1_97_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨46, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 46 (by decide)))

theorem fz1_97_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨47, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 47 (by decide)))

theorem fz1_97_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨48, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 48 (by decide)))

theorem fz1_97_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨49, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 49 (by decide)))

theorem fz1_97_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨50, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 50 (by decide)))

theorem fz1_97_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨51, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 51 (by decide)))

theorem fz1_97_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨52, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 52 (by decide)))

theorem fz1_97_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨54, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 54 (by decide)))

theorem fz1_97_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨55, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 55 (by decide)))

theorem fz1_97_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨56, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 56 (by decide)))

theorem fz1_97_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨57, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 57 (by decide)))

theorem fz1_97_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨58, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 58 (by decide)))

theorem fz1_97_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨59, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 59 (by decide)))

theorem fz1_97_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨60, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 60 (by decide)))

theorem fz1_97_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨61, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 61 (by decide)))

theorem fz1_97_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨62, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 62 (by decide)))

theorem fz1_97_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨63, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 63 (by decide)))

theorem fz1_97_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨64, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 64 (by decide)))

theorem fz1_97_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨65, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 65 (by decide)))

theorem fz1_97_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨66, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 66 (by decide)))

theorem fz1_97_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨67, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 67 (by decide)))

theorem fz1_97_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨68, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 68 (by decide)))

theorem fz1_97_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨69, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 69 (by decide)))

theorem fz1_97_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨70, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 70 (by decide)))

theorem fz1_97_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨71, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 71 (by decide)))

theorem fz1_97_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨72, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 72 (by decide)))

theorem fz1_97_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨73, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 73 (by decide)))

theorem fz1_97_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨74, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 74 (by decide)))

theorem fz1_97_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨75, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 75 (by decide)))

theorem fz1_97_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨76, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 76 (by decide)))

theorem fz1_97_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨77, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 77 (by decide)))

theorem fz1_97_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨78, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 78 (by decide)))

theorem fz1_97_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨79, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 79 (by decide)))

theorem fz1_97_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨80, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 80 (by decide)))

theorem fz1_97_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨81, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 81 (by decide)))

theorem fz1_97_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨82, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 82 (by decide)))

theorem fz1_97_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨83, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 83 (by decide)))

theorem fz1_97_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨84, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 84 (by decide)))

theorem fz1_97_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨85, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 85 (by decide)))

theorem fz1_97_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨86, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 86 (by decide)))

theorem fz1_97_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨87, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 87 (by decide)))

theorem fz1_97_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨88, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 88 (by decide)))

theorem fz1_97_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨89, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 89 (by decide)))

theorem fz1_97_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨90, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 90 (by decide)))

theorem fz1_97_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨91, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 91 (by decide)))

theorem fz1_97_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨92, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 92 (by decide)))

theorem fz1_97_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨93, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 93 (by decide)))

theorem fz1_97_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨94, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 94 (by decide)))

theorem fz1_97_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨95, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 95 (by decide)))

theorem fz1_97_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨96, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 96 (by decide)))

theorem fz1_97_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨98, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 98 (by decide)))

theorem fz1_97_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨99, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 99 (by decide)))

theorem fz1_97_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨100, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 100 (by decide)))

theorem fz1_97_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨101, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 101 (by decide)))

theorem fz1_97_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨102, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 102 (by decide)))

theorem fz1_97_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨103, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 103 (by decide)))

theorem fz1_97_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨104, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 104 (by decide)))

theorem fz1_97_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨105, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 105 (by decide)))

theorem fz1_97_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨106, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 106 (by decide)))

theorem fz1_97_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨107, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 107 (by decide)))

theorem fz1_97_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨108, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 108 (by decide)))

theorem fz1_97_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨109, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 109 (by decide)))

theorem fz1_97_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨110, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 110 (by decide)))

theorem fz1_97_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨111, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 111 (by decide)))

theorem fz1_97_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨112, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 112 (by decide)))

theorem fz1_97_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨113, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 113 (by decide)))

theorem fz1_97_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨114, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 114 (by decide)))

theorem fz1_97_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK97)) = 0 :=
  repsFixedCard rK97 ⟨115, by decide⟩ R97 hpxR97 hcardq97
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_97) 115 (by decide)))

theorem fixz2_97 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK97) (retConj 2 (Q2.R97_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_97_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨1, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 1 (by decide)))

theorem fz2_97_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨2, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 2 (by decide)))

theorem fz2_97_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨3, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 3 (by decide)))

theorem fz2_97_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨4, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 4 (by decide)))

theorem fz2_97_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨5, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 5 (by decide)))

theorem fz2_97_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨6, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 6 (by decide)))

theorem fz2_97_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨7, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 7 (by decide)))

theorem fz2_97_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨8, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 8 (by decide)))

theorem fz2_97_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨9, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 9 (by decide)))

theorem fz2_97_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨11, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 11 (by decide)))

theorem fz2_97_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨13, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 13 (by decide)))

theorem fz2_97_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨14, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 14 (by decide)))

theorem fz2_97_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨15, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 15 (by decide)))

theorem fz2_97_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨16, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 16 (by decide)))

theorem fz2_97_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨17, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 17 (by decide)))

theorem fz2_97_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨18, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 18 (by decide)))

theorem fz2_97_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨19, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 19 (by decide)))

theorem fz2_97_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨20, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 20 (by decide)))

theorem fz2_97_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨21, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 21 (by decide)))

theorem fz2_97_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨22, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 22 (by decide)))

theorem fz2_97_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨23, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 23 (by decide)))

theorem fz2_97_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨24, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 24 (by decide)))

theorem fz2_97_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨25, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 25 (by decide)))

theorem fz2_97_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨26, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 26 (by decide)))

theorem fz2_97_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨27, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 27 (by decide)))

theorem fz2_97_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨28, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 28 (by decide)))

theorem fz2_97_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨29, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 29 (by decide)))

theorem fz2_97_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨30, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 30 (by decide)))

theorem fz2_97_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨31, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 31 (by decide)))

theorem fz2_97_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨32, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 32 (by decide)))

theorem fz2_97_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨33, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 33 (by decide)))

theorem fz2_97_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨34, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 34 (by decide)))

theorem fz2_97_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨36, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 36 (by decide)))

theorem fz2_97_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨37, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 37 (by decide)))

theorem fz2_97_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨38, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 38 (by decide)))

theorem fz2_97_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨39, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 39 (by decide)))

theorem fz2_97_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨40, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 40 (by decide)))

theorem fz2_97_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨41, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 41 (by decide)))

theorem fz2_97_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨42, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 42 (by decide)))

theorem fz2_97_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨43, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 43 (by decide)))

theorem fz2_97_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨44, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 44 (by decide)))

theorem fz2_97_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨45, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 45 (by decide)))

theorem fz2_97_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨46, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 46 (by decide)))

theorem fz2_97_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨47, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 47 (by decide)))

theorem fz2_97_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨48, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 48 (by decide)))

theorem fz2_97_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨49, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 49 (by decide)))

theorem fz2_97_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨50, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 50 (by decide)))

theorem fz2_97_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨51, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 51 (by decide)))

theorem fz2_97_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨52, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 52 (by decide)))

theorem fz2_97_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨54, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 54 (by decide)))

theorem fz2_97_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨55, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 55 (by decide)))

theorem fz2_97_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨56, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 56 (by decide)))

theorem fz2_97_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨57, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 57 (by decide)))

theorem fz2_97_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨58, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 58 (by decide)))

theorem fz2_97_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨59, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 59 (by decide)))

theorem fz2_97_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨60, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 60 (by decide)))

theorem fz2_97_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨61, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 61 (by decide)))

theorem fz2_97_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨62, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 62 (by decide)))

theorem fz2_97_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨63, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 63 (by decide)))

theorem fz2_97_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨64, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 64 (by decide)))

theorem fz2_97_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨65, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 65 (by decide)))

theorem fz2_97_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨66, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 66 (by decide)))

theorem fz2_97_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨67, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 67 (by decide)))

theorem fz2_97_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨68, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 68 (by decide)))

theorem fz2_97_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨69, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 69 (by decide)))

theorem fz2_97_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨70, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 70 (by decide)))

theorem fz2_97_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨71, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 71 (by decide)))

theorem fz2_97_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨72, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 72 (by decide)))

theorem fz2_97_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨73, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 73 (by decide)))

theorem fz2_97_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨74, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 74 (by decide)))

theorem fz2_97_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨75, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 75 (by decide)))

theorem fz2_97_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨76, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 76 (by decide)))

theorem fz2_97_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨77, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 77 (by decide)))

theorem fz2_97_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨78, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 78 (by decide)))

theorem fz2_97_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨79, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 79 (by decide)))

theorem fz2_97_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨80, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 80 (by decide)))

theorem fz2_97_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨81, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 81 (by decide)))

theorem fz2_97_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨82, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 82 (by decide)))

theorem fz2_97_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨83, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 83 (by decide)))

theorem fz2_97_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨84, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 84 (by decide)))

theorem fz2_97_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨85, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 85 (by decide)))

theorem fz2_97_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨86, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 86 (by decide)))

theorem fz2_97_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨87, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 87 (by decide)))

theorem fz2_97_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨88, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 88 (by decide)))

theorem fz2_97_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨89, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 89 (by decide)))

theorem fz2_97_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨90, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 90 (by decide)))

theorem fz2_97_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨91, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 91 (by decide)))

theorem fz2_97_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨92, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 92 (by decide)))

theorem fz2_97_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨93, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 93 (by decide)))

theorem fz2_97_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨94, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 94 (by decide)))

theorem fz2_97_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨95, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 95 (by decide)))

theorem fz2_97_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨96, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 96 (by decide)))

theorem fz2_97_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨98, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 98 (by decide)))

theorem fz2_97_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨99, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 99 (by decide)))

theorem fz2_97_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨100, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 100 (by decide)))

theorem fz2_97_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨101, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 101 (by decide)))

theorem fz2_97_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨102, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 102 (by decide)))

theorem fz2_97_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨103, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 103 (by decide)))

theorem fz2_97_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨104, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 104 (by decide)))

theorem fz2_97_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨105, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 105 (by decide)))

theorem fz2_97_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨106, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 106 (by decide)))

theorem fz2_97_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨107, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 107 (by decide)))

theorem fz2_97_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨108, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 108 (by decide)))

theorem fz2_97_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨109, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 109 (by decide)))

theorem fz2_97_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨110, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 110 (by decide)))

theorem fz2_97_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨111, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 111 (by decide)))

theorem fz2_97_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨112, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 112 (by decide)))

theorem fz2_97_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨113, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 113 (by decide)))

theorem fz2_97_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨114, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 114 (by decide)))

theorem fz2_97_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK97)) = 0 :=
  Q2.repsFixedCard2 rK97 ⟨115, by decide⟩ Q2.R97_2 Q2.hpxR97_2 Q2.hcardq97_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_97) 115 (by decide)))

theorem fixz1_98 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK98) (retConj 1 (R98 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_98_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨1, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 1 (by decide)))

theorem fz1_98_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨2, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 2 (by decide)))

theorem fz1_98_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨3, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 3 (by decide)))

theorem fz1_98_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨4, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 4 (by decide)))

theorem fz1_98_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨5, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 5 (by decide)))

theorem fz1_98_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨6, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 6 (by decide)))

theorem fz1_98_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨7, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 7 (by decide)))

theorem fz1_98_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨8, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 8 (by decide)))

theorem fz1_98_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨9, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 9 (by decide)))

theorem fz1_98_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨11, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 11 (by decide)))

theorem fz1_98_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨13, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 13 (by decide)))

theorem fz1_98_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨14, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 14 (by decide)))

theorem fz1_98_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨15, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 15 (by decide)))

theorem fz1_98_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨16, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 16 (by decide)))

theorem fz1_98_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨17, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 17 (by decide)))

theorem fz1_98_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨18, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 18 (by decide)))

theorem fz1_98_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨19, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 19 (by decide)))

theorem fz1_98_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨20, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 20 (by decide)))

theorem fz1_98_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨21, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 21 (by decide)))

theorem fz1_98_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨22, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 22 (by decide)))

theorem fz1_98_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨23, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 23 (by decide)))

theorem fz1_98_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨24, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 24 (by decide)))

theorem fz1_98_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨25, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 25 (by decide)))

theorem fz1_98_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨26, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 26 (by decide)))

theorem fz1_98_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨27, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 27 (by decide)))

theorem fz1_98_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨28, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 28 (by decide)))

theorem fz1_98_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨29, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 29 (by decide)))

theorem fz1_98_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨30, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 30 (by decide)))

theorem fz1_98_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨31, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 31 (by decide)))

theorem fz1_98_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨32, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 32 (by decide)))

theorem fz1_98_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨33, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 33 (by decide)))

theorem fz1_98_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨34, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 34 (by decide)))

theorem fz1_98_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨35, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 35 (by decide)))

theorem fz1_98_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨37, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 37 (by decide)))

theorem fz1_98_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨38, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 38 (by decide)))

theorem fz1_98_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨39, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 39 (by decide)))

theorem fz1_98_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨40, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 40 (by decide)))

theorem fz1_98_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨41, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 41 (by decide)))

theorem fz1_98_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨42, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 42 (by decide)))

theorem fz1_98_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨43, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 43 (by decide)))

theorem fz1_98_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨44, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 44 (by decide)))

theorem fz1_98_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨45, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 45 (by decide)))

theorem fz1_98_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨46, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 46 (by decide)))

theorem fz1_98_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨47, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 47 (by decide)))

theorem fz1_98_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨48, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 48 (by decide)))

theorem fz1_98_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨49, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 49 (by decide)))

theorem fz1_98_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨50, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 50 (by decide)))

theorem fz1_98_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨51, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 51 (by decide)))

theorem fz1_98_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨52, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 52 (by decide)))

theorem fz1_98_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨54, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 54 (by decide)))

theorem fz1_98_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨55, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 55 (by decide)))

theorem fz1_98_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨56, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 56 (by decide)))

theorem fz1_98_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨57, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 57 (by decide)))

theorem fz1_98_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨58, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 58 (by decide)))

theorem fz1_98_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨59, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 59 (by decide)))

theorem fz1_98_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨60, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 60 (by decide)))

theorem fz1_98_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨61, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 61 (by decide)))

theorem fz1_98_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨62, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 62 (by decide)))

theorem fz1_98_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨63, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 63 (by decide)))

theorem fz1_98_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨64, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 64 (by decide)))

theorem fz1_98_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨65, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 65 (by decide)))

theorem fz1_98_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨66, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 66 (by decide)))

theorem fz1_98_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨67, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 67 (by decide)))

theorem fz1_98_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨68, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 68 (by decide)))

theorem fz1_98_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨69, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 69 (by decide)))

theorem fz1_98_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨70, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 70 (by decide)))

theorem fz1_98_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨71, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 71 (by decide)))

theorem fz1_98_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨72, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 72 (by decide)))

theorem fz1_98_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨73, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 73 (by decide)))

theorem fz1_98_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨74, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 74 (by decide)))

theorem fz1_98_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨75, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 75 (by decide)))

theorem fz1_98_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨76, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 76 (by decide)))

theorem fz1_98_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨77, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 77 (by decide)))

theorem fz1_98_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨78, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 78 (by decide)))

theorem fz1_98_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨79, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 79 (by decide)))

theorem fz1_98_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨80, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 80 (by decide)))

theorem fz1_98_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨81, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 81 (by decide)))

theorem fz1_98_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨82, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 82 (by decide)))

theorem fz1_98_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨83, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 83 (by decide)))

theorem fz1_98_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨84, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 84 (by decide)))

theorem fz1_98_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨85, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 85 (by decide)))

theorem fz1_98_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨86, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 86 (by decide)))

theorem fz1_98_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨87, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 87 (by decide)))

theorem fz1_98_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨88, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 88 (by decide)))

theorem fz1_98_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨89, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 89 (by decide)))

theorem fz1_98_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨90, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 90 (by decide)))

theorem fz1_98_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨91, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 91 (by decide)))

theorem fz1_98_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨92, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 92 (by decide)))

theorem fz1_98_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨93, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 93 (by decide)))

theorem fz1_98_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨94, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 94 (by decide)))

theorem fz1_98_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨95, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 95 (by decide)))

theorem fz1_98_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨96, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 96 (by decide)))

theorem fz1_98_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨97, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 97 (by decide)))

theorem fz1_98_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨99, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 99 (by decide)))

theorem fz1_98_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨100, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 100 (by decide)))

theorem fz1_98_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨101, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 101 (by decide)))

theorem fz1_98_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨102, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 102 (by decide)))

theorem fz1_98_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨103, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 103 (by decide)))

theorem fz1_98_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨104, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 104 (by decide)))

theorem fz1_98_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨105, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 105 (by decide)))

theorem fz1_98_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨106, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 106 (by decide)))

theorem fz1_98_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨107, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 107 (by decide)))

theorem fz1_98_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨108, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 108 (by decide)))

theorem fz1_98_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨109, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 109 (by decide)))

theorem fz1_98_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨110, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 110 (by decide)))

theorem fz1_98_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨111, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 111 (by decide)))

theorem fz1_98_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨112, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 112 (by decide)))

theorem fz1_98_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨113, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 113 (by decide)))

theorem fz1_98_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨114, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 114 (by decide)))

theorem fz1_98_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK98)) = 0 :=
  repsFixedCard rK98 ⟨115, by decide⟩ R98 hpxR98 hcardq98
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_98) 115 (by decide)))

theorem fixz2_98 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK98) (retConj 2 (Q2.R98_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_98_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨1, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 1 (by decide)))

theorem fz2_98_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨2, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 2 (by decide)))

theorem fz2_98_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨3, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 3 (by decide)))

theorem fz2_98_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨4, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 4 (by decide)))

theorem fz2_98_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨5, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 5 (by decide)))

theorem fz2_98_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨6, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 6 (by decide)))

theorem fz2_98_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨7, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 7 (by decide)))

theorem fz2_98_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨8, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 8 (by decide)))

theorem fz2_98_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨9, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 9 (by decide)))

theorem fz2_98_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨11, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 11 (by decide)))

theorem fz2_98_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨13, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 13 (by decide)))

theorem fz2_98_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨14, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 14 (by decide)))

theorem fz2_98_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨15, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 15 (by decide)))

theorem fz2_98_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨16, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 16 (by decide)))

theorem fz2_98_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨17, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 17 (by decide)))

theorem fz2_98_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨18, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 18 (by decide)))

theorem fz2_98_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨19, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 19 (by decide)))

theorem fz2_98_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨20, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 20 (by decide)))

theorem fz2_98_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨21, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 21 (by decide)))

theorem fz2_98_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨22, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 22 (by decide)))

theorem fz2_98_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨23, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 23 (by decide)))

theorem fz2_98_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨24, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 24 (by decide)))

theorem fz2_98_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨25, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 25 (by decide)))

theorem fz2_98_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨26, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 26 (by decide)))

theorem fz2_98_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨27, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 27 (by decide)))

theorem fz2_98_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨28, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 28 (by decide)))

theorem fz2_98_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨29, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 29 (by decide)))

theorem fz2_98_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨30, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 30 (by decide)))

theorem fz2_98_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨31, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 31 (by decide)))

theorem fz2_98_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨32, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 32 (by decide)))

theorem fz2_98_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨33, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 33 (by decide)))

theorem fz2_98_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨34, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 34 (by decide)))

theorem fz2_98_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨35, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 35 (by decide)))

theorem fz2_98_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨37, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 37 (by decide)))

theorem fz2_98_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨38, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 38 (by decide)))

theorem fz2_98_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨39, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 39 (by decide)))

theorem fz2_98_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨40, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 40 (by decide)))

theorem fz2_98_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨41, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 41 (by decide)))

theorem fz2_98_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨42, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 42 (by decide)))

theorem fz2_98_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨43, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 43 (by decide)))

theorem fz2_98_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨44, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 44 (by decide)))

theorem fz2_98_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨45, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 45 (by decide)))

theorem fz2_98_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨46, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 46 (by decide)))

theorem fz2_98_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨47, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 47 (by decide)))

theorem fz2_98_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨48, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 48 (by decide)))

theorem fz2_98_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨49, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 49 (by decide)))

theorem fz2_98_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨50, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 50 (by decide)))

theorem fz2_98_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨51, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 51 (by decide)))

theorem fz2_98_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨52, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 52 (by decide)))

theorem fz2_98_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨54, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 54 (by decide)))

theorem fz2_98_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨55, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 55 (by decide)))

theorem fz2_98_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨56, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 56 (by decide)))

theorem fz2_98_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨57, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 57 (by decide)))

theorem fz2_98_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨58, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 58 (by decide)))

theorem fz2_98_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨59, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 59 (by decide)))

theorem fz2_98_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨60, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 60 (by decide)))

theorem fz2_98_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨61, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 61 (by decide)))

theorem fz2_98_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨62, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 62 (by decide)))

theorem fz2_98_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨63, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 63 (by decide)))

theorem fz2_98_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨64, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 64 (by decide)))

theorem fz2_98_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨65, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 65 (by decide)))

theorem fz2_98_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨66, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 66 (by decide)))

theorem fz2_98_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨67, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 67 (by decide)))

theorem fz2_98_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨68, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 68 (by decide)))

theorem fz2_98_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨69, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 69 (by decide)))

theorem fz2_98_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨70, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 70 (by decide)))

theorem fz2_98_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨71, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 71 (by decide)))

theorem fz2_98_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨72, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 72 (by decide)))

theorem fz2_98_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨73, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 73 (by decide)))

theorem fz2_98_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨74, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 74 (by decide)))

theorem fz2_98_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨75, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 75 (by decide)))

theorem fz2_98_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨76, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 76 (by decide)))

theorem fz2_98_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨77, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 77 (by decide)))

theorem fz2_98_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨78, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 78 (by decide)))

theorem fz2_98_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨79, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 79 (by decide)))

theorem fz2_98_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨80, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 80 (by decide)))

theorem fz2_98_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨81, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 81 (by decide)))

theorem fz2_98_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨82, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 82 (by decide)))

theorem fz2_98_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨83, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 83 (by decide)))

theorem fz2_98_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨84, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 84 (by decide)))

theorem fz2_98_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨85, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 85 (by decide)))

theorem fz2_98_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨86, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 86 (by decide)))

theorem fz2_98_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨87, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 87 (by decide)))

theorem fz2_98_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨88, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 88 (by decide)))

theorem fz2_98_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨89, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 89 (by decide)))

theorem fz2_98_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨90, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 90 (by decide)))

theorem fz2_98_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨91, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 91 (by decide)))

theorem fz2_98_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨92, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 92 (by decide)))

theorem fz2_98_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨93, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 93 (by decide)))

theorem fz2_98_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨94, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 94 (by decide)))

theorem fz2_98_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨95, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 95 (by decide)))

theorem fz2_98_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨96, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 96 (by decide)))

theorem fz2_98_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨97, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 97 (by decide)))

theorem fz2_98_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨99, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 99 (by decide)))

theorem fz2_98_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨100, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 100 (by decide)))

theorem fz2_98_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨101, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 101 (by decide)))

theorem fz2_98_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨102, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 102 (by decide)))

theorem fz2_98_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨103, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 103 (by decide)))

theorem fz2_98_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨104, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 104 (by decide)))

theorem fz2_98_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨105, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 105 (by decide)))

theorem fz2_98_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨106, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 106 (by decide)))

theorem fz2_98_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨107, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 107 (by decide)))

theorem fz2_98_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨108, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 108 (by decide)))

theorem fz2_98_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨109, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 109 (by decide)))

theorem fz2_98_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨110, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 110 (by decide)))

theorem fz2_98_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨111, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 111 (by decide)))

theorem fz2_98_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨112, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 112 (by decide)))

theorem fz2_98_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨113, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 113 (by decide)))

theorem fz2_98_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨114, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 114 (by decide)))

theorem fz2_98_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK98)) = 0 :=
  Q2.repsFixedCard2 rK98 ⟨115, by decide⟩ Q2.R98_2 Q2.hpxR98_2 Q2.hcardq98_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_98) 115 (by decide)))

end LeanDring.P5Presentation
