/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C015

/-!
# Species-table cells, off-support emptiness certificates, chunk 57

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

theorem fixz1_61 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK61) (retConj 1 (R61 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_61_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨2, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 2 (by decide)))

theorem fz1_61_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨3, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 3 (by decide)))

theorem fz1_61_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨4, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 4 (by decide)))

theorem fz1_61_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨5, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 5 (by decide)))

theorem fz1_61_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨6, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 6 (by decide)))

theorem fz1_61_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨7, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 7 (by decide)))

theorem fz1_61_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨8, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 8 (by decide)))

theorem fz1_61_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨9, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 9 (by decide)))

theorem fz1_61_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨10, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 10 (by decide)))

theorem fz1_61_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨11, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 11 (by decide)))

theorem fz1_61_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨13, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 13 (by decide)))

theorem fz1_61_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨14, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 14 (by decide)))

theorem fz1_61_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨15, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 15 (by decide)))

theorem fz1_61_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨16, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 16 (by decide)))

theorem fz1_61_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨17, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 17 (by decide)))

theorem fz1_61_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨18, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 18 (by decide)))

theorem fz1_61_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨20, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 20 (by decide)))

theorem fz1_61_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨21, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 21 (by decide)))

theorem fz1_61_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨22, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 22 (by decide)))

theorem fz1_61_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨23, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 23 (by decide)))

theorem fz1_61_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨24, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 24 (by decide)))

theorem fz1_61_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨25, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 25 (by decide)))

theorem fz1_61_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨26, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 26 (by decide)))

theorem fz1_61_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨27, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 27 (by decide)))

theorem fz1_61_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨28, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 28 (by decide)))

theorem fz1_61_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨30, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 30 (by decide)))

theorem fz1_61_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨31, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 31 (by decide)))

theorem fz1_61_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨32, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 32 (by decide)))

theorem fz1_61_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨33, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 33 (by decide)))

theorem fz1_61_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨35, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 35 (by decide)))

theorem fz1_61_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨36, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 36 (by decide)))

theorem fz1_61_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨37, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 37 (by decide)))

theorem fz1_61_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨38, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 38 (by decide)))

theorem fz1_61_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨40, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 40 (by decide)))

theorem fz1_61_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨41, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 41 (by decide)))

theorem fz1_61_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨42, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 42 (by decide)))

theorem fz1_61_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨43, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 43 (by decide)))

theorem fz1_61_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨45, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 45 (by decide)))

theorem fz1_61_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨46, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 46 (by decide)))

theorem fz1_61_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨47, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 47 (by decide)))

theorem fz1_61_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨48, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 48 (by decide)))

theorem fz1_61_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨50, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 50 (by decide)))

theorem fz1_61_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨51, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 51 (by decide)))

theorem fz1_61_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨52, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 52 (by decide)))

theorem fz1_61_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨53, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 53 (by decide)))

theorem fz1_61_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨54, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 54 (by decide)))

theorem fz1_61_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨55, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 55 (by decide)))

theorem fz1_61_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨56, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 56 (by decide)))

theorem fz1_61_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨57, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 57 (by decide)))

theorem fz1_61_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨58, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 58 (by decide)))

theorem fz1_61_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨59, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 59 (by decide)))

theorem fz1_61_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨60, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 60 (by decide)))

theorem fz1_61_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨62, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 62 (by decide)))

theorem fz1_61_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨63, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 63 (by decide)))

theorem fz1_61_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨64, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 64 (by decide)))

theorem fz1_61_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨65, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 65 (by decide)))

theorem fz1_61_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨66, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 66 (by decide)))

theorem fz1_61_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨67, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 67 (by decide)))

theorem fz1_61_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨68, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 68 (by decide)))

theorem fz1_61_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨69, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 69 (by decide)))

theorem fz1_61_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨70, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 70 (by decide)))

theorem fz1_61_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨71, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 71 (by decide)))

theorem fz1_61_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨72, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 72 (by decide)))

theorem fz1_61_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨73, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 73 (by decide)))

theorem fz1_61_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨74, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 74 (by decide)))

theorem fz1_61_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨75, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 75 (by decide)))

theorem fz1_61_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨76, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 76 (by decide)))

theorem fz1_61_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨77, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 77 (by decide)))

theorem fz1_61_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨78, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 78 (by decide)))

theorem fz1_61_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨79, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 79 (by decide)))

theorem fz1_61_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨80, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 80 (by decide)))

theorem fz1_61_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨81, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 81 (by decide)))

theorem fz1_61_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨82, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 82 (by decide)))

theorem fz1_61_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨83, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 83 (by decide)))

theorem fz1_61_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨84, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 84 (by decide)))

theorem fz1_61_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨85, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 85 (by decide)))

theorem fz1_61_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨86, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 86 (by decide)))

theorem fz1_61_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨87, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 87 (by decide)))

theorem fz1_61_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨88, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 88 (by decide)))

theorem fz1_61_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨89, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 89 (by decide)))

theorem fz1_61_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨90, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 90 (by decide)))

theorem fz1_61_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨91, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 91 (by decide)))

theorem fz1_61_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨92, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 92 (by decide)))

theorem fz1_61_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨93, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 93 (by decide)))

theorem fz1_61_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨94, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 94 (by decide)))

theorem fz1_61_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨95, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 95 (by decide)))

theorem fz1_61_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨96, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 96 (by decide)))

theorem fz1_61_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨97, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 97 (by decide)))

theorem fz1_61_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨98, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 98 (by decide)))

theorem fz1_61_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨99, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 99 (by decide)))

theorem fz1_61_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨100, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 100 (by decide)))

theorem fz1_61_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨101, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 101 (by decide)))

theorem fz1_61_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨102, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 102 (by decide)))

theorem fz1_61_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨103, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 103 (by decide)))

theorem fz1_61_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨104, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 104 (by decide)))

theorem fz1_61_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨105, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 105 (by decide)))

theorem fz1_61_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨106, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 106 (by decide)))

theorem fz1_61_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨107, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 107 (by decide)))

theorem fz1_61_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨108, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 108 (by decide)))

theorem fz1_61_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨109, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 109 (by decide)))

theorem fz1_61_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨110, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 110 (by decide)))

theorem fz1_61_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨111, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 111 (by decide)))

theorem fz1_61_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨112, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 112 (by decide)))

theorem fz1_61_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨113, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 113 (by decide)))

theorem fz1_61_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨114, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 114 (by decide)))

theorem fz1_61_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK61)) = 0 :=
  repsFixedCard rK61 ⟨115, by decide⟩ R61 hpxR61 hcardq61
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_61) 115 (by decide)))

theorem fixz2_61 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK61) (retConj 2 (Q2.R61_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_61_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨2, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 2 (by decide)))

theorem fz2_61_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨3, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 3 (by decide)))

theorem fz2_61_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨4, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 4 (by decide)))

theorem fz2_61_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨5, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 5 (by decide)))

theorem fz2_61_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨6, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 6 (by decide)))

theorem fz2_61_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨7, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 7 (by decide)))

theorem fz2_61_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨8, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 8 (by decide)))

theorem fz2_61_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨9, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 9 (by decide)))

theorem fz2_61_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨10, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 10 (by decide)))

theorem fz2_61_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨11, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 11 (by decide)))

theorem fz2_61_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨13, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 13 (by decide)))

theorem fz2_61_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨14, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 14 (by decide)))

theorem fz2_61_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨15, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 15 (by decide)))

theorem fz2_61_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨16, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 16 (by decide)))

theorem fz2_61_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨17, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 17 (by decide)))

theorem fz2_61_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨18, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 18 (by decide)))

theorem fz2_61_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨20, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 20 (by decide)))

theorem fz2_61_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨21, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 21 (by decide)))

theorem fz2_61_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨22, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 22 (by decide)))

theorem fz2_61_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨23, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 23 (by decide)))

theorem fz2_61_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨24, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 24 (by decide)))

theorem fz2_61_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨25, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 25 (by decide)))

theorem fz2_61_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨26, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 26 (by decide)))

theorem fz2_61_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨27, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 27 (by decide)))

theorem fz2_61_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨28, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 28 (by decide)))

theorem fz2_61_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨30, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 30 (by decide)))

theorem fz2_61_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨31, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 31 (by decide)))

theorem fz2_61_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨32, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 32 (by decide)))

theorem fz2_61_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨33, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 33 (by decide)))

theorem fz2_61_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨35, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 35 (by decide)))

theorem fz2_61_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨36, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 36 (by decide)))

theorem fz2_61_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨37, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 37 (by decide)))

theorem fz2_61_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨38, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 38 (by decide)))

theorem fz2_61_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨40, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 40 (by decide)))

theorem fz2_61_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨41, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 41 (by decide)))

theorem fz2_61_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨42, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 42 (by decide)))

theorem fz2_61_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨43, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 43 (by decide)))

theorem fz2_61_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨45, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 45 (by decide)))

theorem fz2_61_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨46, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 46 (by decide)))

theorem fz2_61_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨47, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 47 (by decide)))

theorem fz2_61_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨48, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 48 (by decide)))

theorem fz2_61_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨50, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 50 (by decide)))

theorem fz2_61_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨51, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 51 (by decide)))

theorem fz2_61_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨52, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 52 (by decide)))

theorem fz2_61_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨53, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 53 (by decide)))

theorem fz2_61_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨54, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 54 (by decide)))

theorem fz2_61_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨55, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 55 (by decide)))

theorem fz2_61_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨56, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 56 (by decide)))

theorem fz2_61_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨57, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 57 (by decide)))

theorem fz2_61_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨58, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 58 (by decide)))

theorem fz2_61_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨59, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 59 (by decide)))

theorem fz2_61_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨60, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 60 (by decide)))

theorem fz2_61_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨62, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 62 (by decide)))

theorem fz2_61_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨63, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 63 (by decide)))

theorem fz2_61_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨64, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 64 (by decide)))

theorem fz2_61_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨65, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 65 (by decide)))

theorem fz2_61_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨66, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 66 (by decide)))

theorem fz2_61_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨67, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 67 (by decide)))

theorem fz2_61_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨68, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 68 (by decide)))

theorem fz2_61_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨69, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 69 (by decide)))

theorem fz2_61_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨70, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 70 (by decide)))

theorem fz2_61_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨71, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 71 (by decide)))

theorem fz2_61_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨72, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 72 (by decide)))

theorem fz2_61_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨73, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 73 (by decide)))

theorem fz2_61_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨74, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 74 (by decide)))

theorem fz2_61_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨75, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 75 (by decide)))

theorem fz2_61_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨76, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 76 (by decide)))

theorem fz2_61_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨77, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 77 (by decide)))

theorem fz2_61_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨78, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 78 (by decide)))

theorem fz2_61_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨79, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 79 (by decide)))

theorem fz2_61_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨80, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 80 (by decide)))

theorem fz2_61_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨81, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 81 (by decide)))

theorem fz2_61_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨82, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 82 (by decide)))

theorem fz2_61_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨83, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 83 (by decide)))

theorem fz2_61_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨84, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 84 (by decide)))

theorem fz2_61_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨85, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 85 (by decide)))

theorem fz2_61_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨86, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 86 (by decide)))

theorem fz2_61_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨87, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 87 (by decide)))

theorem fz2_61_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨88, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 88 (by decide)))

theorem fz2_61_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨89, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 89 (by decide)))

theorem fz2_61_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨90, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 90 (by decide)))

theorem fz2_61_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨91, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 91 (by decide)))

theorem fz2_61_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨92, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 92 (by decide)))

theorem fz2_61_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨93, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 93 (by decide)))

theorem fz2_61_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨94, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 94 (by decide)))

theorem fz2_61_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨95, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 95 (by decide)))

theorem fz2_61_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨96, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 96 (by decide)))

theorem fz2_61_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨97, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 97 (by decide)))

theorem fz2_61_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨98, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 98 (by decide)))

theorem fz2_61_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨99, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 99 (by decide)))

theorem fz2_61_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨100, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 100 (by decide)))

theorem fz2_61_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨101, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 101 (by decide)))

theorem fz2_61_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨102, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 102 (by decide)))

theorem fz2_61_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨103, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 103 (by decide)))

theorem fz2_61_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨104, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 104 (by decide)))

theorem fz2_61_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨105, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 105 (by decide)))

theorem fz2_61_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨106, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 106 (by decide)))

theorem fz2_61_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨107, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 107 (by decide)))

theorem fz2_61_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨108, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 108 (by decide)))

theorem fz2_61_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨109, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 109 (by decide)))

theorem fz2_61_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨110, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 110 (by decide)))

theorem fz2_61_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨111, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 111 (by decide)))

theorem fz2_61_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨112, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 112 (by decide)))

theorem fz2_61_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨113, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 113 (by decide)))

theorem fz2_61_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨114, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 114 (by decide)))

theorem fz2_61_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK61)) = 0 :=
  Q2.repsFixedCard2 rK61 ⟨115, by decide⟩ Q2.R61_2 Q2.hpxR61_2 Q2.hcardq61_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_61) 115 (by decide)))

theorem fixz1_62 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK62) (retConj 1 (R62 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_62_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨1, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 1 (by decide)))

theorem fz1_62_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨2, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 2 (by decide)))

theorem fz1_62_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨3, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 3 (by decide)))

theorem fz1_62_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨4, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 4 (by decide)))

theorem fz1_62_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨5, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 5 (by decide)))

theorem fz1_62_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨6, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 6 (by decide)))

theorem fz1_62_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨8, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 8 (by decide)))

theorem fz1_62_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨9, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 9 (by decide)))

theorem fz1_62_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨10, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 10 (by decide)))

theorem fz1_62_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨11, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 11 (by decide)))

theorem fz1_62_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨13, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 13 (by decide)))

theorem fz1_62_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨14, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 14 (by decide)))

theorem fz1_62_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨15, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 15 (by decide)))

theorem fz1_62_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨16, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 16 (by decide)))

theorem fz1_62_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨17, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 17 (by decide)))

theorem fz1_62_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨18, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 18 (by decide)))

theorem fz1_62_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨19, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 19 (by decide)))

theorem fz1_62_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨20, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 20 (by decide)))

theorem fz1_62_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨21, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 21 (by decide)))

theorem fz1_62_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨22, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 22 (by decide)))

theorem fz1_62_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨23, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 23 (by decide)))

theorem fz1_62_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨24, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 24 (by decide)))

theorem fz1_62_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨26, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 26 (by decide)))

theorem fz1_62_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨27, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 27 (by decide)))

theorem fz1_62_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨28, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 28 (by decide)))

theorem fz1_62_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨30, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 30 (by decide)))

theorem fz1_62_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨31, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 31 (by decide)))

theorem fz1_62_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨32, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 32 (by decide)))

theorem fz1_62_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨33, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 33 (by decide)))

theorem fz1_62_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨35, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 35 (by decide)))

theorem fz1_62_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨36, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 36 (by decide)))

theorem fz1_62_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨37, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 37 (by decide)))

theorem fz1_62_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨38, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 38 (by decide)))

theorem fz1_62_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨40, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 40 (by decide)))

theorem fz1_62_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨41, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 41 (by decide)))

theorem fz1_62_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨42, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 42 (by decide)))

theorem fz1_62_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨43, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 43 (by decide)))

theorem fz1_62_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨45, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 45 (by decide)))

theorem fz1_62_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨46, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 46 (by decide)))

theorem fz1_62_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨47, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 47 (by decide)))

theorem fz1_62_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨48, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 48 (by decide)))

theorem fz1_62_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨50, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 50 (by decide)))

theorem fz1_62_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨51, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 51 (by decide)))

theorem fz1_62_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨52, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 52 (by decide)))

theorem fz1_62_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨53, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 53 (by decide)))

theorem fz1_62_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨54, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 54 (by decide)))

theorem fz1_62_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨55, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 55 (by decide)))

theorem fz1_62_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨56, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 56 (by decide)))

theorem fz1_62_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨57, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 57 (by decide)))

theorem fz1_62_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨58, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 58 (by decide)))

theorem fz1_62_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨59, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 59 (by decide)))

theorem fz1_62_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨60, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 60 (by decide)))

theorem fz1_62_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨61, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 61 (by decide)))

theorem fz1_62_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨63, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 63 (by decide)))

theorem fz1_62_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨64, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 64 (by decide)))

theorem fz1_62_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨65, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 65 (by decide)))

theorem fz1_62_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨66, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 66 (by decide)))

theorem fz1_62_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨67, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 67 (by decide)))

theorem fz1_62_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨68, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 68 (by decide)))

theorem fz1_62_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨69, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 69 (by decide)))

theorem fz1_62_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨70, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 70 (by decide)))

theorem fz1_62_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨71, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 71 (by decide)))

theorem fz1_62_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨72, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 72 (by decide)))

theorem fz1_62_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨73, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 73 (by decide)))

theorem fz1_62_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨74, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 74 (by decide)))

theorem fz1_62_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨75, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 75 (by decide)))

theorem fz1_62_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨76, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 76 (by decide)))

theorem fz1_62_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨77, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 77 (by decide)))

theorem fz1_62_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨78, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 78 (by decide)))

theorem fz1_62_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨79, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 79 (by decide)))

theorem fz1_62_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨80, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 80 (by decide)))

theorem fz1_62_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨81, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 81 (by decide)))

theorem fz1_62_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨82, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 82 (by decide)))

theorem fz1_62_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨83, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 83 (by decide)))

theorem fz1_62_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨84, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 84 (by decide)))

theorem fz1_62_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨85, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 85 (by decide)))

theorem fz1_62_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨86, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 86 (by decide)))

theorem fz1_62_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨87, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 87 (by decide)))

theorem fz1_62_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨88, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 88 (by decide)))

theorem fz1_62_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨89, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 89 (by decide)))

theorem fz1_62_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨90, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 90 (by decide)))

theorem fz1_62_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨91, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 91 (by decide)))

theorem fz1_62_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨92, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 92 (by decide)))

theorem fz1_62_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨93, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 93 (by decide)))

theorem fz1_62_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨94, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 94 (by decide)))

theorem fz1_62_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨95, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 95 (by decide)))

theorem fz1_62_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨96, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 96 (by decide)))

theorem fz1_62_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨97, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 97 (by decide)))

theorem fz1_62_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨98, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 98 (by decide)))

theorem fz1_62_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨99, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 99 (by decide)))

theorem fz1_62_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨100, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 100 (by decide)))

theorem fz1_62_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨101, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 101 (by decide)))

theorem fz1_62_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨102, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 102 (by decide)))

theorem fz1_62_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨103, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 103 (by decide)))

theorem fz1_62_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨104, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 104 (by decide)))

theorem fz1_62_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨105, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 105 (by decide)))

theorem fz1_62_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨106, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 106 (by decide)))

theorem fz1_62_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨107, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 107 (by decide)))

theorem fz1_62_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨108, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 108 (by decide)))

theorem fz1_62_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨109, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 109 (by decide)))

theorem fz1_62_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨110, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 110 (by decide)))

theorem fz1_62_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨111, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 111 (by decide)))

theorem fz1_62_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨112, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 112 (by decide)))

theorem fz1_62_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨113, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 113 (by decide)))

theorem fz1_62_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨114, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 114 (by decide)))

theorem fz1_62_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK62)) = 0 :=
  repsFixedCard rK62 ⟨115, by decide⟩ R62 hpxR62 hcardq62
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_62) 115 (by decide)))

theorem fixz2_62 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK62) (retConj 2 (Q2.R62_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_62_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨1, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 1 (by decide)))

theorem fz2_62_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨2, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 2 (by decide)))

theorem fz2_62_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨3, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 3 (by decide)))

theorem fz2_62_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨4, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 4 (by decide)))

theorem fz2_62_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨5, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 5 (by decide)))

theorem fz2_62_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨6, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 6 (by decide)))

theorem fz2_62_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨8, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 8 (by decide)))

theorem fz2_62_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨9, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 9 (by decide)))

theorem fz2_62_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨10, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 10 (by decide)))

theorem fz2_62_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨11, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 11 (by decide)))

theorem fz2_62_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨13, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 13 (by decide)))

theorem fz2_62_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨14, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 14 (by decide)))

theorem fz2_62_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨15, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 15 (by decide)))

theorem fz2_62_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨16, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 16 (by decide)))

theorem fz2_62_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨17, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 17 (by decide)))

theorem fz2_62_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨18, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 18 (by decide)))

theorem fz2_62_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨19, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 19 (by decide)))

theorem fz2_62_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨20, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 20 (by decide)))

theorem fz2_62_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨21, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 21 (by decide)))

theorem fz2_62_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨22, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 22 (by decide)))

theorem fz2_62_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨23, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 23 (by decide)))

theorem fz2_62_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨24, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 24 (by decide)))

theorem fz2_62_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨26, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 26 (by decide)))

theorem fz2_62_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨27, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 27 (by decide)))

theorem fz2_62_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨28, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 28 (by decide)))

theorem fz2_62_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨30, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 30 (by decide)))

theorem fz2_62_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨31, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 31 (by decide)))

theorem fz2_62_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨32, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 32 (by decide)))

theorem fz2_62_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨33, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 33 (by decide)))

theorem fz2_62_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨35, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 35 (by decide)))

theorem fz2_62_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨36, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 36 (by decide)))

theorem fz2_62_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨37, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 37 (by decide)))

theorem fz2_62_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨38, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 38 (by decide)))

theorem fz2_62_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨40, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 40 (by decide)))

theorem fz2_62_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨41, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 41 (by decide)))

theorem fz2_62_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨42, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 42 (by decide)))

theorem fz2_62_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨43, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 43 (by decide)))

theorem fz2_62_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨45, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 45 (by decide)))

theorem fz2_62_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨46, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 46 (by decide)))

theorem fz2_62_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨47, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 47 (by decide)))

theorem fz2_62_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨48, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 48 (by decide)))

theorem fz2_62_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨50, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 50 (by decide)))

theorem fz2_62_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨51, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 51 (by decide)))

theorem fz2_62_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨52, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 52 (by decide)))

theorem fz2_62_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨53, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 53 (by decide)))

theorem fz2_62_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨54, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 54 (by decide)))

theorem fz2_62_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨55, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 55 (by decide)))

theorem fz2_62_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨56, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 56 (by decide)))

theorem fz2_62_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨57, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 57 (by decide)))

theorem fz2_62_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨58, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 58 (by decide)))

theorem fz2_62_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨59, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 59 (by decide)))

theorem fz2_62_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨60, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 60 (by decide)))

theorem fz2_62_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨61, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 61 (by decide)))

theorem fz2_62_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨63, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 63 (by decide)))

theorem fz2_62_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨64, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 64 (by decide)))

theorem fz2_62_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨65, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 65 (by decide)))

theorem fz2_62_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨66, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 66 (by decide)))

theorem fz2_62_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨67, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 67 (by decide)))

theorem fz2_62_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨68, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 68 (by decide)))

theorem fz2_62_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨69, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 69 (by decide)))

theorem fz2_62_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨70, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 70 (by decide)))

theorem fz2_62_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨71, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 71 (by decide)))

theorem fz2_62_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨72, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 72 (by decide)))

theorem fz2_62_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨73, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 73 (by decide)))

theorem fz2_62_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨74, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 74 (by decide)))

theorem fz2_62_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨75, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 75 (by decide)))

theorem fz2_62_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨76, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 76 (by decide)))

theorem fz2_62_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨77, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 77 (by decide)))

theorem fz2_62_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨78, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 78 (by decide)))

theorem fz2_62_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨79, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 79 (by decide)))

theorem fz2_62_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨80, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 80 (by decide)))

theorem fz2_62_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨81, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 81 (by decide)))

theorem fz2_62_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨82, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 82 (by decide)))

theorem fz2_62_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨83, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 83 (by decide)))

theorem fz2_62_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨84, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 84 (by decide)))

theorem fz2_62_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨85, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 85 (by decide)))

theorem fz2_62_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨86, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 86 (by decide)))

theorem fz2_62_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨87, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 87 (by decide)))

theorem fz2_62_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨88, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 88 (by decide)))

theorem fz2_62_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨89, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 89 (by decide)))

theorem fz2_62_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨90, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 90 (by decide)))

theorem fz2_62_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨91, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 91 (by decide)))

theorem fz2_62_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨92, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 92 (by decide)))

theorem fz2_62_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨93, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 93 (by decide)))

theorem fz2_62_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨94, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 94 (by decide)))

theorem fz2_62_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨95, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 95 (by decide)))

theorem fz2_62_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨96, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 96 (by decide)))

theorem fz2_62_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨97, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 97 (by decide)))

theorem fz2_62_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨98, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 98 (by decide)))

theorem fz2_62_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨99, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 99 (by decide)))

theorem fz2_62_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨100, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 100 (by decide)))

theorem fz2_62_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨101, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 101 (by decide)))

theorem fz2_62_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨102, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 102 (by decide)))

theorem fz2_62_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨103, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 103 (by decide)))

theorem fz2_62_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨104, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 104 (by decide)))

theorem fz2_62_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨105, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 105 (by decide)))

theorem fz2_62_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨106, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 106 (by decide)))

theorem fz2_62_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨107, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 107 (by decide)))

theorem fz2_62_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨108, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 108 (by decide)))

theorem fz2_62_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨109, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 109 (by decide)))

theorem fz2_62_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨110, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 110 (by decide)))

theorem fz2_62_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨111, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 111 (by decide)))

theorem fz2_62_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨112, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 112 (by decide)))

theorem fz2_62_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨113, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 113 (by decide)))

theorem fz2_62_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨114, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 114 (by decide)))

theorem fz2_62_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK62)) = 0 :=
  Q2.repsFixedCard2 rK62 ⟨115, by decide⟩ Q2.R62_2 Q2.hpxR62_2 Q2.hcardq62_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_62) 115 (by decide)))

end LeanDring.P5Presentation
