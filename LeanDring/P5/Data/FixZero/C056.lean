/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C014

/-!
# Species-table cells, off-support emptiness certificates, chunk 55

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

theorem fixz1_57 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK57) (retConj 1 (R57 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_57_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨1, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 1 (by decide)))

theorem fz1_57_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨2, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 2 (by decide)))

theorem fz1_57_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨3, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 3 (by decide)))

theorem fz1_57_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨4, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 4 (by decide)))

theorem fz1_57_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨5, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 5 (by decide)))

theorem fz1_57_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨6, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 6 (by decide)))

theorem fz1_57_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨8, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 8 (by decide)))

theorem fz1_57_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨9, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 9 (by decide)))

theorem fz1_57_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨10, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 10 (by decide)))

theorem fz1_57_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨11, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 11 (by decide)))

theorem fz1_57_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨13, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 13 (by decide)))

theorem fz1_57_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨14, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 14 (by decide)))

theorem fz1_57_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨15, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 15 (by decide)))

theorem fz1_57_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨16, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 16 (by decide)))

theorem fz1_57_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨17, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 17 (by decide)))

theorem fz1_57_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨18, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 18 (by decide)))

theorem fz1_57_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨19, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 19 (by decide)))

theorem fz1_57_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨20, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 20 (by decide)))

theorem fz1_57_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨21, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 21 (by decide)))

theorem fz1_57_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨22, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 22 (by decide)))

theorem fz1_57_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨23, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 23 (by decide)))

theorem fz1_57_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨24, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 24 (by decide)))

theorem fz1_57_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨26, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 26 (by decide)))

theorem fz1_57_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨27, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 27 (by decide)))

theorem fz1_57_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨29, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 29 (by decide)))

theorem fz1_57_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨30, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 30 (by decide)))

theorem fz1_57_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨31, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 31 (by decide)))

theorem fz1_57_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨32, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 32 (by decide)))

theorem fz1_57_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨34, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 34 (by decide)))

theorem fz1_57_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨35, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 35 (by decide)))

theorem fz1_57_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨36, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 36 (by decide)))

theorem fz1_57_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨37, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 37 (by decide)))

theorem fz1_57_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨39, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 39 (by decide)))

theorem fz1_57_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨40, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 40 (by decide)))

theorem fz1_57_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨41, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 41 (by decide)))

theorem fz1_57_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨42, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 42 (by decide)))

theorem fz1_57_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨44, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 44 (by decide)))

theorem fz1_57_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨45, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 45 (by decide)))

theorem fz1_57_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨46, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 46 (by decide)))

theorem fz1_57_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨47, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 47 (by decide)))

theorem fz1_57_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨49, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 49 (by decide)))

theorem fz1_57_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨50, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 50 (by decide)))

theorem fz1_57_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨51, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 51 (by decide)))

theorem fz1_57_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨52, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 52 (by decide)))

theorem fz1_57_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨53, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 53 (by decide)))

theorem fz1_57_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨54, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 54 (by decide)))

theorem fz1_57_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨55, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 55 (by decide)))

theorem fz1_57_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨56, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 56 (by decide)))

theorem fz1_57_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨58, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 58 (by decide)))

theorem fz1_57_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨59, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 59 (by decide)))

theorem fz1_57_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨60, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 60 (by decide)))

theorem fz1_57_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨61, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 61 (by decide)))

theorem fz1_57_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨62, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 62 (by decide)))

theorem fz1_57_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨63, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 63 (by decide)))

theorem fz1_57_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨64, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 64 (by decide)))

theorem fz1_57_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨65, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 65 (by decide)))

theorem fz1_57_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨66, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 66 (by decide)))

theorem fz1_57_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨67, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 67 (by decide)))

theorem fz1_57_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨68, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 68 (by decide)))

theorem fz1_57_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨69, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 69 (by decide)))

theorem fz1_57_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨70, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 70 (by decide)))

theorem fz1_57_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨71, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 71 (by decide)))

theorem fz1_57_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨72, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 72 (by decide)))

theorem fz1_57_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨73, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 73 (by decide)))

theorem fz1_57_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨74, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 74 (by decide)))

theorem fz1_57_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨75, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 75 (by decide)))

theorem fz1_57_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨76, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 76 (by decide)))

theorem fz1_57_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨77, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 77 (by decide)))

theorem fz1_57_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨78, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 78 (by decide)))

theorem fz1_57_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨79, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 79 (by decide)))

theorem fz1_57_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨80, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 80 (by decide)))

theorem fz1_57_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨81, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 81 (by decide)))

theorem fz1_57_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨82, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 82 (by decide)))

theorem fz1_57_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨83, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 83 (by decide)))

theorem fz1_57_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨84, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 84 (by decide)))

theorem fz1_57_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨85, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 85 (by decide)))

theorem fz1_57_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨86, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 86 (by decide)))

theorem fz1_57_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨87, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 87 (by decide)))

theorem fz1_57_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨88, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 88 (by decide)))

theorem fz1_57_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨89, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 89 (by decide)))

theorem fz1_57_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨90, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 90 (by decide)))

theorem fz1_57_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨91, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 91 (by decide)))

theorem fz1_57_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨92, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 92 (by decide)))

theorem fz1_57_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨93, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 93 (by decide)))

theorem fz1_57_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨94, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 94 (by decide)))

theorem fz1_57_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨95, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 95 (by decide)))

theorem fz1_57_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨96, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 96 (by decide)))

theorem fz1_57_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨97, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 97 (by decide)))

theorem fz1_57_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨98, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 98 (by decide)))

theorem fz1_57_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨99, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 99 (by decide)))

theorem fz1_57_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨100, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 100 (by decide)))

theorem fz1_57_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨101, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 101 (by decide)))

theorem fz1_57_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨102, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 102 (by decide)))

theorem fz1_57_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨103, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 103 (by decide)))

theorem fz1_57_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨104, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 104 (by decide)))

theorem fz1_57_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨105, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 105 (by decide)))

theorem fz1_57_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨106, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 106 (by decide)))

theorem fz1_57_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨107, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 107 (by decide)))

theorem fz1_57_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨108, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 108 (by decide)))

theorem fz1_57_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨109, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 109 (by decide)))

theorem fz1_57_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨110, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 110 (by decide)))

theorem fz1_57_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨111, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 111 (by decide)))

theorem fz1_57_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨112, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 112 (by decide)))

theorem fz1_57_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨113, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 113 (by decide)))

theorem fz1_57_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨114, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 114 (by decide)))

theorem fz1_57_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK57)) = 0 :=
  repsFixedCard rK57 ⟨115, by decide⟩ R57 hpxR57 hcardq57
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_57) 115 (by decide)))

theorem fixz2_57 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK57) (retConj 2 (Q2.R57_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_57_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨1, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 1 (by decide)))

theorem fz2_57_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨2, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 2 (by decide)))

theorem fz2_57_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨3, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 3 (by decide)))

theorem fz2_57_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨4, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 4 (by decide)))

theorem fz2_57_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨5, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 5 (by decide)))

theorem fz2_57_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨6, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 6 (by decide)))

theorem fz2_57_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨8, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 8 (by decide)))

theorem fz2_57_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨9, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 9 (by decide)))

theorem fz2_57_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨10, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 10 (by decide)))

theorem fz2_57_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨11, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 11 (by decide)))

theorem fz2_57_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨13, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 13 (by decide)))

theorem fz2_57_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨14, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 14 (by decide)))

theorem fz2_57_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨15, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 15 (by decide)))

theorem fz2_57_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨16, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 16 (by decide)))

theorem fz2_57_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨17, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 17 (by decide)))

theorem fz2_57_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨18, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 18 (by decide)))

theorem fz2_57_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨19, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 19 (by decide)))

theorem fz2_57_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨20, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 20 (by decide)))

theorem fz2_57_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨21, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 21 (by decide)))

theorem fz2_57_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨22, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 22 (by decide)))

theorem fz2_57_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨23, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 23 (by decide)))

theorem fz2_57_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨24, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 24 (by decide)))

theorem fz2_57_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨26, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 26 (by decide)))

theorem fz2_57_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨27, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 27 (by decide)))

theorem fz2_57_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨29, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 29 (by decide)))

theorem fz2_57_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨30, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 30 (by decide)))

theorem fz2_57_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨31, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 31 (by decide)))

theorem fz2_57_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨32, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 32 (by decide)))

theorem fz2_57_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨34, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 34 (by decide)))

theorem fz2_57_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨35, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 35 (by decide)))

theorem fz2_57_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨36, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 36 (by decide)))

theorem fz2_57_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨37, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 37 (by decide)))

theorem fz2_57_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨39, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 39 (by decide)))

theorem fz2_57_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨40, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 40 (by decide)))

theorem fz2_57_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨41, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 41 (by decide)))

theorem fz2_57_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨42, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 42 (by decide)))

theorem fz2_57_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨44, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 44 (by decide)))

theorem fz2_57_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨45, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 45 (by decide)))

theorem fz2_57_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨46, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 46 (by decide)))

theorem fz2_57_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨47, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 47 (by decide)))

theorem fz2_57_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨49, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 49 (by decide)))

theorem fz2_57_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨50, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 50 (by decide)))

theorem fz2_57_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨51, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 51 (by decide)))

theorem fz2_57_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨52, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 52 (by decide)))

theorem fz2_57_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨53, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 53 (by decide)))

theorem fz2_57_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨54, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 54 (by decide)))

theorem fz2_57_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨55, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 55 (by decide)))

theorem fz2_57_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨56, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 56 (by decide)))

theorem fz2_57_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨58, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 58 (by decide)))

theorem fz2_57_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨59, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 59 (by decide)))

theorem fz2_57_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨60, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 60 (by decide)))

theorem fz2_57_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨61, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 61 (by decide)))

theorem fz2_57_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨62, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 62 (by decide)))

theorem fz2_57_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨63, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 63 (by decide)))

theorem fz2_57_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨64, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 64 (by decide)))

theorem fz2_57_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨65, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 65 (by decide)))

theorem fz2_57_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨66, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 66 (by decide)))

theorem fz2_57_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨67, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 67 (by decide)))

theorem fz2_57_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨68, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 68 (by decide)))

theorem fz2_57_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨69, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 69 (by decide)))

theorem fz2_57_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨70, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 70 (by decide)))

theorem fz2_57_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨71, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 71 (by decide)))

theorem fz2_57_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨72, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 72 (by decide)))

theorem fz2_57_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨73, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 73 (by decide)))

theorem fz2_57_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨74, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 74 (by decide)))

theorem fz2_57_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨75, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 75 (by decide)))

theorem fz2_57_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨76, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 76 (by decide)))

theorem fz2_57_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨77, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 77 (by decide)))

theorem fz2_57_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨78, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 78 (by decide)))

theorem fz2_57_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨79, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 79 (by decide)))

theorem fz2_57_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨80, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 80 (by decide)))

theorem fz2_57_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨81, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 81 (by decide)))

theorem fz2_57_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨82, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 82 (by decide)))

theorem fz2_57_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨83, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 83 (by decide)))

theorem fz2_57_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨84, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 84 (by decide)))

theorem fz2_57_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨85, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 85 (by decide)))

theorem fz2_57_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨86, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 86 (by decide)))

theorem fz2_57_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨87, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 87 (by decide)))

theorem fz2_57_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨88, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 88 (by decide)))

theorem fz2_57_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨89, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 89 (by decide)))

theorem fz2_57_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨90, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 90 (by decide)))

theorem fz2_57_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨91, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 91 (by decide)))

theorem fz2_57_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨92, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 92 (by decide)))

theorem fz2_57_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨93, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 93 (by decide)))

theorem fz2_57_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨94, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 94 (by decide)))

theorem fz2_57_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨95, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 95 (by decide)))

theorem fz2_57_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨96, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 96 (by decide)))

theorem fz2_57_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨97, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 97 (by decide)))

theorem fz2_57_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨98, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 98 (by decide)))

theorem fz2_57_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨99, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 99 (by decide)))

theorem fz2_57_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨100, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 100 (by decide)))

theorem fz2_57_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨101, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 101 (by decide)))

theorem fz2_57_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨102, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 102 (by decide)))

theorem fz2_57_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨103, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 103 (by decide)))

theorem fz2_57_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨104, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 104 (by decide)))

theorem fz2_57_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨105, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 105 (by decide)))

theorem fz2_57_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨106, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 106 (by decide)))

theorem fz2_57_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨107, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 107 (by decide)))

theorem fz2_57_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨108, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 108 (by decide)))

theorem fz2_57_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨109, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 109 (by decide)))

theorem fz2_57_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨110, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 110 (by decide)))

theorem fz2_57_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨111, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 111 (by decide)))

theorem fz2_57_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨112, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 112 (by decide)))

theorem fz2_57_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨113, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 113 (by decide)))

theorem fz2_57_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨114, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 114 (by decide)))

theorem fz2_57_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK57)) = 0 :=
  Q2.repsFixedCard2 rK57 ⟨115, by decide⟩ Q2.R57_2 Q2.hpxR57_2 Q2.hcardq57_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_57) 115 (by decide)))

theorem fixz1_58 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 57, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK58) (retConj 1 (R58 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_58_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨1, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 1 (by decide)))

theorem fz1_58_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨2, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 2 (by decide)))

theorem fz1_58_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨3, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 3 (by decide)))

theorem fz1_58_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨4, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 4 (by decide)))

theorem fz1_58_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨5, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 5 (by decide)))

theorem fz1_58_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨7, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 7 (by decide)))

theorem fz1_58_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨8, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 8 (by decide)))

theorem fz1_58_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨9, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 9 (by decide)))

theorem fz1_58_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨10, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 10 (by decide)))

theorem fz1_58_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨11, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 11 (by decide)))

theorem fz1_58_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨13, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 13 (by decide)))

theorem fz1_58_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨14, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 14 (by decide)))

theorem fz1_58_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨15, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 15 (by decide)))

theorem fz1_58_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨16, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 16 (by decide)))

theorem fz1_58_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨17, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 17 (by decide)))

theorem fz1_58_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨18, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 18 (by decide)))

theorem fz1_58_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨19, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 19 (by decide)))

theorem fz1_58_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨20, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 20 (by decide)))

theorem fz1_58_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨21, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 21 (by decide)))

theorem fz1_58_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨22, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 22 (by decide)))

theorem fz1_58_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨23, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 23 (by decide)))

theorem fz1_58_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨25, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 25 (by decide)))

theorem fz1_58_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨26, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 26 (by decide)))

theorem fz1_58_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨27, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 27 (by decide)))

theorem fz1_58_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨29, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 29 (by decide)))

theorem fz1_58_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨30, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 30 (by decide)))

theorem fz1_58_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨31, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 31 (by decide)))

theorem fz1_58_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨32, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 32 (by decide)))

theorem fz1_58_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨34, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 34 (by decide)))

theorem fz1_58_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨35, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 35 (by decide)))

theorem fz1_58_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨36, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 36 (by decide)))

theorem fz1_58_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨37, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 37 (by decide)))

theorem fz1_58_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨39, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 39 (by decide)))

theorem fz1_58_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨40, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 40 (by decide)))

theorem fz1_58_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨41, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 41 (by decide)))

theorem fz1_58_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨42, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 42 (by decide)))

theorem fz1_58_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨44, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 44 (by decide)))

theorem fz1_58_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨45, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 45 (by decide)))

theorem fz1_58_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨46, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 46 (by decide)))

theorem fz1_58_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨47, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 47 (by decide)))

theorem fz1_58_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨49, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 49 (by decide)))

theorem fz1_58_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨50, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 50 (by decide)))

theorem fz1_58_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨51, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 51 (by decide)))

theorem fz1_58_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨52, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 52 (by decide)))

theorem fz1_58_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨53, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 53 (by decide)))

theorem fz1_58_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨54, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 54 (by decide)))

theorem fz1_58_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨55, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 55 (by decide)))

theorem fz1_58_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨56, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 56 (by decide)))

theorem fz1_58_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨57, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 57 (by decide)))

theorem fz1_58_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨59, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 59 (by decide)))

theorem fz1_58_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨60, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 60 (by decide)))

theorem fz1_58_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨61, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 61 (by decide)))

theorem fz1_58_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨62, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 62 (by decide)))

theorem fz1_58_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨63, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 63 (by decide)))

theorem fz1_58_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨64, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 64 (by decide)))

theorem fz1_58_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨65, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 65 (by decide)))

theorem fz1_58_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨66, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 66 (by decide)))

theorem fz1_58_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨67, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 67 (by decide)))

theorem fz1_58_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨68, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 68 (by decide)))

theorem fz1_58_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨69, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 69 (by decide)))

theorem fz1_58_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨70, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 70 (by decide)))

theorem fz1_58_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨71, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 71 (by decide)))

theorem fz1_58_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨72, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 72 (by decide)))

theorem fz1_58_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨73, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 73 (by decide)))

theorem fz1_58_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨74, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 74 (by decide)))

theorem fz1_58_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨75, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 75 (by decide)))

theorem fz1_58_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨76, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 76 (by decide)))

theorem fz1_58_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨77, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 77 (by decide)))

theorem fz1_58_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨78, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 78 (by decide)))

theorem fz1_58_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨79, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 79 (by decide)))

theorem fz1_58_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨80, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 80 (by decide)))

theorem fz1_58_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨81, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 81 (by decide)))

theorem fz1_58_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨82, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 82 (by decide)))

theorem fz1_58_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨83, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 83 (by decide)))

theorem fz1_58_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨84, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 84 (by decide)))

theorem fz1_58_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨85, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 85 (by decide)))

theorem fz1_58_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨86, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 86 (by decide)))

theorem fz1_58_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨87, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 87 (by decide)))

theorem fz1_58_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨88, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 88 (by decide)))

theorem fz1_58_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨89, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 89 (by decide)))

theorem fz1_58_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨90, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 90 (by decide)))

theorem fz1_58_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨91, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 91 (by decide)))

theorem fz1_58_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨92, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 92 (by decide)))

theorem fz1_58_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨93, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 93 (by decide)))

theorem fz1_58_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨94, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 94 (by decide)))

theorem fz1_58_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨95, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 95 (by decide)))

theorem fz1_58_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨96, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 96 (by decide)))

theorem fz1_58_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨97, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 97 (by decide)))

theorem fz1_58_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨98, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 98 (by decide)))

theorem fz1_58_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨99, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 99 (by decide)))

theorem fz1_58_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨100, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 100 (by decide)))

theorem fz1_58_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨101, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 101 (by decide)))

theorem fz1_58_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨102, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 102 (by decide)))

theorem fz1_58_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨103, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 103 (by decide)))

theorem fz1_58_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨104, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 104 (by decide)))

theorem fz1_58_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨105, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 105 (by decide)))

theorem fz1_58_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨106, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 106 (by decide)))

theorem fz1_58_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨107, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 107 (by decide)))

theorem fz1_58_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨108, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 108 (by decide)))

theorem fz1_58_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨109, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 109 (by decide)))

theorem fz1_58_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨110, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 110 (by decide)))

theorem fz1_58_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨111, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 111 (by decide)))

theorem fz1_58_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨112, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 112 (by decide)))

theorem fz1_58_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨113, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 113 (by decide)))

theorem fz1_58_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨114, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 114 (by decide)))

theorem fz1_58_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK58)) = 0 :=
  repsFixedCard rK58 ⟨115, by decide⟩ R58 hpxR58 hcardq58
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_58) 115 (by decide)))

theorem fixz2_58 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 57, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK58) (retConj 2 (Q2.R58_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_58_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨1, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 1 (by decide)))

theorem fz2_58_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨2, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 2 (by decide)))

theorem fz2_58_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨3, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 3 (by decide)))

theorem fz2_58_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨4, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 4 (by decide)))

theorem fz2_58_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨5, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 5 (by decide)))

theorem fz2_58_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨7, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 7 (by decide)))

theorem fz2_58_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨8, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 8 (by decide)))

theorem fz2_58_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨9, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 9 (by decide)))

theorem fz2_58_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨10, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 10 (by decide)))

theorem fz2_58_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨11, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 11 (by decide)))

theorem fz2_58_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨13, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 13 (by decide)))

theorem fz2_58_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨14, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 14 (by decide)))

theorem fz2_58_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨15, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 15 (by decide)))

theorem fz2_58_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨16, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 16 (by decide)))

theorem fz2_58_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨17, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 17 (by decide)))

theorem fz2_58_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨18, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 18 (by decide)))

theorem fz2_58_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨19, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 19 (by decide)))

theorem fz2_58_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨20, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 20 (by decide)))

theorem fz2_58_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨21, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 21 (by decide)))

theorem fz2_58_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨22, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 22 (by decide)))

theorem fz2_58_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨23, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 23 (by decide)))

theorem fz2_58_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨25, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 25 (by decide)))

theorem fz2_58_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨26, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 26 (by decide)))

theorem fz2_58_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨27, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 27 (by decide)))

theorem fz2_58_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨29, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 29 (by decide)))

theorem fz2_58_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨30, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 30 (by decide)))

theorem fz2_58_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨31, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 31 (by decide)))

theorem fz2_58_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨32, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 32 (by decide)))

theorem fz2_58_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨34, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 34 (by decide)))

theorem fz2_58_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨35, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 35 (by decide)))

theorem fz2_58_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨36, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 36 (by decide)))

theorem fz2_58_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨37, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 37 (by decide)))

theorem fz2_58_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨39, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 39 (by decide)))

theorem fz2_58_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨40, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 40 (by decide)))

theorem fz2_58_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨41, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 41 (by decide)))

theorem fz2_58_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨42, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 42 (by decide)))

theorem fz2_58_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨44, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 44 (by decide)))

theorem fz2_58_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨45, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 45 (by decide)))

theorem fz2_58_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨46, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 46 (by decide)))

theorem fz2_58_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨47, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 47 (by decide)))

theorem fz2_58_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨49, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 49 (by decide)))

theorem fz2_58_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨50, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 50 (by decide)))

theorem fz2_58_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨51, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 51 (by decide)))

theorem fz2_58_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨52, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 52 (by decide)))

theorem fz2_58_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨53, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 53 (by decide)))

theorem fz2_58_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨54, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 54 (by decide)))

theorem fz2_58_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨55, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 55 (by decide)))

theorem fz2_58_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨56, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 56 (by decide)))

theorem fz2_58_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨57, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 57 (by decide)))

theorem fz2_58_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨59, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 59 (by decide)))

theorem fz2_58_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨60, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 60 (by decide)))

theorem fz2_58_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨61, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 61 (by decide)))

theorem fz2_58_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨62, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 62 (by decide)))

theorem fz2_58_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨63, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 63 (by decide)))

theorem fz2_58_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨64, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 64 (by decide)))

theorem fz2_58_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨65, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 65 (by decide)))

theorem fz2_58_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨66, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 66 (by decide)))

theorem fz2_58_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨67, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 67 (by decide)))

theorem fz2_58_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨68, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 68 (by decide)))

theorem fz2_58_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨69, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 69 (by decide)))

theorem fz2_58_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨70, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 70 (by decide)))

theorem fz2_58_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨71, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 71 (by decide)))

theorem fz2_58_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨72, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 72 (by decide)))

theorem fz2_58_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨73, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 73 (by decide)))

theorem fz2_58_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨74, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 74 (by decide)))

theorem fz2_58_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨75, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 75 (by decide)))

theorem fz2_58_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨76, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 76 (by decide)))

theorem fz2_58_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨77, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 77 (by decide)))

theorem fz2_58_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨78, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 78 (by decide)))

theorem fz2_58_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨79, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 79 (by decide)))

theorem fz2_58_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨80, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 80 (by decide)))

theorem fz2_58_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨81, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 81 (by decide)))

theorem fz2_58_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨82, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 82 (by decide)))

theorem fz2_58_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨83, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 83 (by decide)))

theorem fz2_58_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨84, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 84 (by decide)))

theorem fz2_58_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨85, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 85 (by decide)))

theorem fz2_58_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨86, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 86 (by decide)))

theorem fz2_58_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨87, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 87 (by decide)))

theorem fz2_58_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨88, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 88 (by decide)))

theorem fz2_58_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨89, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 89 (by decide)))

theorem fz2_58_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨90, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 90 (by decide)))

theorem fz2_58_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨91, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 91 (by decide)))

theorem fz2_58_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨92, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 92 (by decide)))

theorem fz2_58_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨93, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 93 (by decide)))

theorem fz2_58_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨94, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 94 (by decide)))

theorem fz2_58_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨95, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 95 (by decide)))

theorem fz2_58_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨96, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 96 (by decide)))

theorem fz2_58_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨97, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 97 (by decide)))

theorem fz2_58_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨98, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 98 (by decide)))

theorem fz2_58_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨99, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 99 (by decide)))

theorem fz2_58_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨100, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 100 (by decide)))

theorem fz2_58_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨101, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 101 (by decide)))

theorem fz2_58_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨102, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 102 (by decide)))

theorem fz2_58_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨103, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 103 (by decide)))

theorem fz2_58_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨104, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 104 (by decide)))

theorem fz2_58_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨105, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 105 (by decide)))

theorem fz2_58_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨106, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 106 (by decide)))

theorem fz2_58_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨107, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 107 (by decide)))

theorem fz2_58_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨108, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 108 (by decide)))

theorem fz2_58_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨109, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 109 (by decide)))

theorem fz2_58_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨110, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 110 (by decide)))

theorem fz2_58_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨111, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 111 (by decide)))

theorem fz2_58_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨112, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 112 (by decide)))

theorem fz2_58_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨113, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 113 (by decide)))

theorem fz2_58_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨114, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 114 (by decide)))

theorem fz2_58_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK58)) = 0 :=
  Q2.repsFixedCard2 rK58 ⟨115, by decide⟩ Q2.R58_2 Q2.hpxR58_2 Q2.hcardq58_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_58) 115 (by decide)))

end LeanDring.P5Presentation
