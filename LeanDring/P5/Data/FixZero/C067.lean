/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C018
import LeanDring.P5.Data.EntryK.C019

/-!
# Species-table cells, off-support emptiness certificates, chunk 66

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

theorem fixz1_79 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK79) (retConj 1 (R79 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_79_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨1, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 1 (by decide)))

theorem fz1_79_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨2, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 2 (by decide)))

theorem fz1_79_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨3, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 3 (by decide)))

theorem fz1_79_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨4, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 4 (by decide)))

theorem fz1_79_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨5, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 5 (by decide)))

theorem fz1_79_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨6, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 6 (by decide)))

theorem fz1_79_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨7, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 7 (by decide)))

theorem fz1_79_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨9, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 9 (by decide)))

theorem fz1_79_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨10, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 10 (by decide)))

theorem fz1_79_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨11, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 11 (by decide)))

theorem fz1_79_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨13, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 13 (by decide)))

theorem fz1_79_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨14, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 14 (by decide)))

theorem fz1_79_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨15, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 15 (by decide)))

theorem fz1_79_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨16, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 16 (by decide)))

theorem fz1_79_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨17, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 17 (by decide)))

theorem fz1_79_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨18, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 18 (by decide)))

theorem fz1_79_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨19, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 19 (by decide)))

theorem fz1_79_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨20, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 20 (by decide)))

theorem fz1_79_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨21, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 21 (by decide)))

theorem fz1_79_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨22, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 22 (by decide)))

theorem fz1_79_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨23, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 23 (by decide)))

theorem fz1_79_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨24, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 24 (by decide)))

theorem fz1_79_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨25, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 25 (by decide)))

theorem fz1_79_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨27, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 27 (by decide)))

theorem fz1_79_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨28, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 28 (by decide)))

theorem fz1_79_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨29, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 29 (by decide)))

theorem fz1_79_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨30, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 30 (by decide)))

theorem fz1_79_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨31, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 31 (by decide)))

theorem fz1_79_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨33, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 33 (by decide)))

theorem fz1_79_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨34, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 34 (by decide)))

theorem fz1_79_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨35, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 35 (by decide)))

theorem fz1_79_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨36, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 36 (by decide)))

theorem fz1_79_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨38, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 38 (by decide)))

theorem fz1_79_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨39, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 39 (by decide)))

theorem fz1_79_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨40, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 40 (by decide)))

theorem fz1_79_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨41, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 41 (by decide)))

theorem fz1_79_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨43, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 43 (by decide)))

theorem fz1_79_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨44, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 44 (by decide)))

theorem fz1_79_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨45, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 45 (by decide)))

theorem fz1_79_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨46, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 46 (by decide)))

theorem fz1_79_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨48, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 48 (by decide)))

theorem fz1_79_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨49, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 49 (by decide)))

theorem fz1_79_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨50, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 50 (by decide)))

theorem fz1_79_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨51, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 51 (by decide)))

theorem fz1_79_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨53, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 53 (by decide)))

theorem fz1_79_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨54, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 54 (by decide)))

theorem fz1_79_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨55, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 55 (by decide)))

theorem fz1_79_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨56, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 56 (by decide)))

theorem fz1_79_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨57, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 57 (by decide)))

theorem fz1_79_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨58, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 58 (by decide)))

theorem fz1_79_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨59, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 59 (by decide)))

theorem fz1_79_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨60, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 60 (by decide)))

theorem fz1_79_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨61, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 61 (by decide)))

theorem fz1_79_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨62, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 62 (by decide)))

theorem fz1_79_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨63, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 63 (by decide)))

theorem fz1_79_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨64, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 64 (by decide)))

theorem fz1_79_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨65, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 65 (by decide)))

theorem fz1_79_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨66, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 66 (by decide)))

theorem fz1_79_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨67, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 67 (by decide)))

theorem fz1_79_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨68, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 68 (by decide)))

theorem fz1_79_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨69, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 69 (by decide)))

theorem fz1_79_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨70, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 70 (by decide)))

theorem fz1_79_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨71, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 71 (by decide)))

theorem fz1_79_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨72, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 72 (by decide)))

theorem fz1_79_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨73, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 73 (by decide)))

theorem fz1_79_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨74, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 74 (by decide)))

theorem fz1_79_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨75, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 75 (by decide)))

theorem fz1_79_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨76, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 76 (by decide)))

theorem fz1_79_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨77, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 77 (by decide)))

theorem fz1_79_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨78, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 78 (by decide)))

theorem fz1_79_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨80, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 80 (by decide)))

theorem fz1_79_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨81, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 81 (by decide)))

theorem fz1_79_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨82, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 82 (by decide)))

theorem fz1_79_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨83, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 83 (by decide)))

theorem fz1_79_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨84, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 84 (by decide)))

theorem fz1_79_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨85, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 85 (by decide)))

theorem fz1_79_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨86, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 86 (by decide)))

theorem fz1_79_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨87, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 87 (by decide)))

theorem fz1_79_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨88, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 88 (by decide)))

theorem fz1_79_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨89, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 89 (by decide)))

theorem fz1_79_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨90, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 90 (by decide)))

theorem fz1_79_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨91, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 91 (by decide)))

theorem fz1_79_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨92, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 92 (by decide)))

theorem fz1_79_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨93, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 93 (by decide)))

theorem fz1_79_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨94, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 94 (by decide)))

theorem fz1_79_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨95, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 95 (by decide)))

theorem fz1_79_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨96, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 96 (by decide)))

theorem fz1_79_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨97, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 97 (by decide)))

theorem fz1_79_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨98, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 98 (by decide)))

theorem fz1_79_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨99, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 99 (by decide)))

theorem fz1_79_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨100, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 100 (by decide)))

theorem fz1_79_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨101, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 101 (by decide)))

theorem fz1_79_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨102, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 102 (by decide)))

theorem fz1_79_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨103, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 103 (by decide)))

theorem fz1_79_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨104, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 104 (by decide)))

theorem fz1_79_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨105, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 105 (by decide)))

theorem fz1_79_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨106, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 106 (by decide)))

theorem fz1_79_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨107, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 107 (by decide)))

theorem fz1_79_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨108, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 108 (by decide)))

theorem fz1_79_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨109, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 109 (by decide)))

theorem fz1_79_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨110, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 110 (by decide)))

theorem fz1_79_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨111, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 111 (by decide)))

theorem fz1_79_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨112, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 112 (by decide)))

theorem fz1_79_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨113, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 113 (by decide)))

theorem fz1_79_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨114, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 114 (by decide)))

theorem fz1_79_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK79)) = 0 :=
  repsFixedCard rK79 ⟨115, by decide⟩ R79 hpxR79 hcardq79
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_79) 115 (by decide)))

theorem fixz2_79 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK79) (retConj 2 (Q2.R79_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_79_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨1, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 1 (by decide)))

theorem fz2_79_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨2, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 2 (by decide)))

theorem fz2_79_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨3, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 3 (by decide)))

theorem fz2_79_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨4, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 4 (by decide)))

theorem fz2_79_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨5, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 5 (by decide)))

theorem fz2_79_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨6, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 6 (by decide)))

theorem fz2_79_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨7, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 7 (by decide)))

theorem fz2_79_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨9, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 9 (by decide)))

theorem fz2_79_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨10, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 10 (by decide)))

theorem fz2_79_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨11, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 11 (by decide)))

theorem fz2_79_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨13, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 13 (by decide)))

theorem fz2_79_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨14, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 14 (by decide)))

theorem fz2_79_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨15, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 15 (by decide)))

theorem fz2_79_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨16, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 16 (by decide)))

theorem fz2_79_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨17, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 17 (by decide)))

theorem fz2_79_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨18, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 18 (by decide)))

theorem fz2_79_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨19, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 19 (by decide)))

theorem fz2_79_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨20, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 20 (by decide)))

theorem fz2_79_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨21, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 21 (by decide)))

theorem fz2_79_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨22, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 22 (by decide)))

theorem fz2_79_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨23, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 23 (by decide)))

theorem fz2_79_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨24, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 24 (by decide)))

theorem fz2_79_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨25, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 25 (by decide)))

theorem fz2_79_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨27, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 27 (by decide)))

theorem fz2_79_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨28, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 28 (by decide)))

theorem fz2_79_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨29, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 29 (by decide)))

theorem fz2_79_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨30, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 30 (by decide)))

theorem fz2_79_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨31, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 31 (by decide)))

theorem fz2_79_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨33, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 33 (by decide)))

theorem fz2_79_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨34, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 34 (by decide)))

theorem fz2_79_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨35, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 35 (by decide)))

theorem fz2_79_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨36, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 36 (by decide)))

theorem fz2_79_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨38, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 38 (by decide)))

theorem fz2_79_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨39, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 39 (by decide)))

theorem fz2_79_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨40, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 40 (by decide)))

theorem fz2_79_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨41, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 41 (by decide)))

theorem fz2_79_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨43, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 43 (by decide)))

theorem fz2_79_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨44, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 44 (by decide)))

theorem fz2_79_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨45, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 45 (by decide)))

theorem fz2_79_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨46, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 46 (by decide)))

theorem fz2_79_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨48, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 48 (by decide)))

theorem fz2_79_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨49, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 49 (by decide)))

theorem fz2_79_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨50, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 50 (by decide)))

theorem fz2_79_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨51, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 51 (by decide)))

theorem fz2_79_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨53, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 53 (by decide)))

theorem fz2_79_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨54, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 54 (by decide)))

theorem fz2_79_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨55, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 55 (by decide)))

theorem fz2_79_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨56, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 56 (by decide)))

theorem fz2_79_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨57, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 57 (by decide)))

theorem fz2_79_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨58, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 58 (by decide)))

theorem fz2_79_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨59, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 59 (by decide)))

theorem fz2_79_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨60, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 60 (by decide)))

theorem fz2_79_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨61, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 61 (by decide)))

theorem fz2_79_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨62, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 62 (by decide)))

theorem fz2_79_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨63, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 63 (by decide)))

theorem fz2_79_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨64, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 64 (by decide)))

theorem fz2_79_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨65, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 65 (by decide)))

theorem fz2_79_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨66, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 66 (by decide)))

theorem fz2_79_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨67, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 67 (by decide)))

theorem fz2_79_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨68, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 68 (by decide)))

theorem fz2_79_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨69, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 69 (by decide)))

theorem fz2_79_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨70, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 70 (by decide)))

theorem fz2_79_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨71, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 71 (by decide)))

theorem fz2_79_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨72, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 72 (by decide)))

theorem fz2_79_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨73, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 73 (by decide)))

theorem fz2_79_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨74, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 74 (by decide)))

theorem fz2_79_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨75, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 75 (by decide)))

theorem fz2_79_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨76, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 76 (by decide)))

theorem fz2_79_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨77, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 77 (by decide)))

theorem fz2_79_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨78, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 78 (by decide)))

theorem fz2_79_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨80, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 80 (by decide)))

theorem fz2_79_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨81, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 81 (by decide)))

theorem fz2_79_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨82, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 82 (by decide)))

theorem fz2_79_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨83, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 83 (by decide)))

theorem fz2_79_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨84, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 84 (by decide)))

theorem fz2_79_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨85, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 85 (by decide)))

theorem fz2_79_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨86, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 86 (by decide)))

theorem fz2_79_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨87, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 87 (by decide)))

theorem fz2_79_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨88, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 88 (by decide)))

theorem fz2_79_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨89, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 89 (by decide)))

theorem fz2_79_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨90, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 90 (by decide)))

theorem fz2_79_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨91, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 91 (by decide)))

theorem fz2_79_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨92, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 92 (by decide)))

theorem fz2_79_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨93, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 93 (by decide)))

theorem fz2_79_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨94, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 94 (by decide)))

theorem fz2_79_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨95, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 95 (by decide)))

theorem fz2_79_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨96, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 96 (by decide)))

theorem fz2_79_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨97, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 97 (by decide)))

theorem fz2_79_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨98, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 98 (by decide)))

theorem fz2_79_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨99, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 99 (by decide)))

theorem fz2_79_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨100, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 100 (by decide)))

theorem fz2_79_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨101, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 101 (by decide)))

theorem fz2_79_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨102, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 102 (by decide)))

theorem fz2_79_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨103, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 103 (by decide)))

theorem fz2_79_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨104, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 104 (by decide)))

theorem fz2_79_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨105, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 105 (by decide)))

theorem fz2_79_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨106, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 106 (by decide)))

theorem fz2_79_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨107, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 107 (by decide)))

theorem fz2_79_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨108, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 108 (by decide)))

theorem fz2_79_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨109, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 109 (by decide)))

theorem fz2_79_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨110, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 110 (by decide)))

theorem fz2_79_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨111, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 111 (by decide)))

theorem fz2_79_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨112, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 112 (by decide)))

theorem fz2_79_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨113, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 113 (by decide)))

theorem fz2_79_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨114, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 114 (by decide)))

theorem fz2_79_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK79)) = 0 :=
  Q2.repsFixedCard2 rK79 ⟨115, by decide⟩ Q2.R79_2 Q2.hpxR79_2 Q2.hcardq79_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_79) 115 (by decide)))

theorem fixz1_80 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK80) (retConj 1 (R80 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_80_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨2, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 2 (by decide)))

theorem fz1_80_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨3, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 3 (by decide)))

theorem fz1_80_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨4, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 4 (by decide)))

theorem fz1_80_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨5, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 5 (by decide)))

theorem fz1_80_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨11, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 11 (by decide)))

theorem fz1_80_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨14, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 14 (by decide)))

theorem fz1_80_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨15, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 15 (by decide)))

theorem fz1_80_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨16, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 16 (by decide)))

theorem fz1_80_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨17, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 17 (by decide)))

theorem fz1_80_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨18, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 18 (by decide)))

theorem fz1_80_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨20, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 20 (by decide)))

theorem fz1_80_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨21, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 21 (by decide)))

theorem fz1_80_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨22, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 22 (by decide)))

theorem fz1_80_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨23, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 23 (by decide)))

theorem fz1_80_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨28, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 28 (by decide)))

theorem fz1_80_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨29, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 29 (by decide)))

theorem fz1_80_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨30, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 30 (by decide)))

theorem fz1_80_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨31, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 31 (by decide)))

theorem fz1_80_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨32, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 32 (by decide)))

theorem fz1_80_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨33, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 33 (by decide)))

theorem fz1_80_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨34, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 34 (by decide)))

theorem fz1_80_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨35, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 35 (by decide)))

theorem fz1_80_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨36, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 36 (by decide)))

theorem fz1_80_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨37, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 37 (by decide)))

theorem fz1_80_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨38, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 38 (by decide)))

theorem fz1_80_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨39, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 39 (by decide)))

theorem fz1_80_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨40, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 40 (by decide)))

theorem fz1_80_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨41, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 41 (by decide)))

theorem fz1_80_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨42, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 42 (by decide)))

theorem fz1_80_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨43, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 43 (by decide)))

theorem fz1_80_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨44, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 44 (by decide)))

theorem fz1_80_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨45, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 45 (by decide)))

theorem fz1_80_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨46, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 46 (by decide)))

theorem fz1_80_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨47, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 47 (by decide)))

theorem fz1_80_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨48, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 48 (by decide)))

theorem fz1_80_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨49, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 49 (by decide)))

theorem fz1_80_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨50, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 50 (by decide)))

theorem fz1_80_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨51, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 51 (by decide)))

theorem fz1_80_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨52, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 52 (by decide)))

theorem fz1_80_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨54, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 54 (by decide)))

theorem fz1_80_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨55, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 55 (by decide)))

theorem fz1_80_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨56, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 56 (by decide)))

theorem fz1_80_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨57, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 57 (by decide)))

theorem fz1_80_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨58, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 58 (by decide)))

theorem fz1_80_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨59, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 59 (by decide)))

theorem fz1_80_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨60, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 60 (by decide)))

theorem fz1_80_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨61, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 61 (by decide)))

theorem fz1_80_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨62, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 62 (by decide)))

theorem fz1_80_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨63, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 63 (by decide)))

theorem fz1_80_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨64, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 64 (by decide)))

theorem fz1_80_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨65, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 65 (by decide)))

theorem fz1_80_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨66, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 66 (by decide)))

theorem fz1_80_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨67, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 67 (by decide)))

theorem fz1_80_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨68, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 68 (by decide)))

theorem fz1_80_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨69, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 69 (by decide)))

theorem fz1_80_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨70, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 70 (by decide)))

theorem fz1_80_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨71, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 71 (by decide)))

theorem fz1_80_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨72, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 72 (by decide)))

theorem fz1_80_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨73, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 73 (by decide)))

theorem fz1_80_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨74, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 74 (by decide)))

theorem fz1_80_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨75, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 75 (by decide)))

theorem fz1_80_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨76, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 76 (by decide)))

theorem fz1_80_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨77, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 77 (by decide)))

theorem fz1_80_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨78, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 78 (by decide)))

theorem fz1_80_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨79, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 79 (by decide)))

theorem fz1_80_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨81, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 81 (by decide)))

theorem fz1_80_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨82, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 82 (by decide)))

theorem fz1_80_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨83, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 83 (by decide)))

theorem fz1_80_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨84, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 84 (by decide)))

theorem fz1_80_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨85, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 85 (by decide)))

theorem fz1_80_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨86, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 86 (by decide)))

theorem fz1_80_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨87, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 87 (by decide)))

theorem fz1_80_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨88, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 88 (by decide)))

theorem fz1_80_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨89, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 89 (by decide)))

theorem fz1_80_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨90, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 90 (by decide)))

theorem fz1_80_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨91, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 91 (by decide)))

theorem fz1_80_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨92, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 92 (by decide)))

theorem fz1_80_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨93, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 93 (by decide)))

theorem fz1_80_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨94, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 94 (by decide)))

theorem fz1_80_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨95, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 95 (by decide)))

theorem fz1_80_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨96, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 96 (by decide)))

theorem fz1_80_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨97, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 97 (by decide)))

theorem fz1_80_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨98, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 98 (by decide)))

theorem fz1_80_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨99, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 99 (by decide)))

theorem fz1_80_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨100, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 100 (by decide)))

theorem fz1_80_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨101, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 101 (by decide)))

theorem fz1_80_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨102, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 102 (by decide)))

theorem fz1_80_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨103, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 103 (by decide)))

theorem fz1_80_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨104, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 104 (by decide)))

theorem fz1_80_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨105, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 105 (by decide)))

theorem fz1_80_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨106, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 106 (by decide)))

theorem fz1_80_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨107, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 107 (by decide)))

theorem fz1_80_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨108, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 108 (by decide)))

theorem fz1_80_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨109, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 109 (by decide)))

theorem fz1_80_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨110, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 110 (by decide)))

theorem fz1_80_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨111, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 111 (by decide)))

theorem fz1_80_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨112, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 112 (by decide)))

theorem fz1_80_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨113, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 113 (by decide)))

theorem fz1_80_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨114, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 114 (by decide)))

theorem fz1_80_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK80)) = 0 :=
  repsFixedCard rK80 ⟨115, by decide⟩ R80 hpxR80 hcardq80
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_80) 115 (by decide)))

theorem fixz2_80 : ([2, 3, 4, 5, 11, 14, 15, 16, 17, 18, 20, 21, 22, 23, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK80) (retConj 2 (Q2.R80_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_80_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨2, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 2 (by decide)))

theorem fz2_80_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨3, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 3 (by decide)))

theorem fz2_80_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨4, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 4 (by decide)))

theorem fz2_80_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨5, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 5 (by decide)))

theorem fz2_80_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨11, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 11 (by decide)))

theorem fz2_80_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨14, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 14 (by decide)))

theorem fz2_80_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨15, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 15 (by decide)))

theorem fz2_80_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨16, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 16 (by decide)))

theorem fz2_80_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨17, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 17 (by decide)))

theorem fz2_80_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨18, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 18 (by decide)))

theorem fz2_80_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨20, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 20 (by decide)))

theorem fz2_80_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨21, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 21 (by decide)))

theorem fz2_80_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨22, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 22 (by decide)))

theorem fz2_80_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨23, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 23 (by decide)))

theorem fz2_80_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨28, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 28 (by decide)))

theorem fz2_80_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨29, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 29 (by decide)))

theorem fz2_80_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨30, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 30 (by decide)))

theorem fz2_80_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨31, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 31 (by decide)))

theorem fz2_80_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨32, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 32 (by decide)))

theorem fz2_80_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨33, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 33 (by decide)))

theorem fz2_80_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨34, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 34 (by decide)))

theorem fz2_80_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨35, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 35 (by decide)))

theorem fz2_80_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨36, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 36 (by decide)))

theorem fz2_80_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨37, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 37 (by decide)))

theorem fz2_80_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨38, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 38 (by decide)))

theorem fz2_80_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨39, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 39 (by decide)))

theorem fz2_80_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨40, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 40 (by decide)))

theorem fz2_80_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨41, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 41 (by decide)))

theorem fz2_80_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨42, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 42 (by decide)))

theorem fz2_80_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨43, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 43 (by decide)))

theorem fz2_80_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨44, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 44 (by decide)))

theorem fz2_80_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨45, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 45 (by decide)))

theorem fz2_80_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨46, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 46 (by decide)))

theorem fz2_80_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨47, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 47 (by decide)))

theorem fz2_80_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨48, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 48 (by decide)))

theorem fz2_80_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨49, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 49 (by decide)))

theorem fz2_80_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨50, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 50 (by decide)))

theorem fz2_80_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨51, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 51 (by decide)))

theorem fz2_80_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨52, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 52 (by decide)))

theorem fz2_80_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨54, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 54 (by decide)))

theorem fz2_80_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨55, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 55 (by decide)))

theorem fz2_80_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨56, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 56 (by decide)))

theorem fz2_80_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨57, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 57 (by decide)))

theorem fz2_80_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨58, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 58 (by decide)))

theorem fz2_80_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨59, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 59 (by decide)))

theorem fz2_80_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨60, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 60 (by decide)))

theorem fz2_80_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨61, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 61 (by decide)))

theorem fz2_80_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨62, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 62 (by decide)))

theorem fz2_80_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨63, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 63 (by decide)))

theorem fz2_80_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨64, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 64 (by decide)))

theorem fz2_80_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨65, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 65 (by decide)))

theorem fz2_80_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨66, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 66 (by decide)))

theorem fz2_80_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨67, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 67 (by decide)))

theorem fz2_80_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨68, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 68 (by decide)))

theorem fz2_80_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨69, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 69 (by decide)))

theorem fz2_80_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨70, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 70 (by decide)))

theorem fz2_80_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨71, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 71 (by decide)))

theorem fz2_80_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨72, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 72 (by decide)))

theorem fz2_80_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨73, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 73 (by decide)))

theorem fz2_80_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨74, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 74 (by decide)))

theorem fz2_80_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨75, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 75 (by decide)))

theorem fz2_80_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨76, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 76 (by decide)))

theorem fz2_80_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨77, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 77 (by decide)))

theorem fz2_80_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨78, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 78 (by decide)))

theorem fz2_80_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨79, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 79 (by decide)))

theorem fz2_80_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨81, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 81 (by decide)))

theorem fz2_80_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨82, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 82 (by decide)))

theorem fz2_80_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨83, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 83 (by decide)))

theorem fz2_80_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨84, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 84 (by decide)))

theorem fz2_80_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨85, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 85 (by decide)))

theorem fz2_80_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨86, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 86 (by decide)))

theorem fz2_80_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨87, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 87 (by decide)))

theorem fz2_80_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨88, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 88 (by decide)))

theorem fz2_80_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨89, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 89 (by decide)))

theorem fz2_80_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨90, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 90 (by decide)))

theorem fz2_80_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨91, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 91 (by decide)))

theorem fz2_80_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨92, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 92 (by decide)))

theorem fz2_80_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨93, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 93 (by decide)))

theorem fz2_80_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨94, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 94 (by decide)))

theorem fz2_80_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨95, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 95 (by decide)))

theorem fz2_80_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨96, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 96 (by decide)))

theorem fz2_80_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨97, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 97 (by decide)))

theorem fz2_80_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨98, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 98 (by decide)))

theorem fz2_80_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨99, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 99 (by decide)))

theorem fz2_80_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨100, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 100 (by decide)))

theorem fz2_80_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨101, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 101 (by decide)))

theorem fz2_80_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨102, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 102 (by decide)))

theorem fz2_80_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨103, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 103 (by decide)))

theorem fz2_80_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨104, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 104 (by decide)))

theorem fz2_80_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨105, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 105 (by decide)))

theorem fz2_80_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨106, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 106 (by decide)))

theorem fz2_80_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨107, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 107 (by decide)))

theorem fz2_80_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨108, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 108 (by decide)))

theorem fz2_80_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨109, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 109 (by decide)))

theorem fz2_80_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨110, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 110 (by decide)))

theorem fz2_80_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨111, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 111 (by decide)))

theorem fz2_80_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨112, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 112 (by decide)))

theorem fz2_80_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨113, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 113 (by decide)))

theorem fz2_80_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨114, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 114 (by decide)))

theorem fz2_80_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK80)) = 0 :=
  Q2.repsFixedCard2 rK80 ⟨115, by decide⟩ Q2.R80_2 Q2.hpxR80_2 Q2.hcardq80_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_80) 115 (by decide)))

end LeanDring.P5Presentation
