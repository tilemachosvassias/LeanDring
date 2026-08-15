/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C014
import LeanDring.P5.Data.EntryK.C015

/-!
# Species-table cells, off-support emptiness certificates, chunk 56

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

theorem fixz1_59 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK59) (retConj 1 (R59 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_59_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨1, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 1 (by decide)))

theorem fz1_59_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨2, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 2 (by decide)))

theorem fz1_59_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨3, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 3 (by decide)))

theorem fz1_59_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨4, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 4 (by decide)))

theorem fz1_59_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨5, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 5 (by decide)))

theorem fz1_59_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨6, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 6 (by decide)))

theorem fz1_59_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨7, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 7 (by decide)))

theorem fz1_59_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨9, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 9 (by decide)))

theorem fz1_59_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨10, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 10 (by decide)))

theorem fz1_59_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨11, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 11 (by decide)))

theorem fz1_59_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨13, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 13 (by decide)))

theorem fz1_59_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨14, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 14 (by decide)))

theorem fz1_59_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨15, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 15 (by decide)))

theorem fz1_59_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨16, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 16 (by decide)))

theorem fz1_59_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨17, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 17 (by decide)))

theorem fz1_59_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨18, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 18 (by decide)))

theorem fz1_59_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨19, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 19 (by decide)))

theorem fz1_59_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨20, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 20 (by decide)))

theorem fz1_59_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨21, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 21 (by decide)))

theorem fz1_59_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨22, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 22 (by decide)))

theorem fz1_59_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨23, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 23 (by decide)))

theorem fz1_59_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨24, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 24 (by decide)))

theorem fz1_59_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨25, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 25 (by decide)))

theorem fz1_59_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨27, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 27 (by decide)))

theorem fz1_59_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨29, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 29 (by decide)))

theorem fz1_59_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨30, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 30 (by decide)))

theorem fz1_59_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨31, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 31 (by decide)))

theorem fz1_59_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨32, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 32 (by decide)))

theorem fz1_59_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨34, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 34 (by decide)))

theorem fz1_59_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨35, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 35 (by decide)))

theorem fz1_59_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨36, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 36 (by decide)))

theorem fz1_59_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨37, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 37 (by decide)))

theorem fz1_59_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨39, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 39 (by decide)))

theorem fz1_59_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨40, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 40 (by decide)))

theorem fz1_59_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨41, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 41 (by decide)))

theorem fz1_59_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨42, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 42 (by decide)))

theorem fz1_59_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨44, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 44 (by decide)))

theorem fz1_59_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨45, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 45 (by decide)))

theorem fz1_59_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨46, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 46 (by decide)))

theorem fz1_59_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨47, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 47 (by decide)))

theorem fz1_59_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨49, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 49 (by decide)))

theorem fz1_59_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨50, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 50 (by decide)))

theorem fz1_59_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨51, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 51 (by decide)))

theorem fz1_59_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨52, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 52 (by decide)))

theorem fz1_59_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨53, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 53 (by decide)))

theorem fz1_59_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨54, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 54 (by decide)))

theorem fz1_59_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨55, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 55 (by decide)))

theorem fz1_59_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨56, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 56 (by decide)))

theorem fz1_59_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨57, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 57 (by decide)))

theorem fz1_59_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨58, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 58 (by decide)))

theorem fz1_59_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨60, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 60 (by decide)))

theorem fz1_59_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨61, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 61 (by decide)))

theorem fz1_59_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨62, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 62 (by decide)))

theorem fz1_59_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨63, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 63 (by decide)))

theorem fz1_59_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨64, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 64 (by decide)))

theorem fz1_59_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨65, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 65 (by decide)))

theorem fz1_59_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨66, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 66 (by decide)))

theorem fz1_59_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨67, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 67 (by decide)))

theorem fz1_59_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨68, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 68 (by decide)))

theorem fz1_59_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨69, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 69 (by decide)))

theorem fz1_59_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨70, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 70 (by decide)))

theorem fz1_59_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨71, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 71 (by decide)))

theorem fz1_59_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨72, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 72 (by decide)))

theorem fz1_59_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨73, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 73 (by decide)))

theorem fz1_59_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨74, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 74 (by decide)))

theorem fz1_59_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨75, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 75 (by decide)))

theorem fz1_59_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨76, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 76 (by decide)))

theorem fz1_59_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨77, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 77 (by decide)))

theorem fz1_59_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨78, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 78 (by decide)))

theorem fz1_59_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨79, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 79 (by decide)))

theorem fz1_59_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨80, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 80 (by decide)))

theorem fz1_59_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨81, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 81 (by decide)))

theorem fz1_59_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨82, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 82 (by decide)))

theorem fz1_59_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨83, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 83 (by decide)))

theorem fz1_59_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨84, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 84 (by decide)))

theorem fz1_59_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨85, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 85 (by decide)))

theorem fz1_59_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨86, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 86 (by decide)))

theorem fz1_59_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨87, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 87 (by decide)))

theorem fz1_59_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨88, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 88 (by decide)))

theorem fz1_59_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨89, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 89 (by decide)))

theorem fz1_59_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨90, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 90 (by decide)))

theorem fz1_59_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨91, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 91 (by decide)))

theorem fz1_59_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨92, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 92 (by decide)))

theorem fz1_59_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨93, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 93 (by decide)))

theorem fz1_59_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨94, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 94 (by decide)))

theorem fz1_59_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨95, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 95 (by decide)))

theorem fz1_59_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨96, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 96 (by decide)))

theorem fz1_59_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨97, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 97 (by decide)))

theorem fz1_59_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨98, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 98 (by decide)))

theorem fz1_59_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨99, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 99 (by decide)))

theorem fz1_59_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨100, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 100 (by decide)))

theorem fz1_59_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨101, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 101 (by decide)))

theorem fz1_59_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨102, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 102 (by decide)))

theorem fz1_59_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨103, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 103 (by decide)))

theorem fz1_59_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨104, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 104 (by decide)))

theorem fz1_59_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨105, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 105 (by decide)))

theorem fz1_59_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨106, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 106 (by decide)))

theorem fz1_59_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨107, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 107 (by decide)))

theorem fz1_59_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨108, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 108 (by decide)))

theorem fz1_59_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨109, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 109 (by decide)))

theorem fz1_59_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨110, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 110 (by decide)))

theorem fz1_59_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨111, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 111 (by decide)))

theorem fz1_59_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨112, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 112 (by decide)))

theorem fz1_59_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨113, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 113 (by decide)))

theorem fz1_59_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨114, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 114 (by decide)))

theorem fz1_59_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK59)) = 0 :=
  repsFixedCard rK59 ⟨115, by decide⟩ R59 hpxR59 hcardq59
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_59) 115 (by decide)))

theorem fixz2_59 : ([1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41, 42, 44, 45, 46, 47, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK59) (retConj 2 (Q2.R59_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_59_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨1, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 1 (by decide)))

theorem fz2_59_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨2, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 2 (by decide)))

theorem fz2_59_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨3, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 3 (by decide)))

theorem fz2_59_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨4, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 4 (by decide)))

theorem fz2_59_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨5, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 5 (by decide)))

theorem fz2_59_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨6, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 6 (by decide)))

theorem fz2_59_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨7, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 7 (by decide)))

theorem fz2_59_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨9, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 9 (by decide)))

theorem fz2_59_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨10, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 10 (by decide)))

theorem fz2_59_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨11, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 11 (by decide)))

theorem fz2_59_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨13, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 13 (by decide)))

theorem fz2_59_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨14, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 14 (by decide)))

theorem fz2_59_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨15, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 15 (by decide)))

theorem fz2_59_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨16, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 16 (by decide)))

theorem fz2_59_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨17, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 17 (by decide)))

theorem fz2_59_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨18, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 18 (by decide)))

theorem fz2_59_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨19, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 19 (by decide)))

theorem fz2_59_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨20, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 20 (by decide)))

theorem fz2_59_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨21, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 21 (by decide)))

theorem fz2_59_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨22, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 22 (by decide)))

theorem fz2_59_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨23, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 23 (by decide)))

theorem fz2_59_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨24, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 24 (by decide)))

theorem fz2_59_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨25, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 25 (by decide)))

theorem fz2_59_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨27, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 27 (by decide)))

theorem fz2_59_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨29, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 29 (by decide)))

theorem fz2_59_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨30, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 30 (by decide)))

theorem fz2_59_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨31, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 31 (by decide)))

theorem fz2_59_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨32, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 32 (by decide)))

theorem fz2_59_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨34, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 34 (by decide)))

theorem fz2_59_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨35, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 35 (by decide)))

theorem fz2_59_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨36, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 36 (by decide)))

theorem fz2_59_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨37, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 37 (by decide)))

theorem fz2_59_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨39, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 39 (by decide)))

theorem fz2_59_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨40, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 40 (by decide)))

theorem fz2_59_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨41, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 41 (by decide)))

theorem fz2_59_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨42, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 42 (by decide)))

theorem fz2_59_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨44, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 44 (by decide)))

theorem fz2_59_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨45, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 45 (by decide)))

theorem fz2_59_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨46, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 46 (by decide)))

theorem fz2_59_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨47, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 47 (by decide)))

theorem fz2_59_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨49, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 49 (by decide)))

theorem fz2_59_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨50, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 50 (by decide)))

theorem fz2_59_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨51, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 51 (by decide)))

theorem fz2_59_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨52, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 52 (by decide)))

theorem fz2_59_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨53, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 53 (by decide)))

theorem fz2_59_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨54, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 54 (by decide)))

theorem fz2_59_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨55, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 55 (by decide)))

theorem fz2_59_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨56, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 56 (by decide)))

theorem fz2_59_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨57, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 57 (by decide)))

theorem fz2_59_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨58, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 58 (by decide)))

theorem fz2_59_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨60, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 60 (by decide)))

theorem fz2_59_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨61, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 61 (by decide)))

theorem fz2_59_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨62, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 62 (by decide)))

theorem fz2_59_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨63, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 63 (by decide)))

theorem fz2_59_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨64, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 64 (by decide)))

theorem fz2_59_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨65, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 65 (by decide)))

theorem fz2_59_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨66, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 66 (by decide)))

theorem fz2_59_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨67, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 67 (by decide)))

theorem fz2_59_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨68, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 68 (by decide)))

theorem fz2_59_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨69, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 69 (by decide)))

theorem fz2_59_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨70, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 70 (by decide)))

theorem fz2_59_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨71, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 71 (by decide)))

theorem fz2_59_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨72, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 72 (by decide)))

theorem fz2_59_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨73, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 73 (by decide)))

theorem fz2_59_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨74, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 74 (by decide)))

theorem fz2_59_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨75, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 75 (by decide)))

theorem fz2_59_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨76, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 76 (by decide)))

theorem fz2_59_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨77, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 77 (by decide)))

theorem fz2_59_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨78, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 78 (by decide)))

theorem fz2_59_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨79, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 79 (by decide)))

theorem fz2_59_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨80, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 80 (by decide)))

theorem fz2_59_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨81, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 81 (by decide)))

theorem fz2_59_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨82, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 82 (by decide)))

theorem fz2_59_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨83, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 83 (by decide)))

theorem fz2_59_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨84, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 84 (by decide)))

theorem fz2_59_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨85, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 85 (by decide)))

theorem fz2_59_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨86, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 86 (by decide)))

theorem fz2_59_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨87, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 87 (by decide)))

theorem fz2_59_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨88, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 88 (by decide)))

theorem fz2_59_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨89, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 89 (by decide)))

theorem fz2_59_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨90, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 90 (by decide)))

theorem fz2_59_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨91, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 91 (by decide)))

theorem fz2_59_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨92, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 92 (by decide)))

theorem fz2_59_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨93, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 93 (by decide)))

theorem fz2_59_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨94, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 94 (by decide)))

theorem fz2_59_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨95, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 95 (by decide)))

theorem fz2_59_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨96, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 96 (by decide)))

theorem fz2_59_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨97, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 97 (by decide)))

theorem fz2_59_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨98, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 98 (by decide)))

theorem fz2_59_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨99, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 99 (by decide)))

theorem fz2_59_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨100, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 100 (by decide)))

theorem fz2_59_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨101, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 101 (by decide)))

theorem fz2_59_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨102, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 102 (by decide)))

theorem fz2_59_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨103, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 103 (by decide)))

theorem fz2_59_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨104, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 104 (by decide)))

theorem fz2_59_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨105, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 105 (by decide)))

theorem fz2_59_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨106, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 106 (by decide)))

theorem fz2_59_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨107, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 107 (by decide)))

theorem fz2_59_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨108, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 108 (by decide)))

theorem fz2_59_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨109, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 109 (by decide)))

theorem fz2_59_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨110, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 110 (by decide)))

theorem fz2_59_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨111, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 111 (by decide)))

theorem fz2_59_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨112, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 112 (by decide)))

theorem fz2_59_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨113, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 113 (by decide)))

theorem fz2_59_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨114, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 114 (by decide)))

theorem fz2_59_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK59)) = 0 :=
  Q2.repsFixedCard2 rK59 ⟨115, by decide⟩ Q2.R59_2 Q2.hpxR59_2 Q2.hcardq59_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_59) 115 (by decide)))

theorem fixz1_60 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK60) (retConj 1 (R60 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_60_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨1, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 1 (by decide)))

theorem fz1_60_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨2, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 2 (by decide)))

theorem fz1_60_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨3, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 3 (by decide)))

theorem fz1_60_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨4, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 4 (by decide)))

theorem fz1_60_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨5, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 5 (by decide)))

theorem fz1_60_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨6, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 6 (by decide)))

theorem fz1_60_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨7, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 7 (by decide)))

theorem fz1_60_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨8, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 8 (by decide)))

theorem fz1_60_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨10, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 10 (by decide)))

theorem fz1_60_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨11, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 11 (by decide)))

theorem fz1_60_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨13, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 13 (by decide)))

theorem fz1_60_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨14, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 14 (by decide)))

theorem fz1_60_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨15, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 15 (by decide)))

theorem fz1_60_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨16, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 16 (by decide)))

theorem fz1_60_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨17, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 17 (by decide)))

theorem fz1_60_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨18, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 18 (by decide)))

theorem fz1_60_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨19, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 19 (by decide)))

theorem fz1_60_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨20, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 20 (by decide)))

theorem fz1_60_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨21, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 21 (by decide)))

theorem fz1_60_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨22, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 22 (by decide)))

theorem fz1_60_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨23, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 23 (by decide)))

theorem fz1_60_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨24, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 24 (by decide)))

theorem fz1_60_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨25, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 25 (by decide)))

theorem fz1_60_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨26, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 26 (by decide)))

theorem fz1_60_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨28, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 28 (by decide)))

theorem fz1_60_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨30, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 30 (by decide)))

theorem fz1_60_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨31, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 31 (by decide)))

theorem fz1_60_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨32, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 32 (by decide)))

theorem fz1_60_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨33, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 33 (by decide)))

theorem fz1_60_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨35, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 35 (by decide)))

theorem fz1_60_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨36, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 36 (by decide)))

theorem fz1_60_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨37, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 37 (by decide)))

theorem fz1_60_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨38, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 38 (by decide)))

theorem fz1_60_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨40, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 40 (by decide)))

theorem fz1_60_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨41, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 41 (by decide)))

theorem fz1_60_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨42, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 42 (by decide)))

theorem fz1_60_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨43, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 43 (by decide)))

theorem fz1_60_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨45, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 45 (by decide)))

theorem fz1_60_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨46, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 46 (by decide)))

theorem fz1_60_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨47, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 47 (by decide)))

theorem fz1_60_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨48, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 48 (by decide)))

theorem fz1_60_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨50, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 50 (by decide)))

theorem fz1_60_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨51, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 51 (by decide)))

theorem fz1_60_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨52, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 52 (by decide)))

theorem fz1_60_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨53, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 53 (by decide)))

theorem fz1_60_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨54, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 54 (by decide)))

theorem fz1_60_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨55, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 55 (by decide)))

theorem fz1_60_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨56, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 56 (by decide)))

theorem fz1_60_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨57, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 57 (by decide)))

theorem fz1_60_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨58, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 58 (by decide)))

theorem fz1_60_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨59, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 59 (by decide)))

theorem fz1_60_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨61, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 61 (by decide)))

theorem fz1_60_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨62, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 62 (by decide)))

theorem fz1_60_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨63, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 63 (by decide)))

theorem fz1_60_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨64, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 64 (by decide)))

theorem fz1_60_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨65, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 65 (by decide)))

theorem fz1_60_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨66, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 66 (by decide)))

theorem fz1_60_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨67, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 67 (by decide)))

theorem fz1_60_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨68, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 68 (by decide)))

theorem fz1_60_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨69, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 69 (by decide)))

theorem fz1_60_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨70, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 70 (by decide)))

theorem fz1_60_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨71, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 71 (by decide)))

theorem fz1_60_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨72, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 72 (by decide)))

theorem fz1_60_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨73, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 73 (by decide)))

theorem fz1_60_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨74, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 74 (by decide)))

theorem fz1_60_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨75, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 75 (by decide)))

theorem fz1_60_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨76, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 76 (by decide)))

theorem fz1_60_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨77, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 77 (by decide)))

theorem fz1_60_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨78, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 78 (by decide)))

theorem fz1_60_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨79, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 79 (by decide)))

theorem fz1_60_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨80, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 80 (by decide)))

theorem fz1_60_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨81, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 81 (by decide)))

theorem fz1_60_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨82, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 82 (by decide)))

theorem fz1_60_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨83, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 83 (by decide)))

theorem fz1_60_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨84, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 84 (by decide)))

theorem fz1_60_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨85, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 85 (by decide)))

theorem fz1_60_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨86, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 86 (by decide)))

theorem fz1_60_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨87, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 87 (by decide)))

theorem fz1_60_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨88, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 88 (by decide)))

theorem fz1_60_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨89, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 89 (by decide)))

theorem fz1_60_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨90, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 90 (by decide)))

theorem fz1_60_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨91, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 91 (by decide)))

theorem fz1_60_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨92, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 92 (by decide)))

theorem fz1_60_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨93, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 93 (by decide)))

theorem fz1_60_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨94, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 94 (by decide)))

theorem fz1_60_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨95, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 95 (by decide)))

theorem fz1_60_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨96, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 96 (by decide)))

theorem fz1_60_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨97, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 97 (by decide)))

theorem fz1_60_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨98, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 98 (by decide)))

theorem fz1_60_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨99, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 99 (by decide)))

theorem fz1_60_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨100, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 100 (by decide)))

theorem fz1_60_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨101, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 101 (by decide)))

theorem fz1_60_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨102, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 102 (by decide)))

theorem fz1_60_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨103, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 103 (by decide)))

theorem fz1_60_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨104, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 104 (by decide)))

theorem fz1_60_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨105, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 105 (by decide)))

theorem fz1_60_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨106, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 106 (by decide)))

theorem fz1_60_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨107, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 107 (by decide)))

theorem fz1_60_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨108, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 108 (by decide)))

theorem fz1_60_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨109, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 109 (by decide)))

theorem fz1_60_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨110, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 110 (by decide)))

theorem fz1_60_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨111, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 111 (by decide)))

theorem fz1_60_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨112, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 112 (by decide)))

theorem fz1_60_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨113, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 113 (by decide)))

theorem fz1_60_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨114, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 114 (by decide)))

theorem fz1_60_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK60)) = 0 :=
  repsFixedCard rK60 ⟨115, by decide⟩ R60 hpxR60 hcardq60
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_60) 115 (by decide)))

theorem fixz2_60 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 30, 31, 32, 33, 35, 36, 37, 38, 40, 41, 42, 43, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK60) (retConj 2 (Q2.R60_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_60_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨1, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 1 (by decide)))

theorem fz2_60_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨2, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 2 (by decide)))

theorem fz2_60_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨3, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 3 (by decide)))

theorem fz2_60_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨4, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 4 (by decide)))

theorem fz2_60_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨5, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 5 (by decide)))

theorem fz2_60_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨6, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 6 (by decide)))

theorem fz2_60_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨7, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 7 (by decide)))

theorem fz2_60_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨8, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 8 (by decide)))

theorem fz2_60_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨10, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 10 (by decide)))

theorem fz2_60_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨11, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 11 (by decide)))

theorem fz2_60_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨13, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 13 (by decide)))

theorem fz2_60_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨14, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 14 (by decide)))

theorem fz2_60_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨15, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 15 (by decide)))

theorem fz2_60_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨16, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 16 (by decide)))

theorem fz2_60_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨17, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 17 (by decide)))

theorem fz2_60_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨18, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 18 (by decide)))

theorem fz2_60_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨19, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 19 (by decide)))

theorem fz2_60_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨20, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 20 (by decide)))

theorem fz2_60_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨21, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 21 (by decide)))

theorem fz2_60_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨22, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 22 (by decide)))

theorem fz2_60_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨23, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 23 (by decide)))

theorem fz2_60_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨24, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 24 (by decide)))

theorem fz2_60_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨25, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 25 (by decide)))

theorem fz2_60_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨26, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 26 (by decide)))

theorem fz2_60_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨28, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 28 (by decide)))

theorem fz2_60_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨30, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 30 (by decide)))

theorem fz2_60_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨31, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 31 (by decide)))

theorem fz2_60_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨32, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 32 (by decide)))

theorem fz2_60_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨33, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 33 (by decide)))

theorem fz2_60_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨35, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 35 (by decide)))

theorem fz2_60_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨36, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 36 (by decide)))

theorem fz2_60_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨37, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 37 (by decide)))

theorem fz2_60_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨38, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 38 (by decide)))

theorem fz2_60_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨40, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 40 (by decide)))

theorem fz2_60_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨41, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 41 (by decide)))

theorem fz2_60_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨42, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 42 (by decide)))

theorem fz2_60_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨43, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 43 (by decide)))

theorem fz2_60_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨45, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 45 (by decide)))

theorem fz2_60_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨46, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 46 (by decide)))

theorem fz2_60_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨47, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 47 (by decide)))

theorem fz2_60_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨48, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 48 (by decide)))

theorem fz2_60_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨50, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 50 (by decide)))

theorem fz2_60_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨51, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 51 (by decide)))

theorem fz2_60_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨52, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 52 (by decide)))

theorem fz2_60_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨53, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 53 (by decide)))

theorem fz2_60_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨54, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 54 (by decide)))

theorem fz2_60_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨55, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 55 (by decide)))

theorem fz2_60_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨56, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 56 (by decide)))

theorem fz2_60_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨57, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 57 (by decide)))

theorem fz2_60_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨58, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 58 (by decide)))

theorem fz2_60_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨59, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 59 (by decide)))

theorem fz2_60_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨61, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 61 (by decide)))

theorem fz2_60_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨62, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 62 (by decide)))

theorem fz2_60_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨63, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 63 (by decide)))

theorem fz2_60_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨64, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 64 (by decide)))

theorem fz2_60_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨65, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 65 (by decide)))

theorem fz2_60_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨66, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 66 (by decide)))

theorem fz2_60_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨67, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 67 (by decide)))

theorem fz2_60_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨68, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 68 (by decide)))

theorem fz2_60_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨69, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 69 (by decide)))

theorem fz2_60_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨70, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 70 (by decide)))

theorem fz2_60_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨71, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 71 (by decide)))

theorem fz2_60_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨72, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 72 (by decide)))

theorem fz2_60_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨73, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 73 (by decide)))

theorem fz2_60_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨74, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 74 (by decide)))

theorem fz2_60_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨75, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 75 (by decide)))

theorem fz2_60_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨76, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 76 (by decide)))

theorem fz2_60_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨77, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 77 (by decide)))

theorem fz2_60_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨78, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 78 (by decide)))

theorem fz2_60_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨79, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 79 (by decide)))

theorem fz2_60_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨80, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 80 (by decide)))

theorem fz2_60_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨81, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 81 (by decide)))

theorem fz2_60_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨82, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 82 (by decide)))

theorem fz2_60_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨83, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 83 (by decide)))

theorem fz2_60_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨84, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 84 (by decide)))

theorem fz2_60_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨85, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 85 (by decide)))

theorem fz2_60_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨86, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 86 (by decide)))

theorem fz2_60_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨87, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 87 (by decide)))

theorem fz2_60_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨88, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 88 (by decide)))

theorem fz2_60_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨89, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 89 (by decide)))

theorem fz2_60_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨90, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 90 (by decide)))

theorem fz2_60_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨91, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 91 (by decide)))

theorem fz2_60_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨92, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 92 (by decide)))

theorem fz2_60_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨93, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 93 (by decide)))

theorem fz2_60_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨94, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 94 (by decide)))

theorem fz2_60_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨95, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 95 (by decide)))

theorem fz2_60_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨96, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 96 (by decide)))

theorem fz2_60_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨97, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 97 (by decide)))

theorem fz2_60_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨98, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 98 (by decide)))

theorem fz2_60_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨99, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 99 (by decide)))

theorem fz2_60_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨100, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 100 (by decide)))

theorem fz2_60_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨101, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 101 (by decide)))

theorem fz2_60_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨102, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 102 (by decide)))

theorem fz2_60_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨103, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 103 (by decide)))

theorem fz2_60_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨104, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 104 (by decide)))

theorem fz2_60_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨105, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 105 (by decide)))

theorem fz2_60_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨106, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 106 (by decide)))

theorem fz2_60_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨107, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 107 (by decide)))

theorem fz2_60_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨108, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 108 (by decide)))

theorem fz2_60_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨109, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 109 (by decide)))

theorem fz2_60_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨110, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 110 (by decide)))

theorem fz2_60_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨111, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 111 (by decide)))

theorem fz2_60_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨112, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 112 (by decide)))

theorem fz2_60_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨113, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 113 (by decide)))

theorem fz2_60_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨114, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 114 (by decide)))

theorem fz2_60_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK60)) = 0 :=
  Q2.repsFixedCard2 rK60 ⟨115, by decide⟩ Q2.R60_2 Q2.hpxR60_2 Q2.hcardq60_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_60) 115 (by decide)))

end LeanDring.P5Presentation
