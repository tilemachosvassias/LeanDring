/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C023

/-!
# Species-table cells, off-support emptiness certificates, chunk 80

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

theorem fixz1_107 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK107) (retConj 1 (R107 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_107_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨1, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 1 (by decide)))

theorem fz1_107_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨2, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 2 (by decide)))

theorem fz1_107_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨3, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 3 (by decide)))

theorem fz1_107_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨4, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 4 (by decide)))

theorem fz1_107_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨5, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 5 (by decide)))

theorem fz1_107_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨6, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 6 (by decide)))

theorem fz1_107_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨7, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 7 (by decide)))

theorem fz1_107_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨8, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 8 (by decide)))

theorem fz1_107_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨9, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 9 (by decide)))

theorem fz1_107_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨11, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 11 (by decide)))

theorem fz1_107_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨13, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 13 (by decide)))

theorem fz1_107_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨14, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 14 (by decide)))

theorem fz1_107_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨15, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 15 (by decide)))

theorem fz1_107_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨16, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 16 (by decide)))

theorem fz1_107_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨17, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 17 (by decide)))

theorem fz1_107_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨18, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 18 (by decide)))

theorem fz1_107_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨19, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 19 (by decide)))

theorem fz1_107_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨20, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 20 (by decide)))

theorem fz1_107_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨21, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 21 (by decide)))

theorem fz1_107_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨22, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 22 (by decide)))

theorem fz1_107_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨23, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 23 (by decide)))

theorem fz1_107_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨24, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 24 (by decide)))

theorem fz1_107_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨25, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 25 (by decide)))

theorem fz1_107_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨26, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 26 (by decide)))

theorem fz1_107_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨27, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 27 (by decide)))

theorem fz1_107_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨28, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 28 (by decide)))

theorem fz1_107_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨29, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 29 (by decide)))

theorem fz1_107_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨30, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 30 (by decide)))

theorem fz1_107_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨31, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 31 (by decide)))

theorem fz1_107_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨32, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 32 (by decide)))

theorem fz1_107_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨33, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 33 (by decide)))

theorem fz1_107_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨34, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 34 (by decide)))

theorem fz1_107_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨35, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 35 (by decide)))

theorem fz1_107_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨36, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 36 (by decide)))

theorem fz1_107_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨37, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 37 (by decide)))

theorem fz1_107_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨38, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 38 (by decide)))

theorem fz1_107_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨39, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 39 (by decide)))

theorem fz1_107_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨40, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 40 (by decide)))

theorem fz1_107_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨41, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 41 (by decide)))

theorem fz1_107_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨42, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 42 (by decide)))

theorem fz1_107_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨43, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 43 (by decide)))

theorem fz1_107_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨44, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 44 (by decide)))

theorem fz1_107_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨46, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 46 (by decide)))

theorem fz1_107_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨47, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 47 (by decide)))

theorem fz1_107_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨48, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 48 (by decide)))

theorem fz1_107_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨49, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 49 (by decide)))

theorem fz1_107_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨50, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 50 (by decide)))

theorem fz1_107_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨51, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 51 (by decide)))

theorem fz1_107_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨52, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 52 (by decide)))

theorem fz1_107_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨54, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 54 (by decide)))

theorem fz1_107_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨55, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 55 (by decide)))

theorem fz1_107_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨56, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 56 (by decide)))

theorem fz1_107_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨57, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 57 (by decide)))

theorem fz1_107_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨58, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 58 (by decide)))

theorem fz1_107_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨59, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 59 (by decide)))

theorem fz1_107_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨60, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 60 (by decide)))

theorem fz1_107_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨61, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 61 (by decide)))

theorem fz1_107_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨62, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 62 (by decide)))

theorem fz1_107_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨63, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 63 (by decide)))

theorem fz1_107_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨64, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 64 (by decide)))

theorem fz1_107_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨65, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 65 (by decide)))

theorem fz1_107_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨66, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 66 (by decide)))

theorem fz1_107_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨67, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 67 (by decide)))

theorem fz1_107_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨68, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 68 (by decide)))

theorem fz1_107_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨69, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 69 (by decide)))

theorem fz1_107_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨70, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 70 (by decide)))

theorem fz1_107_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨71, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 71 (by decide)))

theorem fz1_107_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨72, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 72 (by decide)))

theorem fz1_107_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨73, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 73 (by decide)))

theorem fz1_107_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨74, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 74 (by decide)))

theorem fz1_107_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨75, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 75 (by decide)))

theorem fz1_107_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨76, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 76 (by decide)))

theorem fz1_107_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨77, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 77 (by decide)))

theorem fz1_107_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨78, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 78 (by decide)))

theorem fz1_107_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨79, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 79 (by decide)))

theorem fz1_107_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨80, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 80 (by decide)))

theorem fz1_107_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨81, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 81 (by decide)))

theorem fz1_107_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨82, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 82 (by decide)))

theorem fz1_107_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨83, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 83 (by decide)))

theorem fz1_107_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨84, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 84 (by decide)))

theorem fz1_107_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨85, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 85 (by decide)))

theorem fz1_107_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨86, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 86 (by decide)))

theorem fz1_107_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨87, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 87 (by decide)))

theorem fz1_107_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨88, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 88 (by decide)))

theorem fz1_107_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨89, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 89 (by decide)))

theorem fz1_107_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨90, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 90 (by decide)))

theorem fz1_107_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨91, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 91 (by decide)))

theorem fz1_107_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨92, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 92 (by decide)))

theorem fz1_107_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨93, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 93 (by decide)))

theorem fz1_107_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨94, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 94 (by decide)))

theorem fz1_107_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨95, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 95 (by decide)))

theorem fz1_107_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨96, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 96 (by decide)))

theorem fz1_107_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨97, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 97 (by decide)))

theorem fz1_107_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨98, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 98 (by decide)))

theorem fz1_107_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨99, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 99 (by decide)))

theorem fz1_107_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨100, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 100 (by decide)))

theorem fz1_107_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨101, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 101 (by decide)))

theorem fz1_107_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨102, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 102 (by decide)))

theorem fz1_107_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨103, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 103 (by decide)))

theorem fz1_107_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨104, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 104 (by decide)))

theorem fz1_107_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨105, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 105 (by decide)))

theorem fz1_107_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨106, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 106 (by decide)))

theorem fz1_107_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨108, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 108 (by decide)))

theorem fz1_107_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨109, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 109 (by decide)))

theorem fz1_107_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨110, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 110 (by decide)))

theorem fz1_107_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨111, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 111 (by decide)))

theorem fz1_107_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨112, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 112 (by decide)))

theorem fz1_107_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨113, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 113 (by decide)))

theorem fz1_107_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨114, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 114 (by decide)))

theorem fz1_107_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK107)) = 0 :=
  repsFixedCard rK107 ⟨115, by decide⟩ R107 hpxR107 hcardq107
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_107) 115 (by decide)))

theorem fixz2_107 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK107) (retConj 2 (Q2.R107_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_107_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨1, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 1 (by decide)))

theorem fz2_107_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨2, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 2 (by decide)))

theorem fz2_107_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨3, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 3 (by decide)))

theorem fz2_107_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨4, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 4 (by decide)))

theorem fz2_107_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨5, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 5 (by decide)))

theorem fz2_107_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨6, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 6 (by decide)))

theorem fz2_107_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨7, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 7 (by decide)))

theorem fz2_107_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨8, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 8 (by decide)))

theorem fz2_107_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨9, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 9 (by decide)))

theorem fz2_107_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨11, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 11 (by decide)))

theorem fz2_107_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨13, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 13 (by decide)))

theorem fz2_107_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨14, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 14 (by decide)))

theorem fz2_107_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨15, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 15 (by decide)))

theorem fz2_107_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨16, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 16 (by decide)))

theorem fz2_107_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨17, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 17 (by decide)))

theorem fz2_107_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨18, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 18 (by decide)))

theorem fz2_107_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨19, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 19 (by decide)))

theorem fz2_107_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨20, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 20 (by decide)))

theorem fz2_107_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨21, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 21 (by decide)))

theorem fz2_107_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨22, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 22 (by decide)))

theorem fz2_107_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨23, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 23 (by decide)))

theorem fz2_107_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨24, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 24 (by decide)))

theorem fz2_107_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨25, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 25 (by decide)))

theorem fz2_107_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨26, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 26 (by decide)))

theorem fz2_107_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨27, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 27 (by decide)))

theorem fz2_107_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨28, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 28 (by decide)))

theorem fz2_107_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨29, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 29 (by decide)))

theorem fz2_107_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨30, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 30 (by decide)))

theorem fz2_107_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨31, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 31 (by decide)))

theorem fz2_107_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨32, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 32 (by decide)))

theorem fz2_107_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨33, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 33 (by decide)))

theorem fz2_107_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨34, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 34 (by decide)))

theorem fz2_107_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨35, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 35 (by decide)))

theorem fz2_107_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨36, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 36 (by decide)))

theorem fz2_107_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨37, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 37 (by decide)))

theorem fz2_107_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨38, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 38 (by decide)))

theorem fz2_107_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨39, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 39 (by decide)))

theorem fz2_107_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨40, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 40 (by decide)))

theorem fz2_107_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨41, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 41 (by decide)))

theorem fz2_107_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨42, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 42 (by decide)))

theorem fz2_107_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨43, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 43 (by decide)))

theorem fz2_107_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨44, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 44 (by decide)))

theorem fz2_107_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨46, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 46 (by decide)))

theorem fz2_107_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨47, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 47 (by decide)))

theorem fz2_107_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨48, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 48 (by decide)))

theorem fz2_107_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨49, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 49 (by decide)))

theorem fz2_107_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨50, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 50 (by decide)))

theorem fz2_107_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨51, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 51 (by decide)))

theorem fz2_107_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨52, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 52 (by decide)))

theorem fz2_107_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨54, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 54 (by decide)))

theorem fz2_107_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨55, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 55 (by decide)))

theorem fz2_107_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨56, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 56 (by decide)))

theorem fz2_107_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨57, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 57 (by decide)))

theorem fz2_107_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨58, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 58 (by decide)))

theorem fz2_107_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨59, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 59 (by decide)))

theorem fz2_107_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨60, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 60 (by decide)))

theorem fz2_107_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨61, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 61 (by decide)))

theorem fz2_107_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨62, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 62 (by decide)))

theorem fz2_107_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨63, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 63 (by decide)))

theorem fz2_107_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨64, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 64 (by decide)))

theorem fz2_107_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨65, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 65 (by decide)))

theorem fz2_107_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨66, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 66 (by decide)))

theorem fz2_107_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨67, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 67 (by decide)))

theorem fz2_107_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨68, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 68 (by decide)))

theorem fz2_107_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨69, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 69 (by decide)))

theorem fz2_107_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨70, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 70 (by decide)))

theorem fz2_107_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨71, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 71 (by decide)))

theorem fz2_107_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨72, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 72 (by decide)))

theorem fz2_107_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨73, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 73 (by decide)))

theorem fz2_107_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨74, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 74 (by decide)))

theorem fz2_107_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨75, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 75 (by decide)))

theorem fz2_107_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨76, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 76 (by decide)))

theorem fz2_107_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨77, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 77 (by decide)))

theorem fz2_107_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨78, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 78 (by decide)))

theorem fz2_107_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨79, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 79 (by decide)))

theorem fz2_107_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨80, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 80 (by decide)))

theorem fz2_107_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨81, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 81 (by decide)))

theorem fz2_107_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨82, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 82 (by decide)))

theorem fz2_107_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨83, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 83 (by decide)))

theorem fz2_107_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨84, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 84 (by decide)))

theorem fz2_107_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨85, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 85 (by decide)))

theorem fz2_107_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨86, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 86 (by decide)))

theorem fz2_107_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨87, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 87 (by decide)))

theorem fz2_107_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨88, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 88 (by decide)))

theorem fz2_107_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨89, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 89 (by decide)))

theorem fz2_107_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨90, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 90 (by decide)))

theorem fz2_107_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨91, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 91 (by decide)))

theorem fz2_107_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨92, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 92 (by decide)))

theorem fz2_107_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨93, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 93 (by decide)))

theorem fz2_107_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨94, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 94 (by decide)))

theorem fz2_107_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨95, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 95 (by decide)))

theorem fz2_107_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨96, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 96 (by decide)))

theorem fz2_107_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨97, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 97 (by decide)))

theorem fz2_107_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨98, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 98 (by decide)))

theorem fz2_107_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨99, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 99 (by decide)))

theorem fz2_107_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨100, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 100 (by decide)))

theorem fz2_107_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨101, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 101 (by decide)))

theorem fz2_107_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨102, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 102 (by decide)))

theorem fz2_107_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨103, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 103 (by decide)))

theorem fz2_107_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨104, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 104 (by decide)))

theorem fz2_107_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨105, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 105 (by decide)))

theorem fz2_107_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨106, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 106 (by decide)))

theorem fz2_107_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨108, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 108 (by decide)))

theorem fz2_107_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨109, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 109 (by decide)))

theorem fz2_107_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨110, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 110 (by decide)))

theorem fz2_107_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨111, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 111 (by decide)))

theorem fz2_107_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨112, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 112 (by decide)))

theorem fz2_107_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨113, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 113 (by decide)))

theorem fz2_107_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨114, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 114 (by decide)))

theorem fz2_107_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK107)) = 0 :=
  Q2.repsFixedCard2 rK107 ⟨115, by decide⟩ Q2.R107_2 Q2.hpxR107_2 Q2.hcardq107_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_107) 115 (by decide)))

theorem fixz1_108 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK108) (retConj 1 (R108 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_108_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨1, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 1 (by decide)))

theorem fz1_108_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨2, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 2 (by decide)))

theorem fz1_108_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨3, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 3 (by decide)))

theorem fz1_108_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨4, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 4 (by decide)))

theorem fz1_108_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨5, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 5 (by decide)))

theorem fz1_108_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨6, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 6 (by decide)))

theorem fz1_108_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨7, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 7 (by decide)))

theorem fz1_108_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨8, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 8 (by decide)))

theorem fz1_108_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨9, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 9 (by decide)))

theorem fz1_108_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨11, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 11 (by decide)))

theorem fz1_108_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨13, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 13 (by decide)))

theorem fz1_108_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨14, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 14 (by decide)))

theorem fz1_108_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨15, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 15 (by decide)))

theorem fz1_108_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨16, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 16 (by decide)))

theorem fz1_108_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨17, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 17 (by decide)))

theorem fz1_108_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨18, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 18 (by decide)))

theorem fz1_108_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨19, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 19 (by decide)))

theorem fz1_108_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨20, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 20 (by decide)))

theorem fz1_108_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨21, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 21 (by decide)))

theorem fz1_108_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨22, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 22 (by decide)))

theorem fz1_108_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨23, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 23 (by decide)))

theorem fz1_108_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨24, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 24 (by decide)))

theorem fz1_108_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨25, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 25 (by decide)))

theorem fz1_108_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨26, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 26 (by decide)))

theorem fz1_108_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨27, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 27 (by decide)))

theorem fz1_108_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨28, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 28 (by decide)))

theorem fz1_108_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨29, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 29 (by decide)))

theorem fz1_108_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨30, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 30 (by decide)))

theorem fz1_108_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨31, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 31 (by decide)))

theorem fz1_108_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨32, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 32 (by decide)))

theorem fz1_108_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨33, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 33 (by decide)))

theorem fz1_108_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨34, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 34 (by decide)))

theorem fz1_108_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨35, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 35 (by decide)))

theorem fz1_108_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨36, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 36 (by decide)))

theorem fz1_108_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨37, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 37 (by decide)))

theorem fz1_108_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨38, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 38 (by decide)))

theorem fz1_108_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨39, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 39 (by decide)))

theorem fz1_108_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨40, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 40 (by decide)))

theorem fz1_108_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨41, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 41 (by decide)))

theorem fz1_108_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨42, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 42 (by decide)))

theorem fz1_108_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨43, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 43 (by decide)))

theorem fz1_108_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨44, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 44 (by decide)))

theorem fz1_108_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨45, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 45 (by decide)))

theorem fz1_108_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨47, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 47 (by decide)))

theorem fz1_108_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨48, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 48 (by decide)))

theorem fz1_108_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨49, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 49 (by decide)))

theorem fz1_108_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨50, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 50 (by decide)))

theorem fz1_108_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨51, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 51 (by decide)))

theorem fz1_108_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨52, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 52 (by decide)))

theorem fz1_108_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨54, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 54 (by decide)))

theorem fz1_108_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨55, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 55 (by decide)))

theorem fz1_108_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨56, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 56 (by decide)))

theorem fz1_108_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨57, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 57 (by decide)))

theorem fz1_108_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨58, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 58 (by decide)))

theorem fz1_108_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨59, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 59 (by decide)))

theorem fz1_108_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨60, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 60 (by decide)))

theorem fz1_108_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨61, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 61 (by decide)))

theorem fz1_108_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨62, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 62 (by decide)))

theorem fz1_108_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨63, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 63 (by decide)))

theorem fz1_108_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨64, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 64 (by decide)))

theorem fz1_108_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨65, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 65 (by decide)))

theorem fz1_108_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨66, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 66 (by decide)))

theorem fz1_108_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨67, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 67 (by decide)))

theorem fz1_108_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨68, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 68 (by decide)))

theorem fz1_108_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨69, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 69 (by decide)))

theorem fz1_108_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨70, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 70 (by decide)))

theorem fz1_108_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨71, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 71 (by decide)))

theorem fz1_108_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨72, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 72 (by decide)))

theorem fz1_108_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨73, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 73 (by decide)))

theorem fz1_108_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨74, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 74 (by decide)))

theorem fz1_108_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨75, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 75 (by decide)))

theorem fz1_108_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨76, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 76 (by decide)))

theorem fz1_108_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨77, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 77 (by decide)))

theorem fz1_108_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨78, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 78 (by decide)))

theorem fz1_108_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨79, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 79 (by decide)))

theorem fz1_108_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨80, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 80 (by decide)))

theorem fz1_108_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨81, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 81 (by decide)))

theorem fz1_108_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨82, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 82 (by decide)))

theorem fz1_108_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨83, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 83 (by decide)))

theorem fz1_108_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨84, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 84 (by decide)))

theorem fz1_108_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨85, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 85 (by decide)))

theorem fz1_108_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨86, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 86 (by decide)))

theorem fz1_108_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨87, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 87 (by decide)))

theorem fz1_108_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨88, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 88 (by decide)))

theorem fz1_108_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨89, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 89 (by decide)))

theorem fz1_108_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨90, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 90 (by decide)))

theorem fz1_108_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨91, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 91 (by decide)))

theorem fz1_108_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨92, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 92 (by decide)))

theorem fz1_108_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨93, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 93 (by decide)))

theorem fz1_108_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨94, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 94 (by decide)))

theorem fz1_108_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨95, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 95 (by decide)))

theorem fz1_108_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨96, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 96 (by decide)))

theorem fz1_108_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨97, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 97 (by decide)))

theorem fz1_108_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨98, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 98 (by decide)))

theorem fz1_108_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨99, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 99 (by decide)))

theorem fz1_108_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨100, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 100 (by decide)))

theorem fz1_108_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨101, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 101 (by decide)))

theorem fz1_108_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨102, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 102 (by decide)))

theorem fz1_108_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨103, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 103 (by decide)))

theorem fz1_108_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨104, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 104 (by decide)))

theorem fz1_108_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨105, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 105 (by decide)))

theorem fz1_108_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨106, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 106 (by decide)))

theorem fz1_108_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨107, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 107 (by decide)))

theorem fz1_108_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨109, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 109 (by decide)))

theorem fz1_108_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨110, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 110 (by decide)))

theorem fz1_108_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨111, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 111 (by decide)))

theorem fz1_108_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨112, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 112 (by decide)))

theorem fz1_108_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨113, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 113 (by decide)))

theorem fz1_108_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨114, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 114 (by decide)))

theorem fz1_108_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK108)) = 0 :=
  repsFixedCard rK108 ⟨115, by decide⟩ R108 hpxR108 hcardq108
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_108) 115 (by decide)))

theorem fixz2_108 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK108) (retConj 2 (Q2.R108_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_108_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨1, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 1 (by decide)))

theorem fz2_108_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨2, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 2 (by decide)))

theorem fz2_108_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨3, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 3 (by decide)))

theorem fz2_108_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨4, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 4 (by decide)))

theorem fz2_108_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨5, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 5 (by decide)))

theorem fz2_108_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨6, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 6 (by decide)))

theorem fz2_108_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨7, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 7 (by decide)))

theorem fz2_108_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨8, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 8 (by decide)))

theorem fz2_108_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨9, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 9 (by decide)))

theorem fz2_108_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨11, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 11 (by decide)))

theorem fz2_108_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨13, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 13 (by decide)))

theorem fz2_108_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨14, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 14 (by decide)))

theorem fz2_108_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨15, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 15 (by decide)))

theorem fz2_108_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨16, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 16 (by decide)))

theorem fz2_108_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨17, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 17 (by decide)))

theorem fz2_108_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨18, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 18 (by decide)))

theorem fz2_108_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨19, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 19 (by decide)))

theorem fz2_108_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨20, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 20 (by decide)))

theorem fz2_108_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨21, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 21 (by decide)))

theorem fz2_108_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨22, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 22 (by decide)))

theorem fz2_108_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨23, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 23 (by decide)))

theorem fz2_108_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨24, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 24 (by decide)))

theorem fz2_108_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨25, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 25 (by decide)))

theorem fz2_108_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨26, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 26 (by decide)))

theorem fz2_108_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨27, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 27 (by decide)))

theorem fz2_108_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨28, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 28 (by decide)))

theorem fz2_108_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨29, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 29 (by decide)))

theorem fz2_108_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨30, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 30 (by decide)))

theorem fz2_108_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨31, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 31 (by decide)))

theorem fz2_108_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨32, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 32 (by decide)))

theorem fz2_108_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨33, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 33 (by decide)))

theorem fz2_108_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨34, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 34 (by decide)))

theorem fz2_108_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨35, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 35 (by decide)))

theorem fz2_108_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨36, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 36 (by decide)))

theorem fz2_108_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨37, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 37 (by decide)))

theorem fz2_108_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨38, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 38 (by decide)))

theorem fz2_108_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨39, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 39 (by decide)))

theorem fz2_108_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨40, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 40 (by decide)))

theorem fz2_108_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨41, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 41 (by decide)))

theorem fz2_108_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨42, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 42 (by decide)))

theorem fz2_108_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨43, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 43 (by decide)))

theorem fz2_108_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨44, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 44 (by decide)))

theorem fz2_108_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨45, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 45 (by decide)))

theorem fz2_108_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨47, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 47 (by decide)))

theorem fz2_108_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨48, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 48 (by decide)))

theorem fz2_108_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨49, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 49 (by decide)))

theorem fz2_108_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨50, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 50 (by decide)))

theorem fz2_108_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨51, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 51 (by decide)))

theorem fz2_108_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨52, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 52 (by decide)))

theorem fz2_108_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨54, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 54 (by decide)))

theorem fz2_108_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨55, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 55 (by decide)))

theorem fz2_108_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨56, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 56 (by decide)))

theorem fz2_108_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨57, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 57 (by decide)))

theorem fz2_108_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨58, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 58 (by decide)))

theorem fz2_108_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨59, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 59 (by decide)))

theorem fz2_108_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨60, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 60 (by decide)))

theorem fz2_108_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨61, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 61 (by decide)))

theorem fz2_108_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨62, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 62 (by decide)))

theorem fz2_108_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨63, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 63 (by decide)))

theorem fz2_108_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨64, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 64 (by decide)))

theorem fz2_108_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨65, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 65 (by decide)))

theorem fz2_108_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨66, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 66 (by decide)))

theorem fz2_108_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨67, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 67 (by decide)))

theorem fz2_108_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨68, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 68 (by decide)))

theorem fz2_108_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨69, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 69 (by decide)))

theorem fz2_108_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨70, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 70 (by decide)))

theorem fz2_108_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨71, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 71 (by decide)))

theorem fz2_108_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨72, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 72 (by decide)))

theorem fz2_108_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨73, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 73 (by decide)))

theorem fz2_108_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨74, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 74 (by decide)))

theorem fz2_108_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨75, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 75 (by decide)))

theorem fz2_108_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨76, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 76 (by decide)))

theorem fz2_108_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨77, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 77 (by decide)))

theorem fz2_108_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨78, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 78 (by decide)))

theorem fz2_108_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨79, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 79 (by decide)))

theorem fz2_108_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨80, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 80 (by decide)))

theorem fz2_108_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨81, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 81 (by decide)))

theorem fz2_108_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨82, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 82 (by decide)))

theorem fz2_108_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨83, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 83 (by decide)))

theorem fz2_108_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨84, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 84 (by decide)))

theorem fz2_108_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨85, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 85 (by decide)))

theorem fz2_108_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨86, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 86 (by decide)))

theorem fz2_108_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨87, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 87 (by decide)))

theorem fz2_108_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨88, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 88 (by decide)))

theorem fz2_108_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨89, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 89 (by decide)))

theorem fz2_108_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨90, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 90 (by decide)))

theorem fz2_108_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨91, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 91 (by decide)))

theorem fz2_108_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨92, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 92 (by decide)))

theorem fz2_108_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨93, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 93 (by decide)))

theorem fz2_108_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨94, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 94 (by decide)))

theorem fz2_108_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨95, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 95 (by decide)))

theorem fz2_108_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨96, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 96 (by decide)))

theorem fz2_108_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨97, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 97 (by decide)))

theorem fz2_108_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨98, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 98 (by decide)))

theorem fz2_108_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨99, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 99 (by decide)))

theorem fz2_108_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨100, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 100 (by decide)))

theorem fz2_108_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨101, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 101 (by decide)))

theorem fz2_108_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨102, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 102 (by decide)))

theorem fz2_108_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨103, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 103 (by decide)))

theorem fz2_108_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨104, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 104 (by decide)))

theorem fz2_108_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨105, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 105 (by decide)))

theorem fz2_108_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨106, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 106 (by decide)))

theorem fz2_108_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨107, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 107 (by decide)))

theorem fz2_108_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨109, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 109 (by decide)))

theorem fz2_108_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨110, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 110 (by decide)))

theorem fz2_108_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨111, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 111 (by decide)))

theorem fz2_108_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨112, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 112 (by decide)))

theorem fz2_108_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨113, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 113 (by decide)))

theorem fz2_108_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨114, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 114 (by decide)))

theorem fz2_108_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK108)) = 0 :=
  Q2.repsFixedCard2 rK108 ⟨115, by decide⟩ Q2.R108_2 Q2.hpxR108_2 Q2.hcardq108_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_108) 115 (by decide)))

end LeanDring.P5Presentation
