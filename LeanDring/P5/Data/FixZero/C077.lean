/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C022

/-!
# Species-table cells, off-support emptiness certificates, chunk 76

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

theorem fixz1_99 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK99) (retConj 1 (R99 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_99_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨1, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 1 (by decide)))

theorem fz1_99_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨2, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 2 (by decide)))

theorem fz1_99_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨3, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 3 (by decide)))

theorem fz1_99_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨4, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 4 (by decide)))

theorem fz1_99_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨5, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 5 (by decide)))

theorem fz1_99_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨6, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 6 (by decide)))

theorem fz1_99_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨7, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 7 (by decide)))

theorem fz1_99_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨8, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 8 (by decide)))

theorem fz1_99_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨9, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 9 (by decide)))

theorem fz1_99_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨11, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 11 (by decide)))

theorem fz1_99_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨13, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 13 (by decide)))

theorem fz1_99_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨14, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 14 (by decide)))

theorem fz1_99_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨15, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 15 (by decide)))

theorem fz1_99_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨16, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 16 (by decide)))

theorem fz1_99_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨17, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 17 (by decide)))

theorem fz1_99_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨18, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 18 (by decide)))

theorem fz1_99_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨19, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 19 (by decide)))

theorem fz1_99_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨20, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 20 (by decide)))

theorem fz1_99_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨21, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 21 (by decide)))

theorem fz1_99_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨22, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 22 (by decide)))

theorem fz1_99_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨23, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 23 (by decide)))

theorem fz1_99_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨24, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 24 (by decide)))

theorem fz1_99_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨25, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 25 (by decide)))

theorem fz1_99_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨26, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 26 (by decide)))

theorem fz1_99_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨27, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 27 (by decide)))

theorem fz1_99_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨28, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 28 (by decide)))

theorem fz1_99_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨29, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 29 (by decide)))

theorem fz1_99_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨30, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 30 (by decide)))

theorem fz1_99_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨31, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 31 (by decide)))

theorem fz1_99_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨32, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 32 (by decide)))

theorem fz1_99_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨33, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 33 (by decide)))

theorem fz1_99_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨34, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 34 (by decide)))

theorem fz1_99_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨35, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 35 (by decide)))

theorem fz1_99_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨36, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 36 (by decide)))

theorem fz1_99_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨38, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 38 (by decide)))

theorem fz1_99_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨39, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 39 (by decide)))

theorem fz1_99_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨40, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 40 (by decide)))

theorem fz1_99_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨41, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 41 (by decide)))

theorem fz1_99_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨42, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 42 (by decide)))

theorem fz1_99_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨43, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 43 (by decide)))

theorem fz1_99_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨44, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 44 (by decide)))

theorem fz1_99_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨45, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 45 (by decide)))

theorem fz1_99_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨46, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 46 (by decide)))

theorem fz1_99_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨47, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 47 (by decide)))

theorem fz1_99_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨48, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 48 (by decide)))

theorem fz1_99_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨49, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 49 (by decide)))

theorem fz1_99_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨50, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 50 (by decide)))

theorem fz1_99_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨51, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 51 (by decide)))

theorem fz1_99_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨52, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 52 (by decide)))

theorem fz1_99_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨54, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 54 (by decide)))

theorem fz1_99_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨55, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 55 (by decide)))

theorem fz1_99_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨56, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 56 (by decide)))

theorem fz1_99_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨57, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 57 (by decide)))

theorem fz1_99_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨58, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 58 (by decide)))

theorem fz1_99_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨59, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 59 (by decide)))

theorem fz1_99_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨60, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 60 (by decide)))

theorem fz1_99_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨61, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 61 (by decide)))

theorem fz1_99_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨62, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 62 (by decide)))

theorem fz1_99_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨63, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 63 (by decide)))

theorem fz1_99_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨64, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 64 (by decide)))

theorem fz1_99_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨65, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 65 (by decide)))

theorem fz1_99_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨66, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 66 (by decide)))

theorem fz1_99_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨67, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 67 (by decide)))

theorem fz1_99_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨68, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 68 (by decide)))

theorem fz1_99_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨69, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 69 (by decide)))

theorem fz1_99_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨70, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 70 (by decide)))

theorem fz1_99_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨71, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 71 (by decide)))

theorem fz1_99_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨72, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 72 (by decide)))

theorem fz1_99_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨73, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 73 (by decide)))

theorem fz1_99_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨74, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 74 (by decide)))

theorem fz1_99_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨75, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 75 (by decide)))

theorem fz1_99_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨76, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 76 (by decide)))

theorem fz1_99_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨77, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 77 (by decide)))

theorem fz1_99_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨78, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 78 (by decide)))

theorem fz1_99_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨79, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 79 (by decide)))

theorem fz1_99_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨80, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 80 (by decide)))

theorem fz1_99_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨81, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 81 (by decide)))

theorem fz1_99_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨82, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 82 (by decide)))

theorem fz1_99_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨83, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 83 (by decide)))

theorem fz1_99_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨84, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 84 (by decide)))

theorem fz1_99_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨85, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 85 (by decide)))

theorem fz1_99_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨86, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 86 (by decide)))

theorem fz1_99_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨87, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 87 (by decide)))

theorem fz1_99_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨88, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 88 (by decide)))

theorem fz1_99_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨89, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 89 (by decide)))

theorem fz1_99_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨90, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 90 (by decide)))

theorem fz1_99_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨91, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 91 (by decide)))

theorem fz1_99_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨92, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 92 (by decide)))

theorem fz1_99_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨93, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 93 (by decide)))

theorem fz1_99_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨94, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 94 (by decide)))

theorem fz1_99_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨95, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 95 (by decide)))

theorem fz1_99_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨96, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 96 (by decide)))

theorem fz1_99_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨97, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 97 (by decide)))

theorem fz1_99_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨98, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 98 (by decide)))

theorem fz1_99_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨100, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 100 (by decide)))

theorem fz1_99_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨101, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 101 (by decide)))

theorem fz1_99_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨102, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 102 (by decide)))

theorem fz1_99_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨103, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 103 (by decide)))

theorem fz1_99_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨104, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 104 (by decide)))

theorem fz1_99_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨105, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 105 (by decide)))

theorem fz1_99_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨106, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 106 (by decide)))

theorem fz1_99_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨107, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 107 (by decide)))

theorem fz1_99_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨108, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 108 (by decide)))

theorem fz1_99_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨109, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 109 (by decide)))

theorem fz1_99_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨110, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 110 (by decide)))

theorem fz1_99_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨111, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 111 (by decide)))

theorem fz1_99_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨112, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 112 (by decide)))

theorem fz1_99_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨113, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 113 (by decide)))

theorem fz1_99_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨114, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 114 (by decide)))

theorem fz1_99_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK99)) = 0 :=
  repsFixedCard rK99 ⟨115, by decide⟩ R99 hpxR99 hcardq99
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_99) 115 (by decide)))

theorem fixz2_99 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK99) (retConj 2 (Q2.R99_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_99_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨1, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 1 (by decide)))

theorem fz2_99_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨2, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 2 (by decide)))

theorem fz2_99_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨3, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 3 (by decide)))

theorem fz2_99_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨4, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 4 (by decide)))

theorem fz2_99_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨5, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 5 (by decide)))

theorem fz2_99_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨6, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 6 (by decide)))

theorem fz2_99_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨7, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 7 (by decide)))

theorem fz2_99_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨8, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 8 (by decide)))

theorem fz2_99_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨9, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 9 (by decide)))

theorem fz2_99_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨11, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 11 (by decide)))

theorem fz2_99_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨13, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 13 (by decide)))

theorem fz2_99_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨14, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 14 (by decide)))

theorem fz2_99_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨15, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 15 (by decide)))

theorem fz2_99_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨16, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 16 (by decide)))

theorem fz2_99_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨17, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 17 (by decide)))

theorem fz2_99_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨18, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 18 (by decide)))

theorem fz2_99_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨19, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 19 (by decide)))

theorem fz2_99_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨20, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 20 (by decide)))

theorem fz2_99_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨21, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 21 (by decide)))

theorem fz2_99_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨22, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 22 (by decide)))

theorem fz2_99_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨23, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 23 (by decide)))

theorem fz2_99_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨24, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 24 (by decide)))

theorem fz2_99_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨25, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 25 (by decide)))

theorem fz2_99_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨26, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 26 (by decide)))

theorem fz2_99_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨27, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 27 (by decide)))

theorem fz2_99_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨28, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 28 (by decide)))

theorem fz2_99_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨29, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 29 (by decide)))

theorem fz2_99_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨30, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 30 (by decide)))

theorem fz2_99_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨31, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 31 (by decide)))

theorem fz2_99_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨32, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 32 (by decide)))

theorem fz2_99_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨33, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 33 (by decide)))

theorem fz2_99_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨34, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 34 (by decide)))

theorem fz2_99_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨35, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 35 (by decide)))

theorem fz2_99_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨36, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 36 (by decide)))

theorem fz2_99_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨38, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 38 (by decide)))

theorem fz2_99_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨39, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 39 (by decide)))

theorem fz2_99_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨40, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 40 (by decide)))

theorem fz2_99_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨41, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 41 (by decide)))

theorem fz2_99_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨42, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 42 (by decide)))

theorem fz2_99_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨43, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 43 (by decide)))

theorem fz2_99_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨44, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 44 (by decide)))

theorem fz2_99_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨45, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 45 (by decide)))

theorem fz2_99_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨46, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 46 (by decide)))

theorem fz2_99_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨47, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 47 (by decide)))

theorem fz2_99_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨48, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 48 (by decide)))

theorem fz2_99_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨49, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 49 (by decide)))

theorem fz2_99_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨50, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 50 (by decide)))

theorem fz2_99_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨51, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 51 (by decide)))

theorem fz2_99_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨52, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 52 (by decide)))

theorem fz2_99_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨54, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 54 (by decide)))

theorem fz2_99_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨55, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 55 (by decide)))

theorem fz2_99_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨56, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 56 (by decide)))

theorem fz2_99_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨57, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 57 (by decide)))

theorem fz2_99_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨58, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 58 (by decide)))

theorem fz2_99_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨59, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 59 (by decide)))

theorem fz2_99_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨60, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 60 (by decide)))

theorem fz2_99_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨61, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 61 (by decide)))

theorem fz2_99_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨62, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 62 (by decide)))

theorem fz2_99_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨63, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 63 (by decide)))

theorem fz2_99_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨64, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 64 (by decide)))

theorem fz2_99_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨65, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 65 (by decide)))

theorem fz2_99_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨66, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 66 (by decide)))

theorem fz2_99_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨67, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 67 (by decide)))

theorem fz2_99_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨68, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 68 (by decide)))

theorem fz2_99_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨69, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 69 (by decide)))

theorem fz2_99_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨70, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 70 (by decide)))

theorem fz2_99_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨71, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 71 (by decide)))

theorem fz2_99_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨72, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 72 (by decide)))

theorem fz2_99_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨73, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 73 (by decide)))

theorem fz2_99_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨74, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 74 (by decide)))

theorem fz2_99_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨75, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 75 (by decide)))

theorem fz2_99_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨76, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 76 (by decide)))

theorem fz2_99_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨77, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 77 (by decide)))

theorem fz2_99_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨78, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 78 (by decide)))

theorem fz2_99_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨79, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 79 (by decide)))

theorem fz2_99_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨80, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 80 (by decide)))

theorem fz2_99_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨81, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 81 (by decide)))

theorem fz2_99_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨82, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 82 (by decide)))

theorem fz2_99_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨83, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 83 (by decide)))

theorem fz2_99_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨84, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 84 (by decide)))

theorem fz2_99_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨85, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 85 (by decide)))

theorem fz2_99_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨86, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 86 (by decide)))

theorem fz2_99_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨87, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 87 (by decide)))

theorem fz2_99_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨88, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 88 (by decide)))

theorem fz2_99_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨89, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 89 (by decide)))

theorem fz2_99_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨90, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 90 (by decide)))

theorem fz2_99_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨91, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 91 (by decide)))

theorem fz2_99_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨92, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 92 (by decide)))

theorem fz2_99_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨93, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 93 (by decide)))

theorem fz2_99_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨94, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 94 (by decide)))

theorem fz2_99_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨95, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 95 (by decide)))

theorem fz2_99_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨96, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 96 (by decide)))

theorem fz2_99_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨97, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 97 (by decide)))

theorem fz2_99_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨98, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 98 (by decide)))

theorem fz2_99_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨100, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 100 (by decide)))

theorem fz2_99_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨101, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 101 (by decide)))

theorem fz2_99_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨102, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 102 (by decide)))

theorem fz2_99_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨103, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 103 (by decide)))

theorem fz2_99_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨104, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 104 (by decide)))

theorem fz2_99_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨105, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 105 (by decide)))

theorem fz2_99_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨106, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 106 (by decide)))

theorem fz2_99_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨107, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 107 (by decide)))

theorem fz2_99_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨108, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 108 (by decide)))

theorem fz2_99_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨109, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 109 (by decide)))

theorem fz2_99_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨110, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 110 (by decide)))

theorem fz2_99_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨111, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 111 (by decide)))

theorem fz2_99_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨112, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 112 (by decide)))

theorem fz2_99_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨113, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 113 (by decide)))

theorem fz2_99_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨114, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 114 (by decide)))

theorem fz2_99_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK99)) = 0 :=
  Q2.repsFixedCard2 rK99 ⟨115, by decide⟩ Q2.R99_2 Q2.hpxR99_2 Q2.hcardq99_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_99) 115 (by decide)))

theorem fixz1_100 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK100) (retConj 1 (R100 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_100_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨1, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 1 (by decide)))

theorem fz1_100_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨2, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 2 (by decide)))

theorem fz1_100_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨3, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 3 (by decide)))

theorem fz1_100_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨4, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 4 (by decide)))

theorem fz1_100_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨5, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 5 (by decide)))

theorem fz1_100_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨6, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 6 (by decide)))

theorem fz1_100_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨7, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 7 (by decide)))

theorem fz1_100_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨8, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 8 (by decide)))

theorem fz1_100_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨9, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 9 (by decide)))

theorem fz1_100_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨11, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 11 (by decide)))

theorem fz1_100_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨13, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 13 (by decide)))

theorem fz1_100_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨14, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 14 (by decide)))

theorem fz1_100_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨15, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 15 (by decide)))

theorem fz1_100_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨16, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 16 (by decide)))

theorem fz1_100_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨17, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 17 (by decide)))

theorem fz1_100_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨18, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 18 (by decide)))

theorem fz1_100_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨19, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 19 (by decide)))

theorem fz1_100_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨20, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 20 (by decide)))

theorem fz1_100_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨21, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 21 (by decide)))

theorem fz1_100_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨22, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 22 (by decide)))

theorem fz1_100_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨23, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 23 (by decide)))

theorem fz1_100_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨24, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 24 (by decide)))

theorem fz1_100_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨25, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 25 (by decide)))

theorem fz1_100_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨26, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 26 (by decide)))

theorem fz1_100_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨27, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 27 (by decide)))

theorem fz1_100_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨28, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 28 (by decide)))

theorem fz1_100_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨29, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 29 (by decide)))

theorem fz1_100_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨30, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 30 (by decide)))

theorem fz1_100_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨31, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 31 (by decide)))

theorem fz1_100_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨32, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 32 (by decide)))

theorem fz1_100_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨33, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 33 (by decide)))

theorem fz1_100_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨34, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 34 (by decide)))

theorem fz1_100_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨35, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 35 (by decide)))

theorem fz1_100_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨36, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 36 (by decide)))

theorem fz1_100_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨37, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 37 (by decide)))

theorem fz1_100_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨39, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 39 (by decide)))

theorem fz1_100_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨40, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 40 (by decide)))

theorem fz1_100_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨41, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 41 (by decide)))

theorem fz1_100_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨42, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 42 (by decide)))

theorem fz1_100_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨43, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 43 (by decide)))

theorem fz1_100_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨44, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 44 (by decide)))

theorem fz1_100_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨45, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 45 (by decide)))

theorem fz1_100_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨46, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 46 (by decide)))

theorem fz1_100_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨47, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 47 (by decide)))

theorem fz1_100_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨48, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 48 (by decide)))

theorem fz1_100_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨49, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 49 (by decide)))

theorem fz1_100_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨50, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 50 (by decide)))

theorem fz1_100_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨51, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 51 (by decide)))

theorem fz1_100_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨52, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 52 (by decide)))

theorem fz1_100_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨54, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 54 (by decide)))

theorem fz1_100_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨55, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 55 (by decide)))

theorem fz1_100_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨56, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 56 (by decide)))

theorem fz1_100_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨57, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 57 (by decide)))

theorem fz1_100_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨58, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 58 (by decide)))

theorem fz1_100_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨59, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 59 (by decide)))

theorem fz1_100_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨60, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 60 (by decide)))

theorem fz1_100_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨61, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 61 (by decide)))

theorem fz1_100_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨62, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 62 (by decide)))

theorem fz1_100_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨63, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 63 (by decide)))

theorem fz1_100_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨64, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 64 (by decide)))

theorem fz1_100_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨65, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 65 (by decide)))

theorem fz1_100_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨66, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 66 (by decide)))

theorem fz1_100_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨67, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 67 (by decide)))

theorem fz1_100_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨68, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 68 (by decide)))

theorem fz1_100_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨69, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 69 (by decide)))

theorem fz1_100_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨70, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 70 (by decide)))

theorem fz1_100_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨71, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 71 (by decide)))

theorem fz1_100_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨72, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 72 (by decide)))

theorem fz1_100_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨73, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 73 (by decide)))

theorem fz1_100_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨74, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 74 (by decide)))

theorem fz1_100_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨75, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 75 (by decide)))

theorem fz1_100_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨76, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 76 (by decide)))

theorem fz1_100_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨77, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 77 (by decide)))

theorem fz1_100_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨78, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 78 (by decide)))

theorem fz1_100_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨79, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 79 (by decide)))

theorem fz1_100_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨80, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 80 (by decide)))

theorem fz1_100_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨81, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 81 (by decide)))

theorem fz1_100_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨82, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 82 (by decide)))

theorem fz1_100_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨83, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 83 (by decide)))

theorem fz1_100_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨84, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 84 (by decide)))

theorem fz1_100_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨85, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 85 (by decide)))

theorem fz1_100_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨86, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 86 (by decide)))

theorem fz1_100_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨87, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 87 (by decide)))

theorem fz1_100_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨88, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 88 (by decide)))

theorem fz1_100_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨89, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 89 (by decide)))

theorem fz1_100_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨90, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 90 (by decide)))

theorem fz1_100_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨91, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 91 (by decide)))

theorem fz1_100_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨92, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 92 (by decide)))

theorem fz1_100_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨93, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 93 (by decide)))

theorem fz1_100_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨94, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 94 (by decide)))

theorem fz1_100_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨95, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 95 (by decide)))

theorem fz1_100_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨96, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 96 (by decide)))

theorem fz1_100_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨97, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 97 (by decide)))

theorem fz1_100_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨98, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 98 (by decide)))

theorem fz1_100_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨99, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 99 (by decide)))

theorem fz1_100_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨101, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 101 (by decide)))

theorem fz1_100_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨102, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 102 (by decide)))

theorem fz1_100_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨103, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 103 (by decide)))

theorem fz1_100_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨104, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 104 (by decide)))

theorem fz1_100_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨105, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 105 (by decide)))

theorem fz1_100_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨106, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 106 (by decide)))

theorem fz1_100_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨107, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 107 (by decide)))

theorem fz1_100_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨108, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 108 (by decide)))

theorem fz1_100_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨109, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 109 (by decide)))

theorem fz1_100_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨110, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 110 (by decide)))

theorem fz1_100_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨111, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 111 (by decide)))

theorem fz1_100_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨112, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 112 (by decide)))

theorem fz1_100_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨113, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 113 (by decide)))

theorem fz1_100_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨114, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 114 (by decide)))

theorem fz1_100_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK100)) = 0 :=
  repsFixedCard rK100 ⟨115, by decide⟩ R100 hpxR100 hcardq100
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_100) 115 (by decide)))

theorem fixz2_100 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK100) (retConj 2 (Q2.R100_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_100_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨1, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 1 (by decide)))

theorem fz2_100_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨2, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 2 (by decide)))

theorem fz2_100_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨3, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 3 (by decide)))

theorem fz2_100_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨4, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 4 (by decide)))

theorem fz2_100_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨5, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 5 (by decide)))

theorem fz2_100_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨6, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 6 (by decide)))

theorem fz2_100_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨7, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 7 (by decide)))

theorem fz2_100_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨8, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 8 (by decide)))

theorem fz2_100_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨9, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 9 (by decide)))

theorem fz2_100_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨11, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 11 (by decide)))

theorem fz2_100_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨13, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 13 (by decide)))

theorem fz2_100_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨14, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 14 (by decide)))

theorem fz2_100_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨15, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 15 (by decide)))

theorem fz2_100_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨16, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 16 (by decide)))

theorem fz2_100_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨17, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 17 (by decide)))

theorem fz2_100_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨18, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 18 (by decide)))

theorem fz2_100_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨19, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 19 (by decide)))

theorem fz2_100_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨20, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 20 (by decide)))

theorem fz2_100_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨21, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 21 (by decide)))

theorem fz2_100_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨22, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 22 (by decide)))

theorem fz2_100_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨23, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 23 (by decide)))

theorem fz2_100_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨24, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 24 (by decide)))

theorem fz2_100_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨25, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 25 (by decide)))

theorem fz2_100_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨26, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 26 (by decide)))

theorem fz2_100_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨27, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 27 (by decide)))

theorem fz2_100_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨28, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 28 (by decide)))

theorem fz2_100_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨29, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 29 (by decide)))

theorem fz2_100_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨30, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 30 (by decide)))

theorem fz2_100_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨31, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 31 (by decide)))

theorem fz2_100_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨32, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 32 (by decide)))

theorem fz2_100_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨33, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 33 (by decide)))

theorem fz2_100_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨34, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 34 (by decide)))

theorem fz2_100_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨35, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 35 (by decide)))

theorem fz2_100_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨36, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 36 (by decide)))

theorem fz2_100_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨37, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 37 (by decide)))

theorem fz2_100_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨39, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 39 (by decide)))

theorem fz2_100_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨40, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 40 (by decide)))

theorem fz2_100_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨41, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 41 (by decide)))

theorem fz2_100_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨42, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 42 (by decide)))

theorem fz2_100_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨43, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 43 (by decide)))

theorem fz2_100_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨44, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 44 (by decide)))

theorem fz2_100_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨45, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 45 (by decide)))

theorem fz2_100_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨46, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 46 (by decide)))

theorem fz2_100_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨47, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 47 (by decide)))

theorem fz2_100_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨48, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 48 (by decide)))

theorem fz2_100_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨49, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 49 (by decide)))

theorem fz2_100_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨50, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 50 (by decide)))

theorem fz2_100_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨51, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 51 (by decide)))

theorem fz2_100_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨52, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 52 (by decide)))

theorem fz2_100_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨54, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 54 (by decide)))

theorem fz2_100_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨55, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 55 (by decide)))

theorem fz2_100_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨56, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 56 (by decide)))

theorem fz2_100_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨57, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 57 (by decide)))

theorem fz2_100_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨58, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 58 (by decide)))

theorem fz2_100_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨59, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 59 (by decide)))

theorem fz2_100_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨60, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 60 (by decide)))

theorem fz2_100_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨61, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 61 (by decide)))

theorem fz2_100_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨62, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 62 (by decide)))

theorem fz2_100_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨63, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 63 (by decide)))

theorem fz2_100_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨64, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 64 (by decide)))

theorem fz2_100_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨65, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 65 (by decide)))

theorem fz2_100_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨66, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 66 (by decide)))

theorem fz2_100_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨67, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 67 (by decide)))

theorem fz2_100_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨68, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 68 (by decide)))

theorem fz2_100_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨69, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 69 (by decide)))

theorem fz2_100_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨70, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 70 (by decide)))

theorem fz2_100_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨71, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 71 (by decide)))

theorem fz2_100_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨72, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 72 (by decide)))

theorem fz2_100_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨73, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 73 (by decide)))

theorem fz2_100_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨74, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 74 (by decide)))

theorem fz2_100_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨75, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 75 (by decide)))

theorem fz2_100_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨76, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 76 (by decide)))

theorem fz2_100_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨77, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 77 (by decide)))

theorem fz2_100_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨78, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 78 (by decide)))

theorem fz2_100_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨79, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 79 (by decide)))

theorem fz2_100_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨80, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 80 (by decide)))

theorem fz2_100_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨81, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 81 (by decide)))

theorem fz2_100_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨82, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 82 (by decide)))

theorem fz2_100_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨83, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 83 (by decide)))

theorem fz2_100_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨84, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 84 (by decide)))

theorem fz2_100_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨85, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 85 (by decide)))

theorem fz2_100_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨86, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 86 (by decide)))

theorem fz2_100_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨87, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 87 (by decide)))

theorem fz2_100_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨88, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 88 (by decide)))

theorem fz2_100_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨89, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 89 (by decide)))

theorem fz2_100_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨90, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 90 (by decide)))

theorem fz2_100_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨91, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 91 (by decide)))

theorem fz2_100_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨92, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 92 (by decide)))

theorem fz2_100_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨93, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 93 (by decide)))

theorem fz2_100_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨94, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 94 (by decide)))

theorem fz2_100_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨95, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 95 (by decide)))

theorem fz2_100_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨96, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 96 (by decide)))

theorem fz2_100_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨97, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 97 (by decide)))

theorem fz2_100_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨98, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 98 (by decide)))

theorem fz2_100_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨99, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 99 (by decide)))

theorem fz2_100_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨101, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 101 (by decide)))

theorem fz2_100_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨102, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 102 (by decide)))

theorem fz2_100_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨103, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 103 (by decide)))

theorem fz2_100_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨104, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 104 (by decide)))

theorem fz2_100_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨105, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 105 (by decide)))

theorem fz2_100_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨106, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 106 (by decide)))

theorem fz2_100_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨107, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 107 (by decide)))

theorem fz2_100_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨108, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 108 (by decide)))

theorem fz2_100_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨109, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 109 (by decide)))

theorem fz2_100_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨110, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 110 (by decide)))

theorem fz2_100_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨111, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 111 (by decide)))

theorem fz2_100_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨112, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 112 (by decide)))

theorem fz2_100_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨113, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 113 (by decide)))

theorem fz2_100_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨114, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 114 (by decide)))

theorem fz2_100_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK100)) = 0 :=
  Q2.repsFixedCard2 rK100 ⟨115, by decide⟩ Q2.R100_2 Q2.hpxR100_2 Q2.hcardq100_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_100) 115 (by decide)))

end LeanDring.P5Presentation
