/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C022

/-!
# Species-table cells, off-support emptiness certificates, chunk 73

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

theorem fixz1_93 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK93) (retConj 1 (R93 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_93_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨1, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 1 (by decide)))

theorem fz1_93_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨2, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 2 (by decide)))

theorem fz1_93_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨3, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 3 (by decide)))

theorem fz1_93_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨4, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 4 (by decide)))

theorem fz1_93_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨5, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 5 (by decide)))

theorem fz1_93_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨6, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 6 (by decide)))

theorem fz1_93_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨7, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 7 (by decide)))

theorem fz1_93_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨8, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 8 (by decide)))

theorem fz1_93_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨9, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 9 (by decide)))

theorem fz1_93_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨11, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 11 (by decide)))

theorem fz1_93_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨13, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 13 (by decide)))

theorem fz1_93_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨14, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 14 (by decide)))

theorem fz1_93_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨15, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 15 (by decide)))

theorem fz1_93_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨16, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 16 (by decide)))

theorem fz1_93_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨17, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 17 (by decide)))

theorem fz1_93_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨18, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 18 (by decide)))

theorem fz1_93_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨19, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 19 (by decide)))

theorem fz1_93_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨20, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 20 (by decide)))

theorem fz1_93_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨21, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 21 (by decide)))

theorem fz1_93_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨22, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 22 (by decide)))

theorem fz1_93_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨23, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 23 (by decide)))

theorem fz1_93_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨24, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 24 (by decide)))

theorem fz1_93_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨25, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 25 (by decide)))

theorem fz1_93_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨26, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 26 (by decide)))

theorem fz1_93_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨27, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 27 (by decide)))

theorem fz1_93_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨28, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 28 (by decide)))

theorem fz1_93_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨29, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 29 (by decide)))

theorem fz1_93_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨30, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 30 (by decide)))

theorem fz1_93_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨32, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 32 (by decide)))

theorem fz1_93_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨33, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 33 (by decide)))

theorem fz1_93_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨34, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 34 (by decide)))

theorem fz1_93_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨35, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 35 (by decide)))

theorem fz1_93_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨36, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 36 (by decide)))

theorem fz1_93_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨37, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 37 (by decide)))

theorem fz1_93_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨38, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 38 (by decide)))

theorem fz1_93_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨39, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 39 (by decide)))

theorem fz1_93_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨40, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 40 (by decide)))

theorem fz1_93_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨41, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 41 (by decide)))

theorem fz1_93_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨42, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 42 (by decide)))

theorem fz1_93_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨43, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 43 (by decide)))

theorem fz1_93_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨44, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 44 (by decide)))

theorem fz1_93_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨45, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 45 (by decide)))

theorem fz1_93_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨46, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 46 (by decide)))

theorem fz1_93_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨47, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 47 (by decide)))

theorem fz1_93_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨48, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 48 (by decide)))

theorem fz1_93_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨49, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 49 (by decide)))

theorem fz1_93_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨50, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 50 (by decide)))

theorem fz1_93_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨51, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 51 (by decide)))

theorem fz1_93_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨52, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 52 (by decide)))

theorem fz1_93_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨54, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 54 (by decide)))

theorem fz1_93_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨55, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 55 (by decide)))

theorem fz1_93_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨56, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 56 (by decide)))

theorem fz1_93_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨57, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 57 (by decide)))

theorem fz1_93_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨58, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 58 (by decide)))

theorem fz1_93_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨59, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 59 (by decide)))

theorem fz1_93_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨60, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 60 (by decide)))

theorem fz1_93_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨61, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 61 (by decide)))

theorem fz1_93_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨62, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 62 (by decide)))

theorem fz1_93_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨63, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 63 (by decide)))

theorem fz1_93_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨64, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 64 (by decide)))

theorem fz1_93_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨65, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 65 (by decide)))

theorem fz1_93_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨66, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 66 (by decide)))

theorem fz1_93_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨67, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 67 (by decide)))

theorem fz1_93_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨68, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 68 (by decide)))

theorem fz1_93_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨69, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 69 (by decide)))

theorem fz1_93_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨70, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 70 (by decide)))

theorem fz1_93_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨71, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 71 (by decide)))

theorem fz1_93_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨72, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 72 (by decide)))

theorem fz1_93_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨73, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 73 (by decide)))

theorem fz1_93_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨74, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 74 (by decide)))

theorem fz1_93_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨75, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 75 (by decide)))

theorem fz1_93_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨76, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 76 (by decide)))

theorem fz1_93_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨77, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 77 (by decide)))

theorem fz1_93_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨78, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 78 (by decide)))

theorem fz1_93_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨79, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 79 (by decide)))

theorem fz1_93_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨80, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 80 (by decide)))

theorem fz1_93_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨81, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 81 (by decide)))

theorem fz1_93_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨82, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 82 (by decide)))

theorem fz1_93_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨83, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 83 (by decide)))

theorem fz1_93_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨84, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 84 (by decide)))

theorem fz1_93_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨85, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 85 (by decide)))

theorem fz1_93_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨86, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 86 (by decide)))

theorem fz1_93_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨87, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 87 (by decide)))

theorem fz1_93_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨88, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 88 (by decide)))

theorem fz1_93_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨89, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 89 (by decide)))

theorem fz1_93_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨90, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 90 (by decide)))

theorem fz1_93_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨91, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 91 (by decide)))

theorem fz1_93_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨92, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 92 (by decide)))

theorem fz1_93_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨94, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 94 (by decide)))

theorem fz1_93_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨95, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 95 (by decide)))

theorem fz1_93_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨96, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 96 (by decide)))

theorem fz1_93_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨97, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 97 (by decide)))

theorem fz1_93_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨98, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 98 (by decide)))

theorem fz1_93_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨99, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 99 (by decide)))

theorem fz1_93_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨100, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 100 (by decide)))

theorem fz1_93_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨101, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 101 (by decide)))

theorem fz1_93_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨102, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 102 (by decide)))

theorem fz1_93_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨103, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 103 (by decide)))

theorem fz1_93_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨104, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 104 (by decide)))

theorem fz1_93_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨105, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 105 (by decide)))

theorem fz1_93_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨106, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 106 (by decide)))

theorem fz1_93_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨107, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 107 (by decide)))

theorem fz1_93_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨108, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 108 (by decide)))

theorem fz1_93_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨109, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 109 (by decide)))

theorem fz1_93_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨110, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 110 (by decide)))

theorem fz1_93_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨111, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 111 (by decide)))

theorem fz1_93_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨112, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 112 (by decide)))

theorem fz1_93_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨113, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 113 (by decide)))

theorem fz1_93_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨114, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 114 (by decide)))

theorem fz1_93_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK93)) = 0 :=
  repsFixedCard rK93 ⟨115, by decide⟩ R93 hpxR93 hcardq93
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_93) 115 (by decide)))

theorem fixz2_93 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK93) (retConj 2 (Q2.R93_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_93_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨1, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 1 (by decide)))

theorem fz2_93_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨2, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 2 (by decide)))

theorem fz2_93_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨3, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 3 (by decide)))

theorem fz2_93_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨4, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 4 (by decide)))

theorem fz2_93_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨5, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 5 (by decide)))

theorem fz2_93_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨6, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 6 (by decide)))

theorem fz2_93_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨7, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 7 (by decide)))

theorem fz2_93_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨8, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 8 (by decide)))

theorem fz2_93_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨9, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 9 (by decide)))

theorem fz2_93_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨11, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 11 (by decide)))

theorem fz2_93_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨13, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 13 (by decide)))

theorem fz2_93_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨14, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 14 (by decide)))

theorem fz2_93_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨15, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 15 (by decide)))

theorem fz2_93_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨16, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 16 (by decide)))

theorem fz2_93_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨17, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 17 (by decide)))

theorem fz2_93_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨18, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 18 (by decide)))

theorem fz2_93_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨19, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 19 (by decide)))

theorem fz2_93_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨20, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 20 (by decide)))

theorem fz2_93_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨21, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 21 (by decide)))

theorem fz2_93_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨22, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 22 (by decide)))

theorem fz2_93_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨23, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 23 (by decide)))

theorem fz2_93_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨24, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 24 (by decide)))

theorem fz2_93_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨25, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 25 (by decide)))

theorem fz2_93_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨26, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 26 (by decide)))

theorem fz2_93_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨27, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 27 (by decide)))

theorem fz2_93_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨28, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 28 (by decide)))

theorem fz2_93_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨29, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 29 (by decide)))

theorem fz2_93_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨30, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 30 (by decide)))

theorem fz2_93_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨32, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 32 (by decide)))

theorem fz2_93_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨33, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 33 (by decide)))

theorem fz2_93_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨34, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 34 (by decide)))

theorem fz2_93_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨35, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 35 (by decide)))

theorem fz2_93_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨36, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 36 (by decide)))

theorem fz2_93_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨37, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 37 (by decide)))

theorem fz2_93_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨38, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 38 (by decide)))

theorem fz2_93_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨39, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 39 (by decide)))

theorem fz2_93_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨40, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 40 (by decide)))

theorem fz2_93_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨41, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 41 (by decide)))

theorem fz2_93_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨42, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 42 (by decide)))

theorem fz2_93_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨43, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 43 (by decide)))

theorem fz2_93_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨44, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 44 (by decide)))

theorem fz2_93_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨45, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 45 (by decide)))

theorem fz2_93_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨46, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 46 (by decide)))

theorem fz2_93_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨47, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 47 (by decide)))

theorem fz2_93_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨48, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 48 (by decide)))

theorem fz2_93_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨49, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 49 (by decide)))

theorem fz2_93_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨50, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 50 (by decide)))

theorem fz2_93_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨51, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 51 (by decide)))

theorem fz2_93_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨52, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 52 (by decide)))

theorem fz2_93_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨54, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 54 (by decide)))

theorem fz2_93_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨55, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 55 (by decide)))

theorem fz2_93_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨56, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 56 (by decide)))

theorem fz2_93_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨57, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 57 (by decide)))

theorem fz2_93_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨58, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 58 (by decide)))

theorem fz2_93_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨59, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 59 (by decide)))

theorem fz2_93_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨60, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 60 (by decide)))

theorem fz2_93_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨61, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 61 (by decide)))

theorem fz2_93_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨62, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 62 (by decide)))

theorem fz2_93_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨63, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 63 (by decide)))

theorem fz2_93_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨64, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 64 (by decide)))

theorem fz2_93_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨65, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 65 (by decide)))

theorem fz2_93_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨66, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 66 (by decide)))

theorem fz2_93_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨67, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 67 (by decide)))

theorem fz2_93_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨68, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 68 (by decide)))

theorem fz2_93_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨69, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 69 (by decide)))

theorem fz2_93_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨70, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 70 (by decide)))

theorem fz2_93_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨71, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 71 (by decide)))

theorem fz2_93_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨72, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 72 (by decide)))

theorem fz2_93_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨73, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 73 (by decide)))

theorem fz2_93_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨74, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 74 (by decide)))

theorem fz2_93_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨75, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 75 (by decide)))

theorem fz2_93_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨76, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 76 (by decide)))

theorem fz2_93_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨77, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 77 (by decide)))

theorem fz2_93_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨78, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 78 (by decide)))

theorem fz2_93_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨79, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 79 (by decide)))

theorem fz2_93_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨80, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 80 (by decide)))

theorem fz2_93_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨81, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 81 (by decide)))

theorem fz2_93_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨82, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 82 (by decide)))

theorem fz2_93_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨83, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 83 (by decide)))

theorem fz2_93_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨84, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 84 (by decide)))

theorem fz2_93_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨85, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 85 (by decide)))

theorem fz2_93_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨86, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 86 (by decide)))

theorem fz2_93_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨87, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 87 (by decide)))

theorem fz2_93_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨88, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 88 (by decide)))

theorem fz2_93_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨89, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 89 (by decide)))

theorem fz2_93_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨90, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 90 (by decide)))

theorem fz2_93_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨91, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 91 (by decide)))

theorem fz2_93_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨92, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 92 (by decide)))

theorem fz2_93_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨94, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 94 (by decide)))

theorem fz2_93_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨95, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 95 (by decide)))

theorem fz2_93_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨96, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 96 (by decide)))

theorem fz2_93_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨97, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 97 (by decide)))

theorem fz2_93_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨98, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 98 (by decide)))

theorem fz2_93_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨99, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 99 (by decide)))

theorem fz2_93_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨100, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 100 (by decide)))

theorem fz2_93_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨101, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 101 (by decide)))

theorem fz2_93_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨102, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 102 (by decide)))

theorem fz2_93_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨103, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 103 (by decide)))

theorem fz2_93_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨104, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 104 (by decide)))

theorem fz2_93_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨105, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 105 (by decide)))

theorem fz2_93_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨106, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 106 (by decide)))

theorem fz2_93_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨107, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 107 (by decide)))

theorem fz2_93_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨108, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 108 (by decide)))

theorem fz2_93_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨109, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 109 (by decide)))

theorem fz2_93_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨110, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 110 (by decide)))

theorem fz2_93_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨111, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 111 (by decide)))

theorem fz2_93_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨112, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 112 (by decide)))

theorem fz2_93_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨113, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 113 (by decide)))

theorem fz2_93_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨114, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 114 (by decide)))

theorem fz2_93_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK93)) = 0 :=
  Q2.repsFixedCard2 rK93 ⟨115, by decide⟩ Q2.R93_2 Q2.hpxR93_2 Q2.hcardq93_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_93) 115 (by decide)))

theorem fixz1_94 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK94) (retConj 1 (R94 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_94_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨1, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 1 (by decide)))

theorem fz1_94_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨2, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 2 (by decide)))

theorem fz1_94_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨3, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 3 (by decide)))

theorem fz1_94_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨4, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 4 (by decide)))

theorem fz1_94_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨5, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 5 (by decide)))

theorem fz1_94_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨6, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 6 (by decide)))

theorem fz1_94_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨7, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 7 (by decide)))

theorem fz1_94_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨8, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 8 (by decide)))

theorem fz1_94_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨9, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 9 (by decide)))

theorem fz1_94_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨11, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 11 (by decide)))

theorem fz1_94_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨13, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 13 (by decide)))

theorem fz1_94_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨14, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 14 (by decide)))

theorem fz1_94_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨15, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 15 (by decide)))

theorem fz1_94_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨16, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 16 (by decide)))

theorem fz1_94_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨17, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 17 (by decide)))

theorem fz1_94_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨18, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 18 (by decide)))

theorem fz1_94_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨19, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 19 (by decide)))

theorem fz1_94_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨20, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 20 (by decide)))

theorem fz1_94_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨21, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 21 (by decide)))

theorem fz1_94_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨22, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 22 (by decide)))

theorem fz1_94_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨23, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 23 (by decide)))

theorem fz1_94_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨24, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 24 (by decide)))

theorem fz1_94_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨25, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 25 (by decide)))

theorem fz1_94_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨26, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 26 (by decide)))

theorem fz1_94_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨27, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 27 (by decide)))

theorem fz1_94_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨28, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 28 (by decide)))

theorem fz1_94_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨29, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 29 (by decide)))

theorem fz1_94_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨30, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 30 (by decide)))

theorem fz1_94_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨31, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 31 (by decide)))

theorem fz1_94_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨33, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 33 (by decide)))

theorem fz1_94_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨34, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 34 (by decide)))

theorem fz1_94_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨35, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 35 (by decide)))

theorem fz1_94_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨36, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 36 (by decide)))

theorem fz1_94_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨37, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 37 (by decide)))

theorem fz1_94_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨38, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 38 (by decide)))

theorem fz1_94_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨39, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 39 (by decide)))

theorem fz1_94_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨40, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 40 (by decide)))

theorem fz1_94_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨41, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 41 (by decide)))

theorem fz1_94_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨42, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 42 (by decide)))

theorem fz1_94_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨43, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 43 (by decide)))

theorem fz1_94_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨44, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 44 (by decide)))

theorem fz1_94_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨45, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 45 (by decide)))

theorem fz1_94_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨46, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 46 (by decide)))

theorem fz1_94_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨47, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 47 (by decide)))

theorem fz1_94_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨48, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 48 (by decide)))

theorem fz1_94_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨49, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 49 (by decide)))

theorem fz1_94_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨50, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 50 (by decide)))

theorem fz1_94_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨51, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 51 (by decide)))

theorem fz1_94_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨52, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 52 (by decide)))

theorem fz1_94_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨54, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 54 (by decide)))

theorem fz1_94_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨55, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 55 (by decide)))

theorem fz1_94_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨56, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 56 (by decide)))

theorem fz1_94_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨57, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 57 (by decide)))

theorem fz1_94_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨58, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 58 (by decide)))

theorem fz1_94_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨59, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 59 (by decide)))

theorem fz1_94_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨60, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 60 (by decide)))

theorem fz1_94_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨61, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 61 (by decide)))

theorem fz1_94_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨62, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 62 (by decide)))

theorem fz1_94_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨63, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 63 (by decide)))

theorem fz1_94_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨64, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 64 (by decide)))

theorem fz1_94_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨65, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 65 (by decide)))

theorem fz1_94_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨66, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 66 (by decide)))

theorem fz1_94_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨67, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 67 (by decide)))

theorem fz1_94_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨68, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 68 (by decide)))

theorem fz1_94_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨69, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 69 (by decide)))

theorem fz1_94_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨70, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 70 (by decide)))

theorem fz1_94_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨71, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 71 (by decide)))

theorem fz1_94_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨72, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 72 (by decide)))

theorem fz1_94_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨73, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 73 (by decide)))

theorem fz1_94_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨74, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 74 (by decide)))

theorem fz1_94_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨75, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 75 (by decide)))

theorem fz1_94_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨76, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 76 (by decide)))

theorem fz1_94_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨77, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 77 (by decide)))

theorem fz1_94_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨78, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 78 (by decide)))

theorem fz1_94_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨79, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 79 (by decide)))

theorem fz1_94_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨80, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 80 (by decide)))

theorem fz1_94_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨81, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 81 (by decide)))

theorem fz1_94_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨82, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 82 (by decide)))

theorem fz1_94_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨83, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 83 (by decide)))

theorem fz1_94_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨84, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 84 (by decide)))

theorem fz1_94_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨85, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 85 (by decide)))

theorem fz1_94_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨86, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 86 (by decide)))

theorem fz1_94_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨87, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 87 (by decide)))

theorem fz1_94_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨88, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 88 (by decide)))

theorem fz1_94_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨89, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 89 (by decide)))

theorem fz1_94_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨90, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 90 (by decide)))

theorem fz1_94_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨91, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 91 (by decide)))

theorem fz1_94_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨92, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 92 (by decide)))

theorem fz1_94_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨93, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 93 (by decide)))

theorem fz1_94_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨95, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 95 (by decide)))

theorem fz1_94_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨96, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 96 (by decide)))

theorem fz1_94_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨97, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 97 (by decide)))

theorem fz1_94_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨98, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 98 (by decide)))

theorem fz1_94_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨99, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 99 (by decide)))

theorem fz1_94_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨100, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 100 (by decide)))

theorem fz1_94_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨101, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 101 (by decide)))

theorem fz1_94_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨102, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 102 (by decide)))

theorem fz1_94_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨103, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 103 (by decide)))

theorem fz1_94_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨104, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 104 (by decide)))

theorem fz1_94_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨105, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 105 (by decide)))

theorem fz1_94_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨106, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 106 (by decide)))

theorem fz1_94_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨107, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 107 (by decide)))

theorem fz1_94_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨108, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 108 (by decide)))

theorem fz1_94_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨109, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 109 (by decide)))

theorem fz1_94_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨110, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 110 (by decide)))

theorem fz1_94_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨111, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 111 (by decide)))

theorem fz1_94_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨112, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 112 (by decide)))

theorem fz1_94_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨113, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 113 (by decide)))

theorem fz1_94_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨114, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 114 (by decide)))

theorem fz1_94_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK94)) = 0 :=
  repsFixedCard rK94 ⟨115, by decide⟩ R94 hpxR94 hcardq94
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_94) 115 (by decide)))

theorem fixz2_94 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK94) (retConj 2 (Q2.R94_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_94_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨1, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 1 (by decide)))

theorem fz2_94_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨2, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 2 (by decide)))

theorem fz2_94_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨3, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 3 (by decide)))

theorem fz2_94_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨4, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 4 (by decide)))

theorem fz2_94_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨5, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 5 (by decide)))

theorem fz2_94_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨6, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 6 (by decide)))

theorem fz2_94_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨7, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 7 (by decide)))

theorem fz2_94_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨8, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 8 (by decide)))

theorem fz2_94_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨9, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 9 (by decide)))

theorem fz2_94_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨11, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 11 (by decide)))

theorem fz2_94_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨13, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 13 (by decide)))

theorem fz2_94_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨14, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 14 (by decide)))

theorem fz2_94_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨15, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 15 (by decide)))

theorem fz2_94_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨16, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 16 (by decide)))

theorem fz2_94_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨17, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 17 (by decide)))

theorem fz2_94_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨18, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 18 (by decide)))

theorem fz2_94_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨19, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 19 (by decide)))

theorem fz2_94_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨20, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 20 (by decide)))

theorem fz2_94_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨21, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 21 (by decide)))

theorem fz2_94_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨22, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 22 (by decide)))

theorem fz2_94_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨23, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 23 (by decide)))

theorem fz2_94_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨24, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 24 (by decide)))

theorem fz2_94_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨25, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 25 (by decide)))

theorem fz2_94_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨26, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 26 (by decide)))

theorem fz2_94_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨27, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 27 (by decide)))

theorem fz2_94_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨28, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 28 (by decide)))

theorem fz2_94_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨29, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 29 (by decide)))

theorem fz2_94_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨30, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 30 (by decide)))

theorem fz2_94_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨31, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 31 (by decide)))

theorem fz2_94_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨33, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 33 (by decide)))

theorem fz2_94_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨34, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 34 (by decide)))

theorem fz2_94_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨35, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 35 (by decide)))

theorem fz2_94_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨36, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 36 (by decide)))

theorem fz2_94_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨37, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 37 (by decide)))

theorem fz2_94_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨38, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 38 (by decide)))

theorem fz2_94_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨39, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 39 (by decide)))

theorem fz2_94_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨40, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 40 (by decide)))

theorem fz2_94_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨41, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 41 (by decide)))

theorem fz2_94_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨42, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 42 (by decide)))

theorem fz2_94_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨43, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 43 (by decide)))

theorem fz2_94_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨44, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 44 (by decide)))

theorem fz2_94_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨45, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 45 (by decide)))

theorem fz2_94_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨46, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 46 (by decide)))

theorem fz2_94_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨47, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 47 (by decide)))

theorem fz2_94_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨48, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 48 (by decide)))

theorem fz2_94_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨49, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 49 (by decide)))

theorem fz2_94_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨50, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 50 (by decide)))

theorem fz2_94_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨51, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 51 (by decide)))

theorem fz2_94_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨52, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 52 (by decide)))

theorem fz2_94_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨54, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 54 (by decide)))

theorem fz2_94_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨55, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 55 (by decide)))

theorem fz2_94_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨56, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 56 (by decide)))

theorem fz2_94_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨57, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 57 (by decide)))

theorem fz2_94_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨58, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 58 (by decide)))

theorem fz2_94_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨59, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 59 (by decide)))

theorem fz2_94_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨60, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 60 (by decide)))

theorem fz2_94_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨61, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 61 (by decide)))

theorem fz2_94_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨62, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 62 (by decide)))

theorem fz2_94_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨63, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 63 (by decide)))

theorem fz2_94_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨64, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 64 (by decide)))

theorem fz2_94_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨65, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 65 (by decide)))

theorem fz2_94_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨66, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 66 (by decide)))

theorem fz2_94_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨67, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 67 (by decide)))

theorem fz2_94_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨68, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 68 (by decide)))

theorem fz2_94_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨69, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 69 (by decide)))

theorem fz2_94_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨70, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 70 (by decide)))

theorem fz2_94_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨71, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 71 (by decide)))

theorem fz2_94_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨72, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 72 (by decide)))

theorem fz2_94_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨73, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 73 (by decide)))

theorem fz2_94_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨74, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 74 (by decide)))

theorem fz2_94_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨75, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 75 (by decide)))

theorem fz2_94_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨76, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 76 (by decide)))

theorem fz2_94_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨77, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 77 (by decide)))

theorem fz2_94_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨78, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 78 (by decide)))

theorem fz2_94_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨79, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 79 (by decide)))

theorem fz2_94_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨80, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 80 (by decide)))

theorem fz2_94_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨81, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 81 (by decide)))

theorem fz2_94_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨82, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 82 (by decide)))

theorem fz2_94_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨83, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 83 (by decide)))

theorem fz2_94_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨84, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 84 (by decide)))

theorem fz2_94_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨85, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 85 (by decide)))

theorem fz2_94_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨86, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 86 (by decide)))

theorem fz2_94_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨87, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 87 (by decide)))

theorem fz2_94_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨88, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 88 (by decide)))

theorem fz2_94_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨89, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 89 (by decide)))

theorem fz2_94_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨90, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 90 (by decide)))

theorem fz2_94_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨91, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 91 (by decide)))

theorem fz2_94_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨92, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 92 (by decide)))

theorem fz2_94_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨93, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 93 (by decide)))

theorem fz2_94_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨95, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 95 (by decide)))

theorem fz2_94_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨96, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 96 (by decide)))

theorem fz2_94_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨97, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 97 (by decide)))

theorem fz2_94_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨98, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 98 (by decide)))

theorem fz2_94_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨99, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 99 (by decide)))

theorem fz2_94_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨100, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 100 (by decide)))

theorem fz2_94_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨101, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 101 (by decide)))

theorem fz2_94_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨102, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 102 (by decide)))

theorem fz2_94_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨103, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 103 (by decide)))

theorem fz2_94_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨104, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 104 (by decide)))

theorem fz2_94_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨105, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 105 (by decide)))

theorem fz2_94_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨106, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 106 (by decide)))

theorem fz2_94_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨107, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 107 (by decide)))

theorem fz2_94_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨108, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 108 (by decide)))

theorem fz2_94_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨109, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 109 (by decide)))

theorem fz2_94_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨110, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 110 (by decide)))

theorem fz2_94_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨111, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 111 (by decide)))

theorem fz2_94_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨112, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 112 (by decide)))

theorem fz2_94_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨113, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 113 (by decide)))

theorem fz2_94_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨114, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 114 (by decide)))

theorem fz2_94_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK94)) = 0 :=
  Q2.repsFixedCard2 rK94 ⟨115, by decide⟩ Q2.R94_2 Q2.hpxR94_2 Q2.hcardq94_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_94) 115 (by decide)))

end LeanDring.P5Presentation
