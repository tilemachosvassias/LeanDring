/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C019

/-!
# Species-table cells, off-support emptiness certificates, chunk 68

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

theorem fixz1_83 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK83) (retConj 1 (R83 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_83_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨1, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 1 (by decide)))

theorem fz1_83_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨2, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 2 (by decide)))

theorem fz1_83_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨3, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 3 (by decide)))

theorem fz1_83_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨5, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 5 (by decide)))

theorem fz1_83_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨6, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 6 (by decide)))

theorem fz1_83_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨7, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 7 (by decide)))

theorem fz1_83_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨8, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 8 (by decide)))

theorem fz1_83_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨9, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 9 (by decide)))

theorem fz1_83_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨11, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 11 (by decide)))

theorem fz1_83_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨13, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 13 (by decide)))

theorem fz1_83_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨14, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 14 (by decide)))

theorem fz1_83_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨15, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 15 (by decide)))

theorem fz1_83_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨16, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 16 (by decide)))

theorem fz1_83_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨17, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 17 (by decide)))

theorem fz1_83_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨18, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 18 (by decide)))

theorem fz1_83_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨19, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 19 (by decide)))

theorem fz1_83_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨20, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 20 (by decide)))

theorem fz1_83_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨21, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 21 (by decide)))

theorem fz1_83_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨23, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 23 (by decide)))

theorem fz1_83_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨24, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 24 (by decide)))

theorem fz1_83_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨25, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 25 (by decide)))

theorem fz1_83_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨26, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 26 (by decide)))

theorem fz1_83_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨27, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 27 (by decide)))

theorem fz1_83_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨28, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 28 (by decide)))

theorem fz1_83_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨29, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 29 (by decide)))

theorem fz1_83_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨30, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 30 (by decide)))

theorem fz1_83_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨31, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 31 (by decide)))

theorem fz1_83_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨32, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 32 (by decide)))

theorem fz1_83_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨33, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 33 (by decide)))

theorem fz1_83_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨34, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 34 (by decide)))

theorem fz1_83_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨35, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 35 (by decide)))

theorem fz1_83_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨36, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 36 (by decide)))

theorem fz1_83_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨37, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 37 (by decide)))

theorem fz1_83_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨38, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 38 (by decide)))

theorem fz1_83_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨39, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 39 (by decide)))

theorem fz1_83_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨40, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 40 (by decide)))

theorem fz1_83_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨41, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 41 (by decide)))

theorem fz1_83_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨42, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 42 (by decide)))

theorem fz1_83_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨43, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 43 (by decide)))

theorem fz1_83_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨44, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 44 (by decide)))

theorem fz1_83_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨45, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 45 (by decide)))

theorem fz1_83_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨46, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 46 (by decide)))

theorem fz1_83_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨47, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 47 (by decide)))

theorem fz1_83_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨48, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 48 (by decide)))

theorem fz1_83_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨49, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 49 (by decide)))

theorem fz1_83_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨50, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 50 (by decide)))

theorem fz1_83_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨51, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 51 (by decide)))

theorem fz1_83_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨52, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 52 (by decide)))

theorem fz1_83_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨54, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 54 (by decide)))

theorem fz1_83_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨55, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 55 (by decide)))

theorem fz1_83_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨56, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 56 (by decide)))

theorem fz1_83_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨57, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 57 (by decide)))

theorem fz1_83_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨58, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 58 (by decide)))

theorem fz1_83_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨59, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 59 (by decide)))

theorem fz1_83_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨60, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 60 (by decide)))

theorem fz1_83_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨61, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 61 (by decide)))

theorem fz1_83_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨62, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 62 (by decide)))

theorem fz1_83_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨63, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 63 (by decide)))

theorem fz1_83_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨64, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 64 (by decide)))

theorem fz1_83_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨65, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 65 (by decide)))

theorem fz1_83_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨66, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 66 (by decide)))

theorem fz1_83_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨67, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 67 (by decide)))

theorem fz1_83_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨68, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 68 (by decide)))

theorem fz1_83_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨69, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 69 (by decide)))

theorem fz1_83_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨70, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 70 (by decide)))

theorem fz1_83_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨71, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 71 (by decide)))

theorem fz1_83_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨72, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 72 (by decide)))

theorem fz1_83_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨73, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 73 (by decide)))

theorem fz1_83_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨74, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 74 (by decide)))

theorem fz1_83_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨75, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 75 (by decide)))

theorem fz1_83_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨76, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 76 (by decide)))

theorem fz1_83_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨77, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 77 (by decide)))

theorem fz1_83_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨78, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 78 (by decide)))

theorem fz1_83_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨79, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 79 (by decide)))

theorem fz1_83_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨80, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 80 (by decide)))

theorem fz1_83_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨81, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 81 (by decide)))

theorem fz1_83_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨82, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 82 (by decide)))

theorem fz1_83_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨84, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 84 (by decide)))

theorem fz1_83_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨85, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 85 (by decide)))

theorem fz1_83_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨86, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 86 (by decide)))

theorem fz1_83_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨87, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 87 (by decide)))

theorem fz1_83_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨88, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 88 (by decide)))

theorem fz1_83_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨89, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 89 (by decide)))

theorem fz1_83_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨90, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 90 (by decide)))

theorem fz1_83_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨91, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 91 (by decide)))

theorem fz1_83_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨92, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 92 (by decide)))

theorem fz1_83_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨93, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 93 (by decide)))

theorem fz1_83_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨94, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 94 (by decide)))

theorem fz1_83_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨95, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 95 (by decide)))

theorem fz1_83_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨96, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 96 (by decide)))

theorem fz1_83_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨97, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 97 (by decide)))

theorem fz1_83_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨98, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 98 (by decide)))

theorem fz1_83_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨99, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 99 (by decide)))

theorem fz1_83_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨100, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 100 (by decide)))

theorem fz1_83_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨101, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 101 (by decide)))

theorem fz1_83_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨102, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 102 (by decide)))

theorem fz1_83_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨103, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 103 (by decide)))

theorem fz1_83_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨104, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 104 (by decide)))

theorem fz1_83_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨105, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 105 (by decide)))

theorem fz1_83_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨106, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 106 (by decide)))

theorem fz1_83_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨107, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 107 (by decide)))

theorem fz1_83_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨108, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 108 (by decide)))

theorem fz1_83_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨109, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 109 (by decide)))

theorem fz1_83_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨110, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 110 (by decide)))

theorem fz1_83_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨111, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 111 (by decide)))

theorem fz1_83_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨112, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 112 (by decide)))

theorem fz1_83_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨113, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 113 (by decide)))

theorem fz1_83_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨114, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 114 (by decide)))

theorem fz1_83_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK83)) = 0 :=
  repsFixedCard rK83 ⟨115, by decide⟩ R83 hpxR83 hcardq83
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_83) 115 (by decide)))

theorem fixz2_83 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK83) (retConj 2 (Q2.R83_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_83_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨1, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 1 (by decide)))

theorem fz2_83_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨2, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 2 (by decide)))

theorem fz2_83_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨3, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 3 (by decide)))

theorem fz2_83_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨5, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 5 (by decide)))

theorem fz2_83_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨6, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 6 (by decide)))

theorem fz2_83_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨7, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 7 (by decide)))

theorem fz2_83_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨8, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 8 (by decide)))

theorem fz2_83_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨9, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 9 (by decide)))

theorem fz2_83_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨11, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 11 (by decide)))

theorem fz2_83_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨13, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 13 (by decide)))

theorem fz2_83_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨14, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 14 (by decide)))

theorem fz2_83_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨15, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 15 (by decide)))

theorem fz2_83_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨16, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 16 (by decide)))

theorem fz2_83_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨17, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 17 (by decide)))

theorem fz2_83_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨18, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 18 (by decide)))

theorem fz2_83_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨19, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 19 (by decide)))

theorem fz2_83_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨20, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 20 (by decide)))

theorem fz2_83_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨21, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 21 (by decide)))

theorem fz2_83_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨23, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 23 (by decide)))

theorem fz2_83_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨24, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 24 (by decide)))

theorem fz2_83_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨25, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 25 (by decide)))

theorem fz2_83_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨26, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 26 (by decide)))

theorem fz2_83_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨27, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 27 (by decide)))

theorem fz2_83_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨28, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 28 (by decide)))

theorem fz2_83_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨29, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 29 (by decide)))

theorem fz2_83_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨30, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 30 (by decide)))

theorem fz2_83_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨31, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 31 (by decide)))

theorem fz2_83_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨32, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 32 (by decide)))

theorem fz2_83_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨33, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 33 (by decide)))

theorem fz2_83_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨34, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 34 (by decide)))

theorem fz2_83_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨35, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 35 (by decide)))

theorem fz2_83_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨36, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 36 (by decide)))

theorem fz2_83_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨37, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 37 (by decide)))

theorem fz2_83_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨38, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 38 (by decide)))

theorem fz2_83_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨39, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 39 (by decide)))

theorem fz2_83_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨40, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 40 (by decide)))

theorem fz2_83_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨41, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 41 (by decide)))

theorem fz2_83_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨42, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 42 (by decide)))

theorem fz2_83_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨43, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 43 (by decide)))

theorem fz2_83_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨44, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 44 (by decide)))

theorem fz2_83_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨45, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 45 (by decide)))

theorem fz2_83_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨46, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 46 (by decide)))

theorem fz2_83_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨47, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 47 (by decide)))

theorem fz2_83_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨48, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 48 (by decide)))

theorem fz2_83_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨49, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 49 (by decide)))

theorem fz2_83_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨50, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 50 (by decide)))

theorem fz2_83_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨51, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 51 (by decide)))

theorem fz2_83_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨52, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 52 (by decide)))

theorem fz2_83_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨54, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 54 (by decide)))

theorem fz2_83_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨55, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 55 (by decide)))

theorem fz2_83_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨56, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 56 (by decide)))

theorem fz2_83_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨57, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 57 (by decide)))

theorem fz2_83_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨58, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 58 (by decide)))

theorem fz2_83_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨59, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 59 (by decide)))

theorem fz2_83_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨60, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 60 (by decide)))

theorem fz2_83_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨61, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 61 (by decide)))

theorem fz2_83_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨62, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 62 (by decide)))

theorem fz2_83_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨63, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 63 (by decide)))

theorem fz2_83_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨64, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 64 (by decide)))

theorem fz2_83_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨65, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 65 (by decide)))

theorem fz2_83_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨66, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 66 (by decide)))

theorem fz2_83_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨67, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 67 (by decide)))

theorem fz2_83_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨68, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 68 (by decide)))

theorem fz2_83_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨69, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 69 (by decide)))

theorem fz2_83_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨70, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 70 (by decide)))

theorem fz2_83_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨71, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 71 (by decide)))

theorem fz2_83_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨72, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 72 (by decide)))

theorem fz2_83_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨73, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 73 (by decide)))

theorem fz2_83_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨74, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 74 (by decide)))

theorem fz2_83_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨75, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 75 (by decide)))

theorem fz2_83_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨76, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 76 (by decide)))

theorem fz2_83_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨77, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 77 (by decide)))

theorem fz2_83_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨78, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 78 (by decide)))

theorem fz2_83_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨79, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 79 (by decide)))

theorem fz2_83_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨80, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 80 (by decide)))

theorem fz2_83_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨81, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 81 (by decide)))

theorem fz2_83_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨82, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 82 (by decide)))

theorem fz2_83_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨84, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 84 (by decide)))

theorem fz2_83_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨85, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 85 (by decide)))

theorem fz2_83_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨86, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 86 (by decide)))

theorem fz2_83_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨87, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 87 (by decide)))

theorem fz2_83_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨88, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 88 (by decide)))

theorem fz2_83_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨89, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 89 (by decide)))

theorem fz2_83_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨90, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 90 (by decide)))

theorem fz2_83_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨91, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 91 (by decide)))

theorem fz2_83_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨92, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 92 (by decide)))

theorem fz2_83_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨93, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 93 (by decide)))

theorem fz2_83_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨94, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 94 (by decide)))

theorem fz2_83_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨95, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 95 (by decide)))

theorem fz2_83_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨96, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 96 (by decide)))

theorem fz2_83_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨97, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 97 (by decide)))

theorem fz2_83_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨98, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 98 (by decide)))

theorem fz2_83_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨99, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 99 (by decide)))

theorem fz2_83_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨100, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 100 (by decide)))

theorem fz2_83_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨101, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 101 (by decide)))

theorem fz2_83_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨102, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 102 (by decide)))

theorem fz2_83_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨103, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 103 (by decide)))

theorem fz2_83_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨104, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 104 (by decide)))

theorem fz2_83_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨105, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 105 (by decide)))

theorem fz2_83_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨106, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 106 (by decide)))

theorem fz2_83_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨107, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 107 (by decide)))

theorem fz2_83_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨108, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 108 (by decide)))

theorem fz2_83_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨109, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 109 (by decide)))

theorem fz2_83_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨110, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 110 (by decide)))

theorem fz2_83_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨111, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 111 (by decide)))

theorem fz2_83_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨112, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 112 (by decide)))

theorem fz2_83_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨113, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 113 (by decide)))

theorem fz2_83_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨114, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 114 (by decide)))

theorem fz2_83_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK83)) = 0 :=
  Q2.repsFixedCard2 rK83 ⟨115, by decide⟩ Q2.R83_2 Q2.hpxR83_2 Q2.hcardq83_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_83) 115 (by decide)))

theorem fixz1_84 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK84) (retConj 1 (R84 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_84_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨1, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 1 (by decide)))

theorem fz1_84_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨2, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 2 (by decide)))

theorem fz1_84_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨3, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 3 (by decide)))

theorem fz1_84_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨4, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 4 (by decide)))

theorem fz1_84_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨6, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 6 (by decide)))

theorem fz1_84_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨7, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 7 (by decide)))

theorem fz1_84_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨8, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 8 (by decide)))

theorem fz1_84_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨9, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 9 (by decide)))

theorem fz1_84_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨11, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 11 (by decide)))

theorem fz1_84_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨13, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 13 (by decide)))

theorem fz1_84_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨14, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 14 (by decide)))

theorem fz1_84_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨15, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 15 (by decide)))

theorem fz1_84_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨16, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 16 (by decide)))

theorem fz1_84_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨17, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 17 (by decide)))

theorem fz1_84_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨18, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 18 (by decide)))

theorem fz1_84_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨19, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 19 (by decide)))

theorem fz1_84_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨20, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 20 (by decide)))

theorem fz1_84_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨21, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 21 (by decide)))

theorem fz1_84_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨22, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 22 (by decide)))

theorem fz1_84_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨24, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 24 (by decide)))

theorem fz1_84_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨25, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 25 (by decide)))

theorem fz1_84_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨26, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 26 (by decide)))

theorem fz1_84_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨27, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 27 (by decide)))

theorem fz1_84_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨28, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 28 (by decide)))

theorem fz1_84_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨29, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 29 (by decide)))

theorem fz1_84_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨30, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 30 (by decide)))

theorem fz1_84_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨31, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 31 (by decide)))

theorem fz1_84_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨32, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 32 (by decide)))

theorem fz1_84_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨33, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 33 (by decide)))

theorem fz1_84_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨34, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 34 (by decide)))

theorem fz1_84_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨35, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 35 (by decide)))

theorem fz1_84_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨36, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 36 (by decide)))

theorem fz1_84_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨37, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 37 (by decide)))

theorem fz1_84_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨38, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 38 (by decide)))

theorem fz1_84_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨39, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 39 (by decide)))

theorem fz1_84_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨40, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 40 (by decide)))

theorem fz1_84_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨41, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 41 (by decide)))

theorem fz1_84_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨42, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 42 (by decide)))

theorem fz1_84_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨43, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 43 (by decide)))

theorem fz1_84_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨44, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 44 (by decide)))

theorem fz1_84_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨45, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 45 (by decide)))

theorem fz1_84_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨46, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 46 (by decide)))

theorem fz1_84_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨47, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 47 (by decide)))

theorem fz1_84_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨48, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 48 (by decide)))

theorem fz1_84_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨49, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 49 (by decide)))

theorem fz1_84_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨50, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 50 (by decide)))

theorem fz1_84_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨51, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 51 (by decide)))

theorem fz1_84_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨52, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 52 (by decide)))

theorem fz1_84_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨54, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 54 (by decide)))

theorem fz1_84_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨55, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 55 (by decide)))

theorem fz1_84_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨56, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 56 (by decide)))

theorem fz1_84_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨57, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 57 (by decide)))

theorem fz1_84_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨58, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 58 (by decide)))

theorem fz1_84_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨59, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 59 (by decide)))

theorem fz1_84_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨60, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 60 (by decide)))

theorem fz1_84_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨61, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 61 (by decide)))

theorem fz1_84_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨62, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 62 (by decide)))

theorem fz1_84_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨63, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 63 (by decide)))

theorem fz1_84_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨64, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 64 (by decide)))

theorem fz1_84_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨65, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 65 (by decide)))

theorem fz1_84_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨66, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 66 (by decide)))

theorem fz1_84_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨67, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 67 (by decide)))

theorem fz1_84_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨68, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 68 (by decide)))

theorem fz1_84_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨69, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 69 (by decide)))

theorem fz1_84_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨70, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 70 (by decide)))

theorem fz1_84_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨71, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 71 (by decide)))

theorem fz1_84_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨72, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 72 (by decide)))

theorem fz1_84_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨73, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 73 (by decide)))

theorem fz1_84_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨74, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 74 (by decide)))

theorem fz1_84_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨75, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 75 (by decide)))

theorem fz1_84_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨76, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 76 (by decide)))

theorem fz1_84_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨77, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 77 (by decide)))

theorem fz1_84_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨78, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 78 (by decide)))

theorem fz1_84_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨79, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 79 (by decide)))

theorem fz1_84_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨80, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 80 (by decide)))

theorem fz1_84_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨81, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 81 (by decide)))

theorem fz1_84_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨82, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 82 (by decide)))

theorem fz1_84_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨83, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 83 (by decide)))

theorem fz1_84_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨85, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 85 (by decide)))

theorem fz1_84_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨86, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 86 (by decide)))

theorem fz1_84_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨87, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 87 (by decide)))

theorem fz1_84_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨88, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 88 (by decide)))

theorem fz1_84_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨89, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 89 (by decide)))

theorem fz1_84_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨90, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 90 (by decide)))

theorem fz1_84_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨91, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 91 (by decide)))

theorem fz1_84_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨92, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 92 (by decide)))

theorem fz1_84_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨93, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 93 (by decide)))

theorem fz1_84_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨94, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 94 (by decide)))

theorem fz1_84_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨95, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 95 (by decide)))

theorem fz1_84_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨96, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 96 (by decide)))

theorem fz1_84_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨97, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 97 (by decide)))

theorem fz1_84_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨98, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 98 (by decide)))

theorem fz1_84_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨99, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 99 (by decide)))

theorem fz1_84_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨100, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 100 (by decide)))

theorem fz1_84_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨101, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 101 (by decide)))

theorem fz1_84_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨102, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 102 (by decide)))

theorem fz1_84_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨103, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 103 (by decide)))

theorem fz1_84_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨104, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 104 (by decide)))

theorem fz1_84_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨105, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 105 (by decide)))

theorem fz1_84_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨106, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 106 (by decide)))

theorem fz1_84_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨107, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 107 (by decide)))

theorem fz1_84_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨108, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 108 (by decide)))

theorem fz1_84_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨109, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 109 (by decide)))

theorem fz1_84_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨110, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 110 (by decide)))

theorem fz1_84_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨111, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 111 (by decide)))

theorem fz1_84_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨112, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 112 (by decide)))

theorem fz1_84_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨113, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 113 (by decide)))

theorem fz1_84_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨114, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 114 (by decide)))

theorem fz1_84_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK84)) = 0 :=
  repsFixedCard rK84 ⟨115, by decide⟩ R84 hpxR84 hcardq84
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_84) 115 (by decide)))

theorem fixz2_84 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK84) (retConj 2 (Q2.R84_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_84_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨1, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 1 (by decide)))

theorem fz2_84_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨2, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 2 (by decide)))

theorem fz2_84_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨3, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 3 (by decide)))

theorem fz2_84_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨4, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 4 (by decide)))

theorem fz2_84_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨6, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 6 (by decide)))

theorem fz2_84_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨7, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 7 (by decide)))

theorem fz2_84_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨8, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 8 (by decide)))

theorem fz2_84_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨9, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 9 (by decide)))

theorem fz2_84_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨11, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 11 (by decide)))

theorem fz2_84_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨13, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 13 (by decide)))

theorem fz2_84_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨14, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 14 (by decide)))

theorem fz2_84_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨15, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 15 (by decide)))

theorem fz2_84_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨16, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 16 (by decide)))

theorem fz2_84_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨17, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 17 (by decide)))

theorem fz2_84_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨18, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 18 (by decide)))

theorem fz2_84_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨19, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 19 (by decide)))

theorem fz2_84_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨20, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 20 (by decide)))

theorem fz2_84_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨21, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 21 (by decide)))

theorem fz2_84_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨22, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 22 (by decide)))

theorem fz2_84_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨24, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 24 (by decide)))

theorem fz2_84_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨25, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 25 (by decide)))

theorem fz2_84_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨26, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 26 (by decide)))

theorem fz2_84_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨27, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 27 (by decide)))

theorem fz2_84_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨28, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 28 (by decide)))

theorem fz2_84_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨29, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 29 (by decide)))

theorem fz2_84_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨30, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 30 (by decide)))

theorem fz2_84_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨31, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 31 (by decide)))

theorem fz2_84_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨32, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 32 (by decide)))

theorem fz2_84_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨33, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 33 (by decide)))

theorem fz2_84_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨34, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 34 (by decide)))

theorem fz2_84_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨35, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 35 (by decide)))

theorem fz2_84_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨36, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 36 (by decide)))

theorem fz2_84_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨37, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 37 (by decide)))

theorem fz2_84_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨38, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 38 (by decide)))

theorem fz2_84_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨39, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 39 (by decide)))

theorem fz2_84_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨40, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 40 (by decide)))

theorem fz2_84_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨41, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 41 (by decide)))

theorem fz2_84_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨42, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 42 (by decide)))

theorem fz2_84_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨43, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 43 (by decide)))

theorem fz2_84_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨44, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 44 (by decide)))

theorem fz2_84_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨45, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 45 (by decide)))

theorem fz2_84_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨46, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 46 (by decide)))

theorem fz2_84_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨47, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 47 (by decide)))

theorem fz2_84_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨48, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 48 (by decide)))

theorem fz2_84_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨49, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 49 (by decide)))

theorem fz2_84_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨50, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 50 (by decide)))

theorem fz2_84_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨51, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 51 (by decide)))

theorem fz2_84_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨52, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 52 (by decide)))

theorem fz2_84_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨54, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 54 (by decide)))

theorem fz2_84_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨55, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 55 (by decide)))

theorem fz2_84_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨56, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 56 (by decide)))

theorem fz2_84_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨57, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 57 (by decide)))

theorem fz2_84_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨58, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 58 (by decide)))

theorem fz2_84_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨59, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 59 (by decide)))

theorem fz2_84_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨60, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 60 (by decide)))

theorem fz2_84_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨61, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 61 (by decide)))

theorem fz2_84_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨62, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 62 (by decide)))

theorem fz2_84_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨63, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 63 (by decide)))

theorem fz2_84_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨64, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 64 (by decide)))

theorem fz2_84_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨65, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 65 (by decide)))

theorem fz2_84_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨66, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 66 (by decide)))

theorem fz2_84_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨67, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 67 (by decide)))

theorem fz2_84_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨68, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 68 (by decide)))

theorem fz2_84_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨69, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 69 (by decide)))

theorem fz2_84_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨70, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 70 (by decide)))

theorem fz2_84_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨71, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 71 (by decide)))

theorem fz2_84_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨72, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 72 (by decide)))

theorem fz2_84_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨73, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 73 (by decide)))

theorem fz2_84_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨74, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 74 (by decide)))

theorem fz2_84_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨75, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 75 (by decide)))

theorem fz2_84_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨76, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 76 (by decide)))

theorem fz2_84_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨77, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 77 (by decide)))

theorem fz2_84_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨78, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 78 (by decide)))

theorem fz2_84_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨79, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 79 (by decide)))

theorem fz2_84_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨80, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 80 (by decide)))

theorem fz2_84_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨81, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 81 (by decide)))

theorem fz2_84_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨82, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 82 (by decide)))

theorem fz2_84_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨83, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 83 (by decide)))

theorem fz2_84_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨85, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 85 (by decide)))

theorem fz2_84_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨86, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 86 (by decide)))

theorem fz2_84_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨87, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 87 (by decide)))

theorem fz2_84_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨88, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 88 (by decide)))

theorem fz2_84_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨89, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 89 (by decide)))

theorem fz2_84_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨90, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 90 (by decide)))

theorem fz2_84_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨91, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 91 (by decide)))

theorem fz2_84_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨92, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 92 (by decide)))

theorem fz2_84_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨93, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 93 (by decide)))

theorem fz2_84_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨94, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 94 (by decide)))

theorem fz2_84_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨95, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 95 (by decide)))

theorem fz2_84_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨96, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 96 (by decide)))

theorem fz2_84_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨97, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 97 (by decide)))

theorem fz2_84_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨98, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 98 (by decide)))

theorem fz2_84_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨99, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 99 (by decide)))

theorem fz2_84_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨100, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 100 (by decide)))

theorem fz2_84_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨101, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 101 (by decide)))

theorem fz2_84_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨102, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 102 (by decide)))

theorem fz2_84_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨103, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 103 (by decide)))

theorem fz2_84_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨104, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 104 (by decide)))

theorem fz2_84_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨105, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 105 (by decide)))

theorem fz2_84_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨106, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 106 (by decide)))

theorem fz2_84_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨107, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 107 (by decide)))

theorem fz2_84_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨108, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 108 (by decide)))

theorem fz2_84_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨109, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 109 (by decide)))

theorem fz2_84_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨110, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 110 (by decide)))

theorem fz2_84_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨111, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 111 (by decide)))

theorem fz2_84_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨112, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 112 (by decide)))

theorem fz2_84_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨113, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 113 (by decide)))

theorem fz2_84_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨114, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 114 (by decide)))

theorem fz2_84_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK84)) = 0 :=
  Q2.repsFixedCard2 rK84 ⟨115, by decide⟩ Q2.R84_2 Q2.hpxR84_2 Q2.hcardq84_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_84) 115 (by decide)))

end LeanDring.P5Presentation
