/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C016

/-!
# Species-table cells, off-support emptiness certificates, chunk 60

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

theorem fixz1_67 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK67) (retConj 1 (R67 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_67_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨1, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 1 (by decide)))

theorem fz1_67_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨2, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 2 (by decide)))

theorem fz1_67_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨3, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 3 (by decide)))

theorem fz1_67_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨4, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 4 (by decide)))

theorem fz1_67_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨5, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 5 (by decide)))

theorem fz1_67_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨6, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 6 (by decide)))

theorem fz1_67_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨8, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 8 (by decide)))

theorem fz1_67_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨9, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 9 (by decide)))

theorem fz1_67_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨10, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 10 (by decide)))

theorem fz1_67_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨11, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 11 (by decide)))

theorem fz1_67_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨13, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 13 (by decide)))

theorem fz1_67_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨14, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 14 (by decide)))

theorem fz1_67_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨15, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 15 (by decide)))

theorem fz1_67_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨16, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 16 (by decide)))

theorem fz1_67_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨17, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 17 (by decide)))

theorem fz1_67_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨18, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 18 (by decide)))

theorem fz1_67_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨19, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 19 (by decide)))

theorem fz1_67_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨20, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 20 (by decide)))

theorem fz1_67_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨21, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 21 (by decide)))

theorem fz1_67_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨22, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 22 (by decide)))

theorem fz1_67_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨23, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 23 (by decide)))

theorem fz1_67_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨24, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 24 (by decide)))

theorem fz1_67_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨26, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 26 (by decide)))

theorem fz1_67_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨27, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 27 (by decide)))

theorem fz1_67_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨28, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 28 (by decide)))

theorem fz1_67_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨29, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 29 (by decide)))

theorem fz1_67_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨31, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 31 (by decide)))

theorem fz1_67_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨32, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 32 (by decide)))

theorem fz1_67_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨33, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 33 (by decide)))

theorem fz1_67_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨34, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 34 (by decide)))

theorem fz1_67_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨36, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 36 (by decide)))

theorem fz1_67_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨37, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 37 (by decide)))

theorem fz1_67_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨38, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 38 (by decide)))

theorem fz1_67_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨39, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 39 (by decide)))

theorem fz1_67_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨41, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 41 (by decide)))

theorem fz1_67_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨42, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 42 (by decide)))

theorem fz1_67_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨43, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 43 (by decide)))

theorem fz1_67_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨44, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 44 (by decide)))

theorem fz1_67_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨46, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 46 (by decide)))

theorem fz1_67_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨47, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 47 (by decide)))

theorem fz1_67_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨48, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 48 (by decide)))

theorem fz1_67_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨49, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 49 (by decide)))

theorem fz1_67_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨51, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 51 (by decide)))

theorem fz1_67_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨52, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 52 (by decide)))

theorem fz1_67_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨53, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 53 (by decide)))

theorem fz1_67_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨54, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 54 (by decide)))

theorem fz1_67_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨55, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 55 (by decide)))

theorem fz1_67_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨56, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 56 (by decide)))

theorem fz1_67_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨57, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 57 (by decide)))

theorem fz1_67_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨58, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 58 (by decide)))

theorem fz1_67_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨59, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 59 (by decide)))

theorem fz1_67_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨60, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 60 (by decide)))

theorem fz1_67_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨61, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 61 (by decide)))

theorem fz1_67_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨62, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 62 (by decide)))

theorem fz1_67_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨63, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 63 (by decide)))

theorem fz1_67_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨64, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 64 (by decide)))

theorem fz1_67_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨65, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 65 (by decide)))

theorem fz1_67_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨66, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 66 (by decide)))

theorem fz1_67_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨68, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 68 (by decide)))

theorem fz1_67_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨69, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 69 (by decide)))

theorem fz1_67_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨70, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 70 (by decide)))

theorem fz1_67_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨71, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 71 (by decide)))

theorem fz1_67_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨72, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 72 (by decide)))

theorem fz1_67_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨73, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 73 (by decide)))

theorem fz1_67_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨74, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 74 (by decide)))

theorem fz1_67_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨75, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 75 (by decide)))

theorem fz1_67_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨76, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 76 (by decide)))

theorem fz1_67_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨77, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 77 (by decide)))

theorem fz1_67_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨78, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 78 (by decide)))

theorem fz1_67_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨79, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 79 (by decide)))

theorem fz1_67_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨80, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 80 (by decide)))

theorem fz1_67_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨81, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 81 (by decide)))

theorem fz1_67_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨82, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 82 (by decide)))

theorem fz1_67_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨83, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 83 (by decide)))

theorem fz1_67_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨84, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 84 (by decide)))

theorem fz1_67_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨85, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 85 (by decide)))

theorem fz1_67_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨86, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 86 (by decide)))

theorem fz1_67_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨87, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 87 (by decide)))

theorem fz1_67_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨88, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 88 (by decide)))

theorem fz1_67_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨89, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 89 (by decide)))

theorem fz1_67_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨90, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 90 (by decide)))

theorem fz1_67_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨91, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 91 (by decide)))

theorem fz1_67_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨92, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 92 (by decide)))

theorem fz1_67_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨93, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 93 (by decide)))

theorem fz1_67_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨94, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 94 (by decide)))

theorem fz1_67_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨95, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 95 (by decide)))

theorem fz1_67_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨96, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 96 (by decide)))

theorem fz1_67_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨97, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 97 (by decide)))

theorem fz1_67_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨98, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 98 (by decide)))

theorem fz1_67_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨99, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 99 (by decide)))

theorem fz1_67_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨100, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 100 (by decide)))

theorem fz1_67_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨101, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 101 (by decide)))

theorem fz1_67_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨102, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 102 (by decide)))

theorem fz1_67_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨103, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 103 (by decide)))

theorem fz1_67_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨104, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 104 (by decide)))

theorem fz1_67_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨105, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 105 (by decide)))

theorem fz1_67_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨106, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 106 (by decide)))

theorem fz1_67_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨107, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 107 (by decide)))

theorem fz1_67_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨108, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 108 (by decide)))

theorem fz1_67_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨109, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 109 (by decide)))

theorem fz1_67_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨110, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 110 (by decide)))

theorem fz1_67_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨111, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 111 (by decide)))

theorem fz1_67_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨112, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 112 (by decide)))

theorem fz1_67_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨113, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 113 (by decide)))

theorem fz1_67_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨114, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 114 (by decide)))

theorem fz1_67_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK67)) = 0 :=
  repsFixedCard rK67 ⟨115, by decide⟩ R67 hpxR67 hcardq67
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_67) 115 (by decide)))

theorem fixz2_67 : ([1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK67) (retConj 2 (Q2.R67_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_67_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨1, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 1 (by decide)))

theorem fz2_67_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨2, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 2 (by decide)))

theorem fz2_67_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨3, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 3 (by decide)))

theorem fz2_67_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨4, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 4 (by decide)))

theorem fz2_67_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨5, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 5 (by decide)))

theorem fz2_67_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨6, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 6 (by decide)))

theorem fz2_67_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨8, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 8 (by decide)))

theorem fz2_67_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨9, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 9 (by decide)))

theorem fz2_67_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨10, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 10 (by decide)))

theorem fz2_67_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨11, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 11 (by decide)))

theorem fz2_67_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨13, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 13 (by decide)))

theorem fz2_67_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨14, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 14 (by decide)))

theorem fz2_67_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨15, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 15 (by decide)))

theorem fz2_67_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨16, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 16 (by decide)))

theorem fz2_67_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨17, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 17 (by decide)))

theorem fz2_67_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨18, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 18 (by decide)))

theorem fz2_67_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨19, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 19 (by decide)))

theorem fz2_67_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨20, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 20 (by decide)))

theorem fz2_67_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨21, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 21 (by decide)))

theorem fz2_67_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨22, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 22 (by decide)))

theorem fz2_67_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨23, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 23 (by decide)))

theorem fz2_67_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨24, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 24 (by decide)))

theorem fz2_67_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨26, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 26 (by decide)))

theorem fz2_67_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨27, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 27 (by decide)))

theorem fz2_67_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨28, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 28 (by decide)))

theorem fz2_67_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨29, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 29 (by decide)))

theorem fz2_67_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨31, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 31 (by decide)))

theorem fz2_67_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨32, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 32 (by decide)))

theorem fz2_67_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨33, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 33 (by decide)))

theorem fz2_67_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨34, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 34 (by decide)))

theorem fz2_67_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨36, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 36 (by decide)))

theorem fz2_67_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨37, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 37 (by decide)))

theorem fz2_67_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨38, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 38 (by decide)))

theorem fz2_67_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨39, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 39 (by decide)))

theorem fz2_67_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨41, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 41 (by decide)))

theorem fz2_67_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨42, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 42 (by decide)))

theorem fz2_67_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨43, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 43 (by decide)))

theorem fz2_67_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨44, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 44 (by decide)))

theorem fz2_67_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨46, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 46 (by decide)))

theorem fz2_67_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨47, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 47 (by decide)))

theorem fz2_67_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨48, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 48 (by decide)))

theorem fz2_67_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨49, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 49 (by decide)))

theorem fz2_67_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨51, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 51 (by decide)))

theorem fz2_67_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨52, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 52 (by decide)))

theorem fz2_67_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨53, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 53 (by decide)))

theorem fz2_67_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨54, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 54 (by decide)))

theorem fz2_67_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨55, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 55 (by decide)))

theorem fz2_67_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨56, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 56 (by decide)))

theorem fz2_67_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨57, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 57 (by decide)))

theorem fz2_67_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨58, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 58 (by decide)))

theorem fz2_67_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨59, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 59 (by decide)))

theorem fz2_67_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨60, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 60 (by decide)))

theorem fz2_67_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨61, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 61 (by decide)))

theorem fz2_67_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨62, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 62 (by decide)))

theorem fz2_67_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨63, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 63 (by decide)))

theorem fz2_67_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨64, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 64 (by decide)))

theorem fz2_67_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨65, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 65 (by decide)))

theorem fz2_67_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨66, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 66 (by decide)))

theorem fz2_67_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨68, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 68 (by decide)))

theorem fz2_67_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨69, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 69 (by decide)))

theorem fz2_67_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨70, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 70 (by decide)))

theorem fz2_67_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨71, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 71 (by decide)))

theorem fz2_67_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨72, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 72 (by decide)))

theorem fz2_67_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨73, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 73 (by decide)))

theorem fz2_67_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨74, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 74 (by decide)))

theorem fz2_67_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨75, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 75 (by decide)))

theorem fz2_67_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨76, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 76 (by decide)))

theorem fz2_67_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨77, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 77 (by decide)))

theorem fz2_67_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨78, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 78 (by decide)))

theorem fz2_67_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨79, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 79 (by decide)))

theorem fz2_67_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨80, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 80 (by decide)))

theorem fz2_67_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨81, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 81 (by decide)))

theorem fz2_67_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨82, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 82 (by decide)))

theorem fz2_67_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨83, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 83 (by decide)))

theorem fz2_67_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨84, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 84 (by decide)))

theorem fz2_67_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨85, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 85 (by decide)))

theorem fz2_67_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨86, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 86 (by decide)))

theorem fz2_67_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨87, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 87 (by decide)))

theorem fz2_67_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨88, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 88 (by decide)))

theorem fz2_67_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨89, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 89 (by decide)))

theorem fz2_67_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨90, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 90 (by decide)))

theorem fz2_67_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨91, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 91 (by decide)))

theorem fz2_67_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨92, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 92 (by decide)))

theorem fz2_67_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨93, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 93 (by decide)))

theorem fz2_67_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨94, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 94 (by decide)))

theorem fz2_67_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨95, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 95 (by decide)))

theorem fz2_67_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨96, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 96 (by decide)))

theorem fz2_67_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨97, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 97 (by decide)))

theorem fz2_67_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨98, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 98 (by decide)))

theorem fz2_67_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨99, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 99 (by decide)))

theorem fz2_67_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨100, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 100 (by decide)))

theorem fz2_67_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨101, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 101 (by decide)))

theorem fz2_67_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨102, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 102 (by decide)))

theorem fz2_67_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨103, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 103 (by decide)))

theorem fz2_67_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨104, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 104 (by decide)))

theorem fz2_67_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨105, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 105 (by decide)))

theorem fz2_67_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨106, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 106 (by decide)))

theorem fz2_67_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨107, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 107 (by decide)))

theorem fz2_67_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨108, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 108 (by decide)))

theorem fz2_67_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨109, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 109 (by decide)))

theorem fz2_67_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨110, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 110 (by decide)))

theorem fz2_67_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨111, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 111 (by decide)))

theorem fz2_67_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨112, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 112 (by decide)))

theorem fz2_67_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨113, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 113 (by decide)))

theorem fz2_67_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨114, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 114 (by decide)))

theorem fz2_67_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK67)) = 0 :=
  Q2.repsFixedCard2 rK67 ⟨115, by decide⟩ Q2.R67_2 Q2.hpxR67_2 Q2.hcardq67_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_67) 115 (by decide)))

theorem fixz1_68 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK68) (retConj 1 (R68 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_68_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨1, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 1 (by decide)))

theorem fz1_68_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨2, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 2 (by decide)))

theorem fz1_68_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨3, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 3 (by decide)))

theorem fz1_68_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨4, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 4 (by decide)))

theorem fz1_68_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨5, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 5 (by decide)))

theorem fz1_68_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨7, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 7 (by decide)))

theorem fz1_68_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨8, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 8 (by decide)))

theorem fz1_68_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨9, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 9 (by decide)))

theorem fz1_68_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨10, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 10 (by decide)))

theorem fz1_68_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨11, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 11 (by decide)))

theorem fz1_68_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨13, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 13 (by decide)))

theorem fz1_68_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨14, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 14 (by decide)))

theorem fz1_68_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨15, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 15 (by decide)))

theorem fz1_68_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨16, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 16 (by decide)))

theorem fz1_68_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨17, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 17 (by decide)))

theorem fz1_68_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨18, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 18 (by decide)))

theorem fz1_68_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨19, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 19 (by decide)))

theorem fz1_68_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨20, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 20 (by decide)))

theorem fz1_68_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨21, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 21 (by decide)))

theorem fz1_68_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨22, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 22 (by decide)))

theorem fz1_68_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨23, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 23 (by decide)))

theorem fz1_68_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨25, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 25 (by decide)))

theorem fz1_68_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨26, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 26 (by decide)))

theorem fz1_68_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨27, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 27 (by decide)))

theorem fz1_68_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨28, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 28 (by decide)))

theorem fz1_68_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨29, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 29 (by decide)))

theorem fz1_68_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨31, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 31 (by decide)))

theorem fz1_68_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨32, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 32 (by decide)))

theorem fz1_68_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨33, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 33 (by decide)))

theorem fz1_68_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨34, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 34 (by decide)))

theorem fz1_68_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨36, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 36 (by decide)))

theorem fz1_68_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨37, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 37 (by decide)))

theorem fz1_68_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨38, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 38 (by decide)))

theorem fz1_68_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨39, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 39 (by decide)))

theorem fz1_68_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨41, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 41 (by decide)))

theorem fz1_68_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨42, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 42 (by decide)))

theorem fz1_68_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨43, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 43 (by decide)))

theorem fz1_68_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨44, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 44 (by decide)))

theorem fz1_68_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨46, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 46 (by decide)))

theorem fz1_68_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨47, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 47 (by decide)))

theorem fz1_68_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨48, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 48 (by decide)))

theorem fz1_68_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨49, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 49 (by decide)))

theorem fz1_68_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨51, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 51 (by decide)))

theorem fz1_68_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨52, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 52 (by decide)))

theorem fz1_68_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨53, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 53 (by decide)))

theorem fz1_68_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨54, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 54 (by decide)))

theorem fz1_68_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨55, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 55 (by decide)))

theorem fz1_68_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨56, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 56 (by decide)))

theorem fz1_68_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨57, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 57 (by decide)))

theorem fz1_68_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨58, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 58 (by decide)))

theorem fz1_68_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨59, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 59 (by decide)))

theorem fz1_68_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨60, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 60 (by decide)))

theorem fz1_68_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨61, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 61 (by decide)))

theorem fz1_68_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨62, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 62 (by decide)))

theorem fz1_68_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨63, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 63 (by decide)))

theorem fz1_68_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨64, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 64 (by decide)))

theorem fz1_68_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨65, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 65 (by decide)))

theorem fz1_68_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨66, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 66 (by decide)))

theorem fz1_68_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨67, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 67 (by decide)))

theorem fz1_68_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨69, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 69 (by decide)))

theorem fz1_68_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨70, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 70 (by decide)))

theorem fz1_68_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨71, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 71 (by decide)))

theorem fz1_68_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨72, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 72 (by decide)))

theorem fz1_68_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨73, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 73 (by decide)))

theorem fz1_68_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨74, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 74 (by decide)))

theorem fz1_68_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨75, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 75 (by decide)))

theorem fz1_68_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨76, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 76 (by decide)))

theorem fz1_68_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨77, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 77 (by decide)))

theorem fz1_68_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨78, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 78 (by decide)))

theorem fz1_68_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨79, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 79 (by decide)))

theorem fz1_68_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨80, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 80 (by decide)))

theorem fz1_68_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨81, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 81 (by decide)))

theorem fz1_68_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨82, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 82 (by decide)))

theorem fz1_68_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨83, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 83 (by decide)))

theorem fz1_68_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨84, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 84 (by decide)))

theorem fz1_68_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨85, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 85 (by decide)))

theorem fz1_68_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨86, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 86 (by decide)))

theorem fz1_68_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨87, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 87 (by decide)))

theorem fz1_68_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨88, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 88 (by decide)))

theorem fz1_68_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨89, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 89 (by decide)))

theorem fz1_68_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨90, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 90 (by decide)))

theorem fz1_68_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨91, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 91 (by decide)))

theorem fz1_68_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨92, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 92 (by decide)))

theorem fz1_68_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨93, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 93 (by decide)))

theorem fz1_68_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨94, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 94 (by decide)))

theorem fz1_68_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨95, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 95 (by decide)))

theorem fz1_68_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨96, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 96 (by decide)))

theorem fz1_68_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨97, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 97 (by decide)))

theorem fz1_68_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨98, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 98 (by decide)))

theorem fz1_68_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨99, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 99 (by decide)))

theorem fz1_68_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨100, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 100 (by decide)))

theorem fz1_68_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨101, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 101 (by decide)))

theorem fz1_68_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨102, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 102 (by decide)))

theorem fz1_68_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨103, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 103 (by decide)))

theorem fz1_68_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨104, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 104 (by decide)))

theorem fz1_68_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨105, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 105 (by decide)))

theorem fz1_68_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨106, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 106 (by decide)))

theorem fz1_68_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨107, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 107 (by decide)))

theorem fz1_68_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨108, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 108 (by decide)))

theorem fz1_68_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨109, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 109 (by decide)))

theorem fz1_68_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨110, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 110 (by decide)))

theorem fz1_68_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨111, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 111 (by decide)))

theorem fz1_68_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨112, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 112 (by decide)))

theorem fz1_68_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨113, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 113 (by decide)))

theorem fz1_68_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨114, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 114 (by decide)))

theorem fz1_68_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK68)) = 0 :=
  repsFixedCard rK68 ⟨115, by decide⟩ R68 hpxR68 hcardq68
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_68) 115 (by decide)))

theorem fixz2_68 : ([1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK68) (retConj 2 (Q2.R68_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_68_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨1, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 1 (by decide)))

theorem fz2_68_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨2, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 2 (by decide)))

theorem fz2_68_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨3, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 3 (by decide)))

theorem fz2_68_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨4, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 4 (by decide)))

theorem fz2_68_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨5, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 5 (by decide)))

theorem fz2_68_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨7, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 7 (by decide)))

theorem fz2_68_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨8, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 8 (by decide)))

theorem fz2_68_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨9, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 9 (by decide)))

theorem fz2_68_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨10, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 10 (by decide)))

theorem fz2_68_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨11, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 11 (by decide)))

theorem fz2_68_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨13, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 13 (by decide)))

theorem fz2_68_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨14, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 14 (by decide)))

theorem fz2_68_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨15, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 15 (by decide)))

theorem fz2_68_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨16, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 16 (by decide)))

theorem fz2_68_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨17, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 17 (by decide)))

theorem fz2_68_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨18, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 18 (by decide)))

theorem fz2_68_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨19, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 19 (by decide)))

theorem fz2_68_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨20, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 20 (by decide)))

theorem fz2_68_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨21, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 21 (by decide)))

theorem fz2_68_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨22, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 22 (by decide)))

theorem fz2_68_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨23, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 23 (by decide)))

theorem fz2_68_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨25, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 25 (by decide)))

theorem fz2_68_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨26, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 26 (by decide)))

theorem fz2_68_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨27, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 27 (by decide)))

theorem fz2_68_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨28, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 28 (by decide)))

theorem fz2_68_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨29, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 29 (by decide)))

theorem fz2_68_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨31, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 31 (by decide)))

theorem fz2_68_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨32, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 32 (by decide)))

theorem fz2_68_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨33, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 33 (by decide)))

theorem fz2_68_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨34, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 34 (by decide)))

theorem fz2_68_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨36, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 36 (by decide)))

theorem fz2_68_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨37, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 37 (by decide)))

theorem fz2_68_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨38, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 38 (by decide)))

theorem fz2_68_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨39, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 39 (by decide)))

theorem fz2_68_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨41, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 41 (by decide)))

theorem fz2_68_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨42, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 42 (by decide)))

theorem fz2_68_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨43, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 43 (by decide)))

theorem fz2_68_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨44, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 44 (by decide)))

theorem fz2_68_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨46, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 46 (by decide)))

theorem fz2_68_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨47, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 47 (by decide)))

theorem fz2_68_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨48, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 48 (by decide)))

theorem fz2_68_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨49, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 49 (by decide)))

theorem fz2_68_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨51, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 51 (by decide)))

theorem fz2_68_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨52, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 52 (by decide)))

theorem fz2_68_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨53, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 53 (by decide)))

theorem fz2_68_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨54, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 54 (by decide)))

theorem fz2_68_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨55, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 55 (by decide)))

theorem fz2_68_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨56, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 56 (by decide)))

theorem fz2_68_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨57, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 57 (by decide)))

theorem fz2_68_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨58, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 58 (by decide)))

theorem fz2_68_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨59, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 59 (by decide)))

theorem fz2_68_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨60, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 60 (by decide)))

theorem fz2_68_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨61, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 61 (by decide)))

theorem fz2_68_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨62, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 62 (by decide)))

theorem fz2_68_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨63, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 63 (by decide)))

theorem fz2_68_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨64, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 64 (by decide)))

theorem fz2_68_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨65, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 65 (by decide)))

theorem fz2_68_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨66, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 66 (by decide)))

theorem fz2_68_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨67, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 67 (by decide)))

theorem fz2_68_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨69, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 69 (by decide)))

theorem fz2_68_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨70, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 70 (by decide)))

theorem fz2_68_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨71, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 71 (by decide)))

theorem fz2_68_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨72, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 72 (by decide)))

theorem fz2_68_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨73, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 73 (by decide)))

theorem fz2_68_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨74, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 74 (by decide)))

theorem fz2_68_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨75, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 75 (by decide)))

theorem fz2_68_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨76, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 76 (by decide)))

theorem fz2_68_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨77, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 77 (by decide)))

theorem fz2_68_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨78, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 78 (by decide)))

theorem fz2_68_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨79, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 79 (by decide)))

theorem fz2_68_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨80, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 80 (by decide)))

theorem fz2_68_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨81, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 81 (by decide)))

theorem fz2_68_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨82, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 82 (by decide)))

theorem fz2_68_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨83, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 83 (by decide)))

theorem fz2_68_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨84, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 84 (by decide)))

theorem fz2_68_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨85, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 85 (by decide)))

theorem fz2_68_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨86, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 86 (by decide)))

theorem fz2_68_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨87, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 87 (by decide)))

theorem fz2_68_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨88, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 88 (by decide)))

theorem fz2_68_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨89, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 89 (by decide)))

theorem fz2_68_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨90, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 90 (by decide)))

theorem fz2_68_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨91, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 91 (by decide)))

theorem fz2_68_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨92, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 92 (by decide)))

theorem fz2_68_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨93, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 93 (by decide)))

theorem fz2_68_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨94, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 94 (by decide)))

theorem fz2_68_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨95, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 95 (by decide)))

theorem fz2_68_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨96, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 96 (by decide)))

theorem fz2_68_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨97, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 97 (by decide)))

theorem fz2_68_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨98, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 98 (by decide)))

theorem fz2_68_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨99, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 99 (by decide)))

theorem fz2_68_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨100, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 100 (by decide)))

theorem fz2_68_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨101, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 101 (by decide)))

theorem fz2_68_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨102, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 102 (by decide)))

theorem fz2_68_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨103, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 103 (by decide)))

theorem fz2_68_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨104, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 104 (by decide)))

theorem fz2_68_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨105, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 105 (by decide)))

theorem fz2_68_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨106, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 106 (by decide)))

theorem fz2_68_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨107, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 107 (by decide)))

theorem fz2_68_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨108, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 108 (by decide)))

theorem fz2_68_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨109, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 109 (by decide)))

theorem fz2_68_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨110, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 110 (by decide)))

theorem fz2_68_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨111, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 111 (by decide)))

theorem fz2_68_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨112, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 112 (by decide)))

theorem fz2_68_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨113, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 113 (by decide)))

theorem fz2_68_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨114, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 114 (by decide)))

theorem fz2_68_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK68)) = 0 :=
  Q2.repsFixedCard2 rK68 ⟨115, by decide⟩ Q2.R68_2 Q2.hpxR68_2 Q2.hcardq68_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_68) 115 (by decide)))

end LeanDring.P5Presentation
