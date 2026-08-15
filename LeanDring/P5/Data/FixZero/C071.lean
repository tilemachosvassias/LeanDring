/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C020
import LeanDring.P5.Data.EntryK.C021

/-!
# Species-table cells, off-support emptiness certificates, chunk 70

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

theorem fixz1_87 : ([1, 6, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK87) (retConj 1 (R87 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_87_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨1, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 1 (by decide)))

theorem fz1_87_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨6, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 6 (by decide)))

theorem fz1_87_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨8, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 8 (by decide)))

theorem fz1_87_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨9, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 9 (by decide)))

theorem fz1_87_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨10, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 10 (by decide)))

theorem fz1_87_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨13, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 13 (by decide)))

theorem fz1_87_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨14, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 14 (by decide)))

theorem fz1_87_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨15, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 15 (by decide)))

theorem fz1_87_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨16, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 16 (by decide)))

theorem fz1_87_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨17, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 17 (by decide)))

theorem fz1_87_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨18, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 18 (by decide)))

theorem fz1_87_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨19, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 19 (by decide)))

theorem fz1_87_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨24, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 24 (by decide)))

theorem fz1_87_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨26, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 26 (by decide)))

theorem fz1_87_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨27, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 27 (by decide)))

theorem fz1_87_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨28, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 28 (by decide)))

theorem fz1_87_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨29, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 29 (by decide)))

theorem fz1_87_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨30, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 30 (by decide)))

theorem fz1_87_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨31, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 31 (by decide)))

theorem fz1_87_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨32, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 32 (by decide)))

theorem fz1_87_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨33, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 33 (by decide)))

theorem fz1_87_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨34, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 34 (by decide)))

theorem fz1_87_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨35, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 35 (by decide)))

theorem fz1_87_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨36, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 36 (by decide)))

theorem fz1_87_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨37, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 37 (by decide)))

theorem fz1_87_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨38, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 38 (by decide)))

theorem fz1_87_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨39, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 39 (by decide)))

theorem fz1_87_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨40, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 40 (by decide)))

theorem fz1_87_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨41, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 41 (by decide)))

theorem fz1_87_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨42, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 42 (by decide)))

theorem fz1_87_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨43, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 43 (by decide)))

theorem fz1_87_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨44, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 44 (by decide)))

theorem fz1_87_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨45, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 45 (by decide)))

theorem fz1_87_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨46, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 46 (by decide)))

theorem fz1_87_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨47, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 47 (by decide)))

theorem fz1_87_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨48, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 48 (by decide)))

theorem fz1_87_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨49, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 49 (by decide)))

theorem fz1_87_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨50, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 50 (by decide)))

theorem fz1_87_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨51, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 51 (by decide)))

theorem fz1_87_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨52, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 52 (by decide)))

theorem fz1_87_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨53, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 53 (by decide)))

theorem fz1_87_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨55, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 55 (by decide)))

theorem fz1_87_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨56, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 56 (by decide)))

theorem fz1_87_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨57, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 57 (by decide)))

theorem fz1_87_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨58, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 58 (by decide)))

theorem fz1_87_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨59, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 59 (by decide)))

theorem fz1_87_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨60, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 60 (by decide)))

theorem fz1_87_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨61, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 61 (by decide)))

theorem fz1_87_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨62, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 62 (by decide)))

theorem fz1_87_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨63, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 63 (by decide)))

theorem fz1_87_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨64, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 64 (by decide)))

theorem fz1_87_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨65, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 65 (by decide)))

theorem fz1_87_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨66, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 66 (by decide)))

theorem fz1_87_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨67, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 67 (by decide)))

theorem fz1_87_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨68, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 68 (by decide)))

theorem fz1_87_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨69, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 69 (by decide)))

theorem fz1_87_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨70, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 70 (by decide)))

theorem fz1_87_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨71, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 71 (by decide)))

theorem fz1_87_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨72, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 72 (by decide)))

theorem fz1_87_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨73, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 73 (by decide)))

theorem fz1_87_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨74, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 74 (by decide)))

theorem fz1_87_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨75, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 75 (by decide)))

theorem fz1_87_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨76, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 76 (by decide)))

theorem fz1_87_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨77, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 77 (by decide)))

theorem fz1_87_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨78, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 78 (by decide)))

theorem fz1_87_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨79, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 79 (by decide)))

theorem fz1_87_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨80, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 80 (by decide)))

theorem fz1_87_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨81, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 81 (by decide)))

theorem fz1_87_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨82, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 82 (by decide)))

theorem fz1_87_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨83, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 83 (by decide)))

theorem fz1_87_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨84, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 84 (by decide)))

theorem fz1_87_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨85, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 85 (by decide)))

theorem fz1_87_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨86, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 86 (by decide)))

theorem fz1_87_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨88, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 88 (by decide)))

theorem fz1_87_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨89, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 89 (by decide)))

theorem fz1_87_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨90, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 90 (by decide)))

theorem fz1_87_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨91, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 91 (by decide)))

theorem fz1_87_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨92, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 92 (by decide)))

theorem fz1_87_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨93, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 93 (by decide)))

theorem fz1_87_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨94, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 94 (by decide)))

theorem fz1_87_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨95, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 95 (by decide)))

theorem fz1_87_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨96, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 96 (by decide)))

theorem fz1_87_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨97, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 97 (by decide)))

theorem fz1_87_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨98, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 98 (by decide)))

theorem fz1_87_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨99, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 99 (by decide)))

theorem fz1_87_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨100, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 100 (by decide)))

theorem fz1_87_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨101, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 101 (by decide)))

theorem fz1_87_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨102, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 102 (by decide)))

theorem fz1_87_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨103, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 103 (by decide)))

theorem fz1_87_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨104, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 104 (by decide)))

theorem fz1_87_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨105, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 105 (by decide)))

theorem fz1_87_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨106, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 106 (by decide)))

theorem fz1_87_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨107, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 107 (by decide)))

theorem fz1_87_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨108, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 108 (by decide)))

theorem fz1_87_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨109, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 109 (by decide)))

theorem fz1_87_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨110, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 110 (by decide)))

theorem fz1_87_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨111, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 111 (by decide)))

theorem fz1_87_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨112, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 112 (by decide)))

theorem fz1_87_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨113, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 113 (by decide)))

theorem fz1_87_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨114, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 114 (by decide)))

theorem fz1_87_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK87)) = 0 :=
  repsFixedCard rK87 ⟨115, by decide⟩ R87 hpxR87 hcardq87
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_87) 115 (by decide)))

theorem fixz2_87 : ([1, 6, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK87) (retConj 2 (Q2.R87_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_87_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨1, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 1 (by decide)))

theorem fz2_87_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨6, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 6 (by decide)))

theorem fz2_87_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨8, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 8 (by decide)))

theorem fz2_87_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨9, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 9 (by decide)))

theorem fz2_87_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨10, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 10 (by decide)))

theorem fz2_87_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨13, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 13 (by decide)))

theorem fz2_87_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨14, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 14 (by decide)))

theorem fz2_87_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨15, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 15 (by decide)))

theorem fz2_87_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨16, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 16 (by decide)))

theorem fz2_87_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨17, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 17 (by decide)))

theorem fz2_87_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨18, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 18 (by decide)))

theorem fz2_87_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨19, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 19 (by decide)))

theorem fz2_87_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨24, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 24 (by decide)))

theorem fz2_87_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨26, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 26 (by decide)))

theorem fz2_87_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨27, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 27 (by decide)))

theorem fz2_87_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨28, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 28 (by decide)))

theorem fz2_87_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨29, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 29 (by decide)))

theorem fz2_87_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨30, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 30 (by decide)))

theorem fz2_87_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨31, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 31 (by decide)))

theorem fz2_87_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨32, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 32 (by decide)))

theorem fz2_87_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨33, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 33 (by decide)))

theorem fz2_87_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨34, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 34 (by decide)))

theorem fz2_87_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨35, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 35 (by decide)))

theorem fz2_87_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨36, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 36 (by decide)))

theorem fz2_87_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨37, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 37 (by decide)))

theorem fz2_87_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨38, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 38 (by decide)))

theorem fz2_87_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨39, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 39 (by decide)))

theorem fz2_87_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨40, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 40 (by decide)))

theorem fz2_87_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨41, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 41 (by decide)))

theorem fz2_87_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨42, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 42 (by decide)))

theorem fz2_87_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨43, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 43 (by decide)))

theorem fz2_87_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨44, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 44 (by decide)))

theorem fz2_87_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨45, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 45 (by decide)))

theorem fz2_87_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨46, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 46 (by decide)))

theorem fz2_87_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨47, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 47 (by decide)))

theorem fz2_87_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨48, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 48 (by decide)))

theorem fz2_87_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨49, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 49 (by decide)))

theorem fz2_87_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨50, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 50 (by decide)))

theorem fz2_87_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨51, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 51 (by decide)))

theorem fz2_87_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨52, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 52 (by decide)))

theorem fz2_87_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨53, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 53 (by decide)))

theorem fz2_87_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨55, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 55 (by decide)))

theorem fz2_87_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨56, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 56 (by decide)))

theorem fz2_87_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨57, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 57 (by decide)))

theorem fz2_87_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨58, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 58 (by decide)))

theorem fz2_87_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨59, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 59 (by decide)))

theorem fz2_87_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨60, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 60 (by decide)))

theorem fz2_87_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨61, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 61 (by decide)))

theorem fz2_87_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨62, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 62 (by decide)))

theorem fz2_87_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨63, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 63 (by decide)))

theorem fz2_87_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨64, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 64 (by decide)))

theorem fz2_87_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨65, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 65 (by decide)))

theorem fz2_87_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨66, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 66 (by decide)))

theorem fz2_87_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨67, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 67 (by decide)))

theorem fz2_87_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨68, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 68 (by decide)))

theorem fz2_87_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨69, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 69 (by decide)))

theorem fz2_87_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨70, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 70 (by decide)))

theorem fz2_87_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨71, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 71 (by decide)))

theorem fz2_87_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨72, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 72 (by decide)))

theorem fz2_87_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨73, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 73 (by decide)))

theorem fz2_87_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨74, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 74 (by decide)))

theorem fz2_87_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨75, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 75 (by decide)))

theorem fz2_87_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨76, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 76 (by decide)))

theorem fz2_87_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨77, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 77 (by decide)))

theorem fz2_87_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨78, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 78 (by decide)))

theorem fz2_87_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨79, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 79 (by decide)))

theorem fz2_87_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨80, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 80 (by decide)))

theorem fz2_87_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨81, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 81 (by decide)))

theorem fz2_87_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨82, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 82 (by decide)))

theorem fz2_87_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨83, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 83 (by decide)))

theorem fz2_87_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨84, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 84 (by decide)))

theorem fz2_87_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨85, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 85 (by decide)))

theorem fz2_87_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨86, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 86 (by decide)))

theorem fz2_87_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨88, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 88 (by decide)))

theorem fz2_87_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨89, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 89 (by decide)))

theorem fz2_87_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨90, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 90 (by decide)))

theorem fz2_87_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨91, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 91 (by decide)))

theorem fz2_87_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨92, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 92 (by decide)))

theorem fz2_87_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨93, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 93 (by decide)))

theorem fz2_87_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨94, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 94 (by decide)))

theorem fz2_87_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨95, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 95 (by decide)))

theorem fz2_87_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨96, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 96 (by decide)))

theorem fz2_87_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨97, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 97 (by decide)))

theorem fz2_87_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨98, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 98 (by decide)))

theorem fz2_87_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨99, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 99 (by decide)))

theorem fz2_87_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨100, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 100 (by decide)))

theorem fz2_87_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨101, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 101 (by decide)))

theorem fz2_87_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨102, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 102 (by decide)))

theorem fz2_87_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨103, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 103 (by decide)))

theorem fz2_87_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨104, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 104 (by decide)))

theorem fz2_87_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨105, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 105 (by decide)))

theorem fz2_87_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨106, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 106 (by decide)))

theorem fz2_87_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨107, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 107 (by decide)))

theorem fz2_87_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨108, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 108 (by decide)))

theorem fz2_87_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨109, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 109 (by decide)))

theorem fz2_87_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨110, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 110 (by decide)))

theorem fz2_87_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨111, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 111 (by decide)))

theorem fz2_87_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨112, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 112 (by decide)))

theorem fz2_87_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨113, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 113 (by decide)))

theorem fz2_87_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨114, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 114 (by decide)))

theorem fz2_87_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK87)) = 0 :=
  Q2.repsFixedCard2 rK87 ⟨115, by decide⟩ Q2.R87_2 Q2.hpxR87_2 Q2.hcardq87_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_87) 115 (by decide)))

theorem fixz1_88 : ([1, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK88) (retConj 1 (R88 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_88_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨1, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 1 (by decide)))

theorem fz1_88_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨7, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 7 (by decide)))

theorem fz1_88_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨8, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 8 (by decide)))

theorem fz1_88_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨9, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 9 (by decide)))

theorem fz1_88_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨10, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 10 (by decide)))

theorem fz1_88_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨13, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 13 (by decide)))

theorem fz1_88_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨14, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 14 (by decide)))

theorem fz1_88_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨15, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 15 (by decide)))

theorem fz1_88_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨16, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 16 (by decide)))

theorem fz1_88_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨17, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 17 (by decide)))

theorem fz1_88_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨18, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 18 (by decide)))

theorem fz1_88_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨19, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 19 (by decide)))

theorem fz1_88_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨25, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 25 (by decide)))

theorem fz1_88_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨26, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 26 (by decide)))

theorem fz1_88_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨27, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 27 (by decide)))

theorem fz1_88_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨28, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 28 (by decide)))

theorem fz1_88_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨29, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 29 (by decide)))

theorem fz1_88_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨30, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 30 (by decide)))

theorem fz1_88_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨31, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 31 (by decide)))

theorem fz1_88_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨32, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 32 (by decide)))

theorem fz1_88_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨33, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 33 (by decide)))

theorem fz1_88_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨34, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 34 (by decide)))

theorem fz1_88_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨35, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 35 (by decide)))

theorem fz1_88_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨36, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 36 (by decide)))

theorem fz1_88_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨37, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 37 (by decide)))

theorem fz1_88_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨38, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 38 (by decide)))

theorem fz1_88_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨39, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 39 (by decide)))

theorem fz1_88_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨40, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 40 (by decide)))

theorem fz1_88_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨41, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 41 (by decide)))

theorem fz1_88_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨42, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 42 (by decide)))

theorem fz1_88_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨43, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 43 (by decide)))

theorem fz1_88_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨44, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 44 (by decide)))

theorem fz1_88_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨45, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 45 (by decide)))

theorem fz1_88_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨46, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 46 (by decide)))

theorem fz1_88_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨47, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 47 (by decide)))

theorem fz1_88_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨48, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 48 (by decide)))

theorem fz1_88_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨49, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 49 (by decide)))

theorem fz1_88_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨50, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 50 (by decide)))

theorem fz1_88_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨51, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 51 (by decide)))

theorem fz1_88_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨52, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 52 (by decide)))

theorem fz1_88_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨53, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 53 (by decide)))

theorem fz1_88_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨55, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 55 (by decide)))

theorem fz1_88_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨56, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 56 (by decide)))

theorem fz1_88_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨57, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 57 (by decide)))

theorem fz1_88_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨58, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 58 (by decide)))

theorem fz1_88_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨59, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 59 (by decide)))

theorem fz1_88_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨60, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 60 (by decide)))

theorem fz1_88_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨61, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 61 (by decide)))

theorem fz1_88_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨62, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 62 (by decide)))

theorem fz1_88_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨63, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 63 (by decide)))

theorem fz1_88_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨64, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 64 (by decide)))

theorem fz1_88_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨65, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 65 (by decide)))

theorem fz1_88_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨66, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 66 (by decide)))

theorem fz1_88_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨67, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 67 (by decide)))

theorem fz1_88_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨68, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 68 (by decide)))

theorem fz1_88_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨69, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 69 (by decide)))

theorem fz1_88_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨70, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 70 (by decide)))

theorem fz1_88_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨71, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 71 (by decide)))

theorem fz1_88_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨72, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 72 (by decide)))

theorem fz1_88_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨73, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 73 (by decide)))

theorem fz1_88_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨74, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 74 (by decide)))

theorem fz1_88_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨75, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 75 (by decide)))

theorem fz1_88_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨76, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 76 (by decide)))

theorem fz1_88_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨77, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 77 (by decide)))

theorem fz1_88_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨78, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 78 (by decide)))

theorem fz1_88_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨79, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 79 (by decide)))

theorem fz1_88_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨80, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 80 (by decide)))

theorem fz1_88_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨81, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 81 (by decide)))

theorem fz1_88_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨82, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 82 (by decide)))

theorem fz1_88_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨83, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 83 (by decide)))

theorem fz1_88_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨84, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 84 (by decide)))

theorem fz1_88_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨85, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 85 (by decide)))

theorem fz1_88_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨86, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 86 (by decide)))

theorem fz1_88_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨87, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 87 (by decide)))

theorem fz1_88_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨89, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 89 (by decide)))

theorem fz1_88_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨90, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 90 (by decide)))

theorem fz1_88_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨91, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 91 (by decide)))

theorem fz1_88_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨92, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 92 (by decide)))

theorem fz1_88_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨93, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 93 (by decide)))

theorem fz1_88_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨94, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 94 (by decide)))

theorem fz1_88_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨95, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 95 (by decide)))

theorem fz1_88_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨96, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 96 (by decide)))

theorem fz1_88_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨97, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 97 (by decide)))

theorem fz1_88_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨98, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 98 (by decide)))

theorem fz1_88_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨99, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 99 (by decide)))

theorem fz1_88_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨100, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 100 (by decide)))

theorem fz1_88_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨101, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 101 (by decide)))

theorem fz1_88_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨102, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 102 (by decide)))

theorem fz1_88_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨103, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 103 (by decide)))

theorem fz1_88_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨104, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 104 (by decide)))

theorem fz1_88_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨105, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 105 (by decide)))

theorem fz1_88_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨106, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 106 (by decide)))

theorem fz1_88_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨107, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 107 (by decide)))

theorem fz1_88_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨108, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 108 (by decide)))

theorem fz1_88_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨109, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 109 (by decide)))

theorem fz1_88_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨110, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 110 (by decide)))

theorem fz1_88_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨111, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 111 (by decide)))

theorem fz1_88_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨112, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 112 (by decide)))

theorem fz1_88_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨113, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 113 (by decide)))

theorem fz1_88_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨114, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 114 (by decide)))

theorem fz1_88_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK88)) = 0 :=
  repsFixedCard rK88 ⟨115, by decide⟩ R88 hpxR88 hcardq88
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_88) 115 (by decide)))

theorem fixz2_88 : ([1, 7, 8, 9, 10, 13, 14, 15, 16, 17, 18, 19, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK88) (retConj 2 (Q2.R88_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_88_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨1, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 1 (by decide)))

theorem fz2_88_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨7, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 7 (by decide)))

theorem fz2_88_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨8, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 8 (by decide)))

theorem fz2_88_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨9, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 9 (by decide)))

theorem fz2_88_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨10, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 10 (by decide)))

theorem fz2_88_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨13, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 13 (by decide)))

theorem fz2_88_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨14, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 14 (by decide)))

theorem fz2_88_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨15, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 15 (by decide)))

theorem fz2_88_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨16, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 16 (by decide)))

theorem fz2_88_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨17, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 17 (by decide)))

theorem fz2_88_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨18, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 18 (by decide)))

theorem fz2_88_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨19, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 19 (by decide)))

theorem fz2_88_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨25, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 25 (by decide)))

theorem fz2_88_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨26, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 26 (by decide)))

theorem fz2_88_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨27, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 27 (by decide)))

theorem fz2_88_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨28, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 28 (by decide)))

theorem fz2_88_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨29, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 29 (by decide)))

theorem fz2_88_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨30, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 30 (by decide)))

theorem fz2_88_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨31, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 31 (by decide)))

theorem fz2_88_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨32, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 32 (by decide)))

theorem fz2_88_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨33, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 33 (by decide)))

theorem fz2_88_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨34, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 34 (by decide)))

theorem fz2_88_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨35, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 35 (by decide)))

theorem fz2_88_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨36, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 36 (by decide)))

theorem fz2_88_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨37, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 37 (by decide)))

theorem fz2_88_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨38, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 38 (by decide)))

theorem fz2_88_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨39, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 39 (by decide)))

theorem fz2_88_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨40, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 40 (by decide)))

theorem fz2_88_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨41, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 41 (by decide)))

theorem fz2_88_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨42, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 42 (by decide)))

theorem fz2_88_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨43, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 43 (by decide)))

theorem fz2_88_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨44, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 44 (by decide)))

theorem fz2_88_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨45, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 45 (by decide)))

theorem fz2_88_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨46, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 46 (by decide)))

theorem fz2_88_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨47, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 47 (by decide)))

theorem fz2_88_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨48, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 48 (by decide)))

theorem fz2_88_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨49, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 49 (by decide)))

theorem fz2_88_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨50, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 50 (by decide)))

theorem fz2_88_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨51, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 51 (by decide)))

theorem fz2_88_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨52, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 52 (by decide)))

theorem fz2_88_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨53, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 53 (by decide)))

theorem fz2_88_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨55, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 55 (by decide)))

theorem fz2_88_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨56, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 56 (by decide)))

theorem fz2_88_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨57, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 57 (by decide)))

theorem fz2_88_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨58, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 58 (by decide)))

theorem fz2_88_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨59, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 59 (by decide)))

theorem fz2_88_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨60, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 60 (by decide)))

theorem fz2_88_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨61, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 61 (by decide)))

theorem fz2_88_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨62, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 62 (by decide)))

theorem fz2_88_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨63, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 63 (by decide)))

theorem fz2_88_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨64, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 64 (by decide)))

theorem fz2_88_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨65, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 65 (by decide)))

theorem fz2_88_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨66, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 66 (by decide)))

theorem fz2_88_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨67, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 67 (by decide)))

theorem fz2_88_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨68, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 68 (by decide)))

theorem fz2_88_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨69, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 69 (by decide)))

theorem fz2_88_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨70, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 70 (by decide)))

theorem fz2_88_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨71, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 71 (by decide)))

theorem fz2_88_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨72, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 72 (by decide)))

theorem fz2_88_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨73, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 73 (by decide)))

theorem fz2_88_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨74, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 74 (by decide)))

theorem fz2_88_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨75, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 75 (by decide)))

theorem fz2_88_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨76, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 76 (by decide)))

theorem fz2_88_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨77, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 77 (by decide)))

theorem fz2_88_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨78, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 78 (by decide)))

theorem fz2_88_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨79, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 79 (by decide)))

theorem fz2_88_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨80, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 80 (by decide)))

theorem fz2_88_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨81, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 81 (by decide)))

theorem fz2_88_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨82, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 82 (by decide)))

theorem fz2_88_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨83, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 83 (by decide)))

theorem fz2_88_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨84, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 84 (by decide)))

theorem fz2_88_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨85, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 85 (by decide)))

theorem fz2_88_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨86, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 86 (by decide)))

theorem fz2_88_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨87, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 87 (by decide)))

theorem fz2_88_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨89, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 89 (by decide)))

theorem fz2_88_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨90, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 90 (by decide)))

theorem fz2_88_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨91, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 91 (by decide)))

theorem fz2_88_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨92, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 92 (by decide)))

theorem fz2_88_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨93, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 93 (by decide)))

theorem fz2_88_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨94, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 94 (by decide)))

theorem fz2_88_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨95, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 95 (by decide)))

theorem fz2_88_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨96, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 96 (by decide)))

theorem fz2_88_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨97, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 97 (by decide)))

theorem fz2_88_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨98, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 98 (by decide)))

theorem fz2_88_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨99, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 99 (by decide)))

theorem fz2_88_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨100, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 100 (by decide)))

theorem fz2_88_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨101, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 101 (by decide)))

theorem fz2_88_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨102, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 102 (by decide)))

theorem fz2_88_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨103, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 103 (by decide)))

theorem fz2_88_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨104, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 104 (by decide)))

theorem fz2_88_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨105, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 105 (by decide)))

theorem fz2_88_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨106, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 106 (by decide)))

theorem fz2_88_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨107, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 107 (by decide)))

theorem fz2_88_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨108, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 108 (by decide)))

theorem fz2_88_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨109, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 109 (by decide)))

theorem fz2_88_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨110, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 110 (by decide)))

theorem fz2_88_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨111, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 111 (by decide)))

theorem fz2_88_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨112, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 112 (by decide)))

theorem fz2_88_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨113, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 113 (by decide)))

theorem fz2_88_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨114, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 114 (by decide)))

theorem fz2_88_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK88)) = 0 :=
  Q2.repsFixedCard2 rK88 ⟨115, by decide⟩ Q2.R88_2 Q2.hpxR88_2 Q2.hcardq88_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_88) 115 (by decide)))

end LeanDring.P5Presentation
