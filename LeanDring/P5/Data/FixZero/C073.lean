/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C021

/-!
# Species-table cells, off-support emptiness certificates, chunk 72

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

theorem fixz1_91 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK91) (retConj 1 (R91 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_91_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨1, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 1 (by decide)))

theorem fz1_91_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨2, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 2 (by decide)))

theorem fz1_91_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨3, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 3 (by decide)))

theorem fz1_91_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨4, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 4 (by decide)))

theorem fz1_91_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨5, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 5 (by decide)))

theorem fz1_91_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨6, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 6 (by decide)))

theorem fz1_91_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨7, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 7 (by decide)))

theorem fz1_91_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨8, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 8 (by decide)))

theorem fz1_91_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨9, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 9 (by decide)))

theorem fz1_91_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨11, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 11 (by decide)))

theorem fz1_91_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨13, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 13 (by decide)))

theorem fz1_91_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨14, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 14 (by decide)))

theorem fz1_91_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨15, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 15 (by decide)))

theorem fz1_91_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨16, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 16 (by decide)))

theorem fz1_91_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨17, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 17 (by decide)))

theorem fz1_91_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨18, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 18 (by decide)))

theorem fz1_91_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨19, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 19 (by decide)))

theorem fz1_91_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨20, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 20 (by decide)))

theorem fz1_91_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨21, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 21 (by decide)))

theorem fz1_91_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨22, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 22 (by decide)))

theorem fz1_91_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨23, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 23 (by decide)))

theorem fz1_91_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨24, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 24 (by decide)))

theorem fz1_91_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨25, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 25 (by decide)))

theorem fz1_91_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨26, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 26 (by decide)))

theorem fz1_91_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨27, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 27 (by decide)))

theorem fz1_91_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨28, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 28 (by decide)))

theorem fz1_91_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨30, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 30 (by decide)))

theorem fz1_91_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨31, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 31 (by decide)))

theorem fz1_91_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨32, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 32 (by decide)))

theorem fz1_91_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨33, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 33 (by decide)))

theorem fz1_91_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨34, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 34 (by decide)))

theorem fz1_91_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨35, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 35 (by decide)))

theorem fz1_91_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨36, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 36 (by decide)))

theorem fz1_91_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨37, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 37 (by decide)))

theorem fz1_91_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨38, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 38 (by decide)))

theorem fz1_91_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨39, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 39 (by decide)))

theorem fz1_91_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨40, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 40 (by decide)))

theorem fz1_91_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨41, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 41 (by decide)))

theorem fz1_91_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨42, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 42 (by decide)))

theorem fz1_91_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨43, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 43 (by decide)))

theorem fz1_91_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨44, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 44 (by decide)))

theorem fz1_91_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨45, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 45 (by decide)))

theorem fz1_91_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨46, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 46 (by decide)))

theorem fz1_91_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨47, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 47 (by decide)))

theorem fz1_91_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨48, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 48 (by decide)))

theorem fz1_91_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨49, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 49 (by decide)))

theorem fz1_91_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨50, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 50 (by decide)))

theorem fz1_91_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨51, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 51 (by decide)))

theorem fz1_91_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨52, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 52 (by decide)))

theorem fz1_91_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨54, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 54 (by decide)))

theorem fz1_91_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨55, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 55 (by decide)))

theorem fz1_91_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨56, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 56 (by decide)))

theorem fz1_91_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨57, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 57 (by decide)))

theorem fz1_91_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨58, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 58 (by decide)))

theorem fz1_91_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨59, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 59 (by decide)))

theorem fz1_91_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨60, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 60 (by decide)))

theorem fz1_91_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨61, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 61 (by decide)))

theorem fz1_91_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨62, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 62 (by decide)))

theorem fz1_91_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨63, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 63 (by decide)))

theorem fz1_91_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨64, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 64 (by decide)))

theorem fz1_91_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨65, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 65 (by decide)))

theorem fz1_91_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨66, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 66 (by decide)))

theorem fz1_91_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨67, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 67 (by decide)))

theorem fz1_91_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨68, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 68 (by decide)))

theorem fz1_91_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨69, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 69 (by decide)))

theorem fz1_91_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨70, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 70 (by decide)))

theorem fz1_91_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨71, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 71 (by decide)))

theorem fz1_91_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨72, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 72 (by decide)))

theorem fz1_91_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨73, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 73 (by decide)))

theorem fz1_91_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨74, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 74 (by decide)))

theorem fz1_91_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨75, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 75 (by decide)))

theorem fz1_91_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨76, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 76 (by decide)))

theorem fz1_91_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨77, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 77 (by decide)))

theorem fz1_91_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨78, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 78 (by decide)))

theorem fz1_91_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨79, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 79 (by decide)))

theorem fz1_91_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨80, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 80 (by decide)))

theorem fz1_91_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨81, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 81 (by decide)))

theorem fz1_91_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨82, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 82 (by decide)))

theorem fz1_91_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨83, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 83 (by decide)))

theorem fz1_91_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨84, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 84 (by decide)))

theorem fz1_91_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨85, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 85 (by decide)))

theorem fz1_91_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨86, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 86 (by decide)))

theorem fz1_91_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨87, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 87 (by decide)))

theorem fz1_91_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨88, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 88 (by decide)))

theorem fz1_91_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨89, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 89 (by decide)))

theorem fz1_91_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨90, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 90 (by decide)))

theorem fz1_91_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨92, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 92 (by decide)))

theorem fz1_91_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨93, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 93 (by decide)))

theorem fz1_91_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨94, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 94 (by decide)))

theorem fz1_91_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨95, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 95 (by decide)))

theorem fz1_91_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨96, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 96 (by decide)))

theorem fz1_91_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨97, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 97 (by decide)))

theorem fz1_91_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨98, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 98 (by decide)))

theorem fz1_91_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨99, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 99 (by decide)))

theorem fz1_91_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨100, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 100 (by decide)))

theorem fz1_91_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨101, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 101 (by decide)))

theorem fz1_91_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨102, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 102 (by decide)))

theorem fz1_91_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨103, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 103 (by decide)))

theorem fz1_91_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨104, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 104 (by decide)))

theorem fz1_91_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨105, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 105 (by decide)))

theorem fz1_91_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨106, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 106 (by decide)))

theorem fz1_91_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨107, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 107 (by decide)))

theorem fz1_91_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨108, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 108 (by decide)))

theorem fz1_91_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨109, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 109 (by decide)))

theorem fz1_91_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨110, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 110 (by decide)))

theorem fz1_91_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨111, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 111 (by decide)))

theorem fz1_91_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨112, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 112 (by decide)))

theorem fz1_91_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨113, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 113 (by decide)))

theorem fz1_91_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨114, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 114 (by decide)))

theorem fz1_91_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK91)) = 0 :=
  repsFixedCard rK91 ⟨115, by decide⟩ R91 hpxR91 hcardq91
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_91) 115 (by decide)))

theorem fixz2_91 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK91) (retConj 2 (Q2.R91_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_91_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨1, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 1 (by decide)))

theorem fz2_91_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨2, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 2 (by decide)))

theorem fz2_91_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨3, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 3 (by decide)))

theorem fz2_91_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨4, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 4 (by decide)))

theorem fz2_91_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨5, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 5 (by decide)))

theorem fz2_91_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨6, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 6 (by decide)))

theorem fz2_91_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨7, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 7 (by decide)))

theorem fz2_91_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨8, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 8 (by decide)))

theorem fz2_91_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨9, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 9 (by decide)))

theorem fz2_91_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨11, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 11 (by decide)))

theorem fz2_91_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨13, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 13 (by decide)))

theorem fz2_91_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨14, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 14 (by decide)))

theorem fz2_91_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨15, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 15 (by decide)))

theorem fz2_91_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨16, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 16 (by decide)))

theorem fz2_91_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨17, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 17 (by decide)))

theorem fz2_91_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨18, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 18 (by decide)))

theorem fz2_91_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨19, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 19 (by decide)))

theorem fz2_91_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨20, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 20 (by decide)))

theorem fz2_91_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨21, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 21 (by decide)))

theorem fz2_91_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨22, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 22 (by decide)))

theorem fz2_91_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨23, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 23 (by decide)))

theorem fz2_91_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨24, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 24 (by decide)))

theorem fz2_91_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨25, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 25 (by decide)))

theorem fz2_91_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨26, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 26 (by decide)))

theorem fz2_91_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨27, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 27 (by decide)))

theorem fz2_91_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨28, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 28 (by decide)))

theorem fz2_91_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨30, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 30 (by decide)))

theorem fz2_91_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨31, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 31 (by decide)))

theorem fz2_91_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨32, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 32 (by decide)))

theorem fz2_91_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨33, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 33 (by decide)))

theorem fz2_91_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨34, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 34 (by decide)))

theorem fz2_91_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨35, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 35 (by decide)))

theorem fz2_91_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨36, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 36 (by decide)))

theorem fz2_91_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨37, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 37 (by decide)))

theorem fz2_91_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨38, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 38 (by decide)))

theorem fz2_91_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨39, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 39 (by decide)))

theorem fz2_91_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨40, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 40 (by decide)))

theorem fz2_91_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨41, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 41 (by decide)))

theorem fz2_91_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨42, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 42 (by decide)))

theorem fz2_91_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨43, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 43 (by decide)))

theorem fz2_91_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨44, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 44 (by decide)))

theorem fz2_91_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨45, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 45 (by decide)))

theorem fz2_91_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨46, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 46 (by decide)))

theorem fz2_91_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨47, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 47 (by decide)))

theorem fz2_91_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨48, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 48 (by decide)))

theorem fz2_91_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨49, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 49 (by decide)))

theorem fz2_91_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨50, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 50 (by decide)))

theorem fz2_91_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨51, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 51 (by decide)))

theorem fz2_91_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨52, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 52 (by decide)))

theorem fz2_91_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨54, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 54 (by decide)))

theorem fz2_91_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨55, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 55 (by decide)))

theorem fz2_91_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨56, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 56 (by decide)))

theorem fz2_91_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨57, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 57 (by decide)))

theorem fz2_91_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨58, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 58 (by decide)))

theorem fz2_91_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨59, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 59 (by decide)))

theorem fz2_91_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨60, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 60 (by decide)))

theorem fz2_91_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨61, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 61 (by decide)))

theorem fz2_91_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨62, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 62 (by decide)))

theorem fz2_91_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨63, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 63 (by decide)))

theorem fz2_91_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨64, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 64 (by decide)))

theorem fz2_91_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨65, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 65 (by decide)))

theorem fz2_91_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨66, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 66 (by decide)))

theorem fz2_91_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨67, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 67 (by decide)))

theorem fz2_91_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨68, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 68 (by decide)))

theorem fz2_91_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨69, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 69 (by decide)))

theorem fz2_91_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨70, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 70 (by decide)))

theorem fz2_91_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨71, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 71 (by decide)))

theorem fz2_91_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨72, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 72 (by decide)))

theorem fz2_91_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨73, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 73 (by decide)))

theorem fz2_91_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨74, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 74 (by decide)))

theorem fz2_91_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨75, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 75 (by decide)))

theorem fz2_91_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨76, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 76 (by decide)))

theorem fz2_91_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨77, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 77 (by decide)))

theorem fz2_91_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨78, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 78 (by decide)))

theorem fz2_91_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨79, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 79 (by decide)))

theorem fz2_91_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨80, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 80 (by decide)))

theorem fz2_91_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨81, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 81 (by decide)))

theorem fz2_91_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨82, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 82 (by decide)))

theorem fz2_91_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨83, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 83 (by decide)))

theorem fz2_91_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨84, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 84 (by decide)))

theorem fz2_91_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨85, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 85 (by decide)))

theorem fz2_91_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨86, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 86 (by decide)))

theorem fz2_91_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨87, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 87 (by decide)))

theorem fz2_91_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨88, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 88 (by decide)))

theorem fz2_91_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨89, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 89 (by decide)))

theorem fz2_91_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨90, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 90 (by decide)))

theorem fz2_91_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨92, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 92 (by decide)))

theorem fz2_91_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨93, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 93 (by decide)))

theorem fz2_91_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨94, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 94 (by decide)))

theorem fz2_91_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨95, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 95 (by decide)))

theorem fz2_91_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨96, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 96 (by decide)))

theorem fz2_91_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨97, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 97 (by decide)))

theorem fz2_91_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨98, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 98 (by decide)))

theorem fz2_91_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨99, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 99 (by decide)))

theorem fz2_91_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨100, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 100 (by decide)))

theorem fz2_91_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨101, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 101 (by decide)))

theorem fz2_91_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨102, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 102 (by decide)))

theorem fz2_91_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨103, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 103 (by decide)))

theorem fz2_91_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨104, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 104 (by decide)))

theorem fz2_91_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨105, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 105 (by decide)))

theorem fz2_91_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨106, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 106 (by decide)))

theorem fz2_91_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨107, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 107 (by decide)))

theorem fz2_91_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨108, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 108 (by decide)))

theorem fz2_91_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨109, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 109 (by decide)))

theorem fz2_91_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨110, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 110 (by decide)))

theorem fz2_91_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨111, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 111 (by decide)))

theorem fz2_91_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨112, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 112 (by decide)))

theorem fz2_91_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨113, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 113 (by decide)))

theorem fz2_91_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨114, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 114 (by decide)))

theorem fz2_91_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK91)) = 0 :=
  Q2.repsFixedCard2 rK91 ⟨115, by decide⟩ Q2.R91_2 Q2.hpxR91_2 Q2.hcardq91_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_91) 115 (by decide)))

theorem fixz1_92 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK92) (retConj 1 (R92 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_92_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨1, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 1 (by decide)))

theorem fz1_92_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨2, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 2 (by decide)))

theorem fz1_92_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨3, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 3 (by decide)))

theorem fz1_92_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨4, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 4 (by decide)))

theorem fz1_92_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨5, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 5 (by decide)))

theorem fz1_92_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨6, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 6 (by decide)))

theorem fz1_92_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨7, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 7 (by decide)))

theorem fz1_92_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨8, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 8 (by decide)))

theorem fz1_92_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨9, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 9 (by decide)))

theorem fz1_92_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨11, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 11 (by decide)))

theorem fz1_92_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨13, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 13 (by decide)))

theorem fz1_92_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨14, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 14 (by decide)))

theorem fz1_92_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨15, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 15 (by decide)))

theorem fz1_92_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨16, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 16 (by decide)))

theorem fz1_92_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨17, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 17 (by decide)))

theorem fz1_92_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨18, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 18 (by decide)))

theorem fz1_92_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨19, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 19 (by decide)))

theorem fz1_92_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨20, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 20 (by decide)))

theorem fz1_92_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨21, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 21 (by decide)))

theorem fz1_92_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨22, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 22 (by decide)))

theorem fz1_92_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨23, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 23 (by decide)))

theorem fz1_92_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨24, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 24 (by decide)))

theorem fz1_92_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨25, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 25 (by decide)))

theorem fz1_92_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨26, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 26 (by decide)))

theorem fz1_92_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨27, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 27 (by decide)))

theorem fz1_92_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨28, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 28 (by decide)))

theorem fz1_92_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨29, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 29 (by decide)))

theorem fz1_92_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨31, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 31 (by decide)))

theorem fz1_92_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨32, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 32 (by decide)))

theorem fz1_92_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨33, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 33 (by decide)))

theorem fz1_92_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨34, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 34 (by decide)))

theorem fz1_92_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨35, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 35 (by decide)))

theorem fz1_92_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨36, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 36 (by decide)))

theorem fz1_92_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨37, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 37 (by decide)))

theorem fz1_92_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨38, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 38 (by decide)))

theorem fz1_92_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨39, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 39 (by decide)))

theorem fz1_92_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨40, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 40 (by decide)))

theorem fz1_92_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨41, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 41 (by decide)))

theorem fz1_92_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨42, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 42 (by decide)))

theorem fz1_92_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨43, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 43 (by decide)))

theorem fz1_92_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨44, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 44 (by decide)))

theorem fz1_92_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨45, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 45 (by decide)))

theorem fz1_92_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨46, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 46 (by decide)))

theorem fz1_92_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨47, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 47 (by decide)))

theorem fz1_92_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨48, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 48 (by decide)))

theorem fz1_92_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨49, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 49 (by decide)))

theorem fz1_92_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨50, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 50 (by decide)))

theorem fz1_92_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨51, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 51 (by decide)))

theorem fz1_92_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨52, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 52 (by decide)))

theorem fz1_92_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨54, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 54 (by decide)))

theorem fz1_92_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨55, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 55 (by decide)))

theorem fz1_92_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨56, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 56 (by decide)))

theorem fz1_92_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨57, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 57 (by decide)))

theorem fz1_92_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨58, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 58 (by decide)))

theorem fz1_92_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨59, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 59 (by decide)))

theorem fz1_92_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨60, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 60 (by decide)))

theorem fz1_92_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨61, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 61 (by decide)))

theorem fz1_92_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨62, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 62 (by decide)))

theorem fz1_92_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨63, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 63 (by decide)))

theorem fz1_92_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨64, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 64 (by decide)))

theorem fz1_92_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨65, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 65 (by decide)))

theorem fz1_92_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨66, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 66 (by decide)))

theorem fz1_92_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨67, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 67 (by decide)))

theorem fz1_92_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨68, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 68 (by decide)))

theorem fz1_92_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨69, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 69 (by decide)))

theorem fz1_92_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨70, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 70 (by decide)))

theorem fz1_92_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨71, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 71 (by decide)))

theorem fz1_92_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨72, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 72 (by decide)))

theorem fz1_92_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨73, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 73 (by decide)))

theorem fz1_92_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨74, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 74 (by decide)))

theorem fz1_92_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨75, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 75 (by decide)))

theorem fz1_92_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨76, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 76 (by decide)))

theorem fz1_92_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨77, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 77 (by decide)))

theorem fz1_92_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨78, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 78 (by decide)))

theorem fz1_92_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨79, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 79 (by decide)))

theorem fz1_92_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨80, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 80 (by decide)))

theorem fz1_92_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨81, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 81 (by decide)))

theorem fz1_92_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨82, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 82 (by decide)))

theorem fz1_92_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨83, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 83 (by decide)))

theorem fz1_92_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨84, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 84 (by decide)))

theorem fz1_92_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨85, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 85 (by decide)))

theorem fz1_92_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨86, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 86 (by decide)))

theorem fz1_92_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨87, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 87 (by decide)))

theorem fz1_92_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨88, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 88 (by decide)))

theorem fz1_92_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨89, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 89 (by decide)))

theorem fz1_92_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨90, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 90 (by decide)))

theorem fz1_92_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨91, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 91 (by decide)))

theorem fz1_92_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨93, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 93 (by decide)))

theorem fz1_92_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨94, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 94 (by decide)))

theorem fz1_92_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨95, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 95 (by decide)))

theorem fz1_92_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨96, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 96 (by decide)))

theorem fz1_92_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨97, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 97 (by decide)))

theorem fz1_92_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨98, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 98 (by decide)))

theorem fz1_92_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨99, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 99 (by decide)))

theorem fz1_92_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨100, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 100 (by decide)))

theorem fz1_92_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨101, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 101 (by decide)))

theorem fz1_92_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨102, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 102 (by decide)))

theorem fz1_92_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨103, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 103 (by decide)))

theorem fz1_92_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨104, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 104 (by decide)))

theorem fz1_92_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨105, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 105 (by decide)))

theorem fz1_92_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨106, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 106 (by decide)))

theorem fz1_92_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨107, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 107 (by decide)))

theorem fz1_92_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨108, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 108 (by decide)))

theorem fz1_92_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨109, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 109 (by decide)))

theorem fz1_92_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨110, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 110 (by decide)))

theorem fz1_92_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨111, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 111 (by decide)))

theorem fz1_92_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨112, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 112 (by decide)))

theorem fz1_92_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨113, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 113 (by decide)))

theorem fz1_92_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨114, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 114 (by decide)))

theorem fz1_92_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK92)) = 0 :=
  repsFixedCard rK92 ⟨115, by decide⟩ R92 hpxR92 hcardq92
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_92) 115 (by decide)))

theorem fixz2_92 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK92) (retConj 2 (Q2.R92_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_92_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨1, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 1 (by decide)))

theorem fz2_92_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨2, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 2 (by decide)))

theorem fz2_92_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨3, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 3 (by decide)))

theorem fz2_92_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨4, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 4 (by decide)))

theorem fz2_92_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨5, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 5 (by decide)))

theorem fz2_92_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨6, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 6 (by decide)))

theorem fz2_92_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨7, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 7 (by decide)))

theorem fz2_92_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨8, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 8 (by decide)))

theorem fz2_92_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨9, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 9 (by decide)))

theorem fz2_92_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨11, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 11 (by decide)))

theorem fz2_92_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨13, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 13 (by decide)))

theorem fz2_92_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨14, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 14 (by decide)))

theorem fz2_92_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨15, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 15 (by decide)))

theorem fz2_92_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨16, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 16 (by decide)))

theorem fz2_92_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨17, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 17 (by decide)))

theorem fz2_92_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨18, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 18 (by decide)))

theorem fz2_92_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨19, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 19 (by decide)))

theorem fz2_92_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨20, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 20 (by decide)))

theorem fz2_92_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨21, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 21 (by decide)))

theorem fz2_92_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨22, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 22 (by decide)))

theorem fz2_92_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨23, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 23 (by decide)))

theorem fz2_92_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨24, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 24 (by decide)))

theorem fz2_92_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨25, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 25 (by decide)))

theorem fz2_92_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨26, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 26 (by decide)))

theorem fz2_92_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨27, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 27 (by decide)))

theorem fz2_92_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨28, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 28 (by decide)))

theorem fz2_92_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨29, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 29 (by decide)))

theorem fz2_92_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨31, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 31 (by decide)))

theorem fz2_92_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨32, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 32 (by decide)))

theorem fz2_92_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨33, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 33 (by decide)))

theorem fz2_92_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨34, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 34 (by decide)))

theorem fz2_92_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨35, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 35 (by decide)))

theorem fz2_92_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨36, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 36 (by decide)))

theorem fz2_92_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨37, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 37 (by decide)))

theorem fz2_92_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨38, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 38 (by decide)))

theorem fz2_92_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨39, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 39 (by decide)))

theorem fz2_92_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨40, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 40 (by decide)))

theorem fz2_92_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨41, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 41 (by decide)))

theorem fz2_92_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨42, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 42 (by decide)))

theorem fz2_92_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨43, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 43 (by decide)))

theorem fz2_92_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨44, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 44 (by decide)))

theorem fz2_92_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨45, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 45 (by decide)))

theorem fz2_92_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨46, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 46 (by decide)))

theorem fz2_92_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨47, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 47 (by decide)))

theorem fz2_92_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨48, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 48 (by decide)))

theorem fz2_92_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨49, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 49 (by decide)))

theorem fz2_92_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨50, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 50 (by decide)))

theorem fz2_92_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨51, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 51 (by decide)))

theorem fz2_92_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨52, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 52 (by decide)))

theorem fz2_92_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨54, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 54 (by decide)))

theorem fz2_92_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨55, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 55 (by decide)))

theorem fz2_92_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨56, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 56 (by decide)))

theorem fz2_92_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨57, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 57 (by decide)))

theorem fz2_92_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨58, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 58 (by decide)))

theorem fz2_92_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨59, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 59 (by decide)))

theorem fz2_92_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨60, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 60 (by decide)))

theorem fz2_92_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨61, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 61 (by decide)))

theorem fz2_92_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨62, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 62 (by decide)))

theorem fz2_92_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨63, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 63 (by decide)))

theorem fz2_92_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨64, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 64 (by decide)))

theorem fz2_92_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨65, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 65 (by decide)))

theorem fz2_92_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨66, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 66 (by decide)))

theorem fz2_92_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨67, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 67 (by decide)))

theorem fz2_92_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨68, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 68 (by decide)))

theorem fz2_92_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨69, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 69 (by decide)))

theorem fz2_92_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨70, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 70 (by decide)))

theorem fz2_92_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨71, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 71 (by decide)))

theorem fz2_92_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨72, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 72 (by decide)))

theorem fz2_92_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨73, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 73 (by decide)))

theorem fz2_92_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨74, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 74 (by decide)))

theorem fz2_92_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨75, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 75 (by decide)))

theorem fz2_92_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨76, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 76 (by decide)))

theorem fz2_92_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨77, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 77 (by decide)))

theorem fz2_92_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨78, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 78 (by decide)))

theorem fz2_92_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨79, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 79 (by decide)))

theorem fz2_92_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨80, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 80 (by decide)))

theorem fz2_92_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨81, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 81 (by decide)))

theorem fz2_92_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨82, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 82 (by decide)))

theorem fz2_92_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨83, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 83 (by decide)))

theorem fz2_92_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨84, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 84 (by decide)))

theorem fz2_92_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨85, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 85 (by decide)))

theorem fz2_92_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨86, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 86 (by decide)))

theorem fz2_92_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨87, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 87 (by decide)))

theorem fz2_92_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨88, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 88 (by decide)))

theorem fz2_92_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨89, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 89 (by decide)))

theorem fz2_92_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨90, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 90 (by decide)))

theorem fz2_92_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨91, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 91 (by decide)))

theorem fz2_92_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨93, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 93 (by decide)))

theorem fz2_92_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨94, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 94 (by decide)))

theorem fz2_92_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨95, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 95 (by decide)))

theorem fz2_92_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨96, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 96 (by decide)))

theorem fz2_92_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨97, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 97 (by decide)))

theorem fz2_92_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨98, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 98 (by decide)))

theorem fz2_92_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨99, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 99 (by decide)))

theorem fz2_92_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨100, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 100 (by decide)))

theorem fz2_92_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨101, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 101 (by decide)))

theorem fz2_92_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨102, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 102 (by decide)))

theorem fz2_92_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨103, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 103 (by decide)))

theorem fz2_92_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨104, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 104 (by decide)))

theorem fz2_92_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨105, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 105 (by decide)))

theorem fz2_92_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨106, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 106 (by decide)))

theorem fz2_92_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨107, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 107 (by decide)))

theorem fz2_92_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨108, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 108 (by decide)))

theorem fz2_92_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨109, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 109 (by decide)))

theorem fz2_92_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨110, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 110 (by decide)))

theorem fz2_92_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨111, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 111 (by decide)))

theorem fz2_92_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨112, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 112 (by decide)))

theorem fz2_92_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨113, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 113 (by decide)))

theorem fz2_92_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨114, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 114 (by decide)))

theorem fz2_92_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK92)) = 0 :=
  Q2.repsFixedCard2 rK92 ⟨115, by decide⟩ Q2.R92_2 Q2.hpxR92_2 Q2.hcardq92_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_92) 115 (by decide)))

end LeanDring.P5Presentation
