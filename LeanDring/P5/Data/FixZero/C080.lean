/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C023

/-!
# Species-table cells, off-support emptiness certificates, chunk 79

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

theorem fixz1_105 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK105) (retConj 1 (R105 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_105_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨1, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 1 (by decide)))

theorem fz1_105_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨2, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 2 (by decide)))

theorem fz1_105_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨3, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 3 (by decide)))

theorem fz1_105_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨4, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 4 (by decide)))

theorem fz1_105_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨5, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 5 (by decide)))

theorem fz1_105_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨6, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 6 (by decide)))

theorem fz1_105_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨7, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 7 (by decide)))

theorem fz1_105_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨8, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 8 (by decide)))

theorem fz1_105_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨9, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 9 (by decide)))

theorem fz1_105_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨11, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 11 (by decide)))

theorem fz1_105_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨13, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 13 (by decide)))

theorem fz1_105_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨14, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 14 (by decide)))

theorem fz1_105_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨15, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 15 (by decide)))

theorem fz1_105_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨16, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 16 (by decide)))

theorem fz1_105_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨17, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 17 (by decide)))

theorem fz1_105_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨18, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 18 (by decide)))

theorem fz1_105_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨19, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 19 (by decide)))

theorem fz1_105_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨20, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 20 (by decide)))

theorem fz1_105_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨21, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 21 (by decide)))

theorem fz1_105_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨22, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 22 (by decide)))

theorem fz1_105_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨23, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 23 (by decide)))

theorem fz1_105_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨24, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 24 (by decide)))

theorem fz1_105_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨25, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 25 (by decide)))

theorem fz1_105_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨26, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 26 (by decide)))

theorem fz1_105_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨27, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 27 (by decide)))

theorem fz1_105_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨28, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 28 (by decide)))

theorem fz1_105_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨29, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 29 (by decide)))

theorem fz1_105_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨30, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 30 (by decide)))

theorem fz1_105_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨31, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 31 (by decide)))

theorem fz1_105_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨32, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 32 (by decide)))

theorem fz1_105_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨33, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 33 (by decide)))

theorem fz1_105_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨34, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 34 (by decide)))

theorem fz1_105_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨35, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 35 (by decide)))

theorem fz1_105_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨36, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 36 (by decide)))

theorem fz1_105_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨37, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 37 (by decide)))

theorem fz1_105_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨38, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 38 (by decide)))

theorem fz1_105_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨39, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 39 (by decide)))

theorem fz1_105_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨40, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 40 (by decide)))

theorem fz1_105_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨41, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 41 (by decide)))

theorem fz1_105_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨42, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 42 (by decide)))

theorem fz1_105_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨44, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 44 (by decide)))

theorem fz1_105_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨45, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 45 (by decide)))

theorem fz1_105_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨46, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 46 (by decide)))

theorem fz1_105_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨47, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 47 (by decide)))

theorem fz1_105_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨48, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 48 (by decide)))

theorem fz1_105_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨49, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 49 (by decide)))

theorem fz1_105_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨50, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 50 (by decide)))

theorem fz1_105_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨51, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 51 (by decide)))

theorem fz1_105_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨52, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 52 (by decide)))

theorem fz1_105_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨54, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 54 (by decide)))

theorem fz1_105_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨55, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 55 (by decide)))

theorem fz1_105_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨56, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 56 (by decide)))

theorem fz1_105_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨57, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 57 (by decide)))

theorem fz1_105_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨58, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 58 (by decide)))

theorem fz1_105_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨59, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 59 (by decide)))

theorem fz1_105_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨60, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 60 (by decide)))

theorem fz1_105_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨61, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 61 (by decide)))

theorem fz1_105_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨62, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 62 (by decide)))

theorem fz1_105_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨63, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 63 (by decide)))

theorem fz1_105_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨64, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 64 (by decide)))

theorem fz1_105_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨65, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 65 (by decide)))

theorem fz1_105_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨66, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 66 (by decide)))

theorem fz1_105_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨67, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 67 (by decide)))

theorem fz1_105_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨68, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 68 (by decide)))

theorem fz1_105_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨69, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 69 (by decide)))

theorem fz1_105_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨70, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 70 (by decide)))

theorem fz1_105_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨71, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 71 (by decide)))

theorem fz1_105_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨72, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 72 (by decide)))

theorem fz1_105_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨73, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 73 (by decide)))

theorem fz1_105_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨74, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 74 (by decide)))

theorem fz1_105_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨75, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 75 (by decide)))

theorem fz1_105_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨76, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 76 (by decide)))

theorem fz1_105_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨77, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 77 (by decide)))

theorem fz1_105_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨78, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 78 (by decide)))

theorem fz1_105_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨79, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 79 (by decide)))

theorem fz1_105_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨80, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 80 (by decide)))

theorem fz1_105_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨81, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 81 (by decide)))

theorem fz1_105_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨82, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 82 (by decide)))

theorem fz1_105_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨83, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 83 (by decide)))

theorem fz1_105_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨84, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 84 (by decide)))

theorem fz1_105_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨85, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 85 (by decide)))

theorem fz1_105_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨86, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 86 (by decide)))

theorem fz1_105_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨87, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 87 (by decide)))

theorem fz1_105_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨88, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 88 (by decide)))

theorem fz1_105_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨89, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 89 (by decide)))

theorem fz1_105_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨90, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 90 (by decide)))

theorem fz1_105_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨91, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 91 (by decide)))

theorem fz1_105_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨92, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 92 (by decide)))

theorem fz1_105_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨93, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 93 (by decide)))

theorem fz1_105_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨94, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 94 (by decide)))

theorem fz1_105_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨95, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 95 (by decide)))

theorem fz1_105_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨96, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 96 (by decide)))

theorem fz1_105_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨97, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 97 (by decide)))

theorem fz1_105_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨98, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 98 (by decide)))

theorem fz1_105_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨99, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 99 (by decide)))

theorem fz1_105_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨100, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 100 (by decide)))

theorem fz1_105_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨101, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 101 (by decide)))

theorem fz1_105_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨102, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 102 (by decide)))

theorem fz1_105_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨103, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 103 (by decide)))

theorem fz1_105_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨104, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 104 (by decide)))

theorem fz1_105_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨106, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 106 (by decide)))

theorem fz1_105_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨107, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 107 (by decide)))

theorem fz1_105_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨108, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 108 (by decide)))

theorem fz1_105_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨109, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 109 (by decide)))

theorem fz1_105_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨110, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 110 (by decide)))

theorem fz1_105_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨111, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 111 (by decide)))

theorem fz1_105_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨112, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 112 (by decide)))

theorem fz1_105_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨113, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 113 (by decide)))

theorem fz1_105_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨114, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 114 (by decide)))

theorem fz1_105_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK105)) = 0 :=
  repsFixedCard rK105 ⟨115, by decide⟩ R105 hpxR105 hcardq105
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_105) 115 (by decide)))

theorem fixz2_105 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK105) (retConj 2 (Q2.R105_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_105_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨1, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 1 (by decide)))

theorem fz2_105_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨2, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 2 (by decide)))

theorem fz2_105_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨3, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 3 (by decide)))

theorem fz2_105_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨4, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 4 (by decide)))

theorem fz2_105_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨5, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 5 (by decide)))

theorem fz2_105_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨6, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 6 (by decide)))

theorem fz2_105_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨7, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 7 (by decide)))

theorem fz2_105_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨8, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 8 (by decide)))

theorem fz2_105_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨9, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 9 (by decide)))

theorem fz2_105_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨11, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 11 (by decide)))

theorem fz2_105_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨13, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 13 (by decide)))

theorem fz2_105_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨14, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 14 (by decide)))

theorem fz2_105_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨15, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 15 (by decide)))

theorem fz2_105_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨16, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 16 (by decide)))

theorem fz2_105_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨17, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 17 (by decide)))

theorem fz2_105_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨18, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 18 (by decide)))

theorem fz2_105_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨19, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 19 (by decide)))

theorem fz2_105_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨20, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 20 (by decide)))

theorem fz2_105_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨21, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 21 (by decide)))

theorem fz2_105_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨22, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 22 (by decide)))

theorem fz2_105_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨23, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 23 (by decide)))

theorem fz2_105_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨24, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 24 (by decide)))

theorem fz2_105_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨25, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 25 (by decide)))

theorem fz2_105_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨26, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 26 (by decide)))

theorem fz2_105_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨27, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 27 (by decide)))

theorem fz2_105_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨28, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 28 (by decide)))

theorem fz2_105_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨29, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 29 (by decide)))

theorem fz2_105_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨30, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 30 (by decide)))

theorem fz2_105_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨31, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 31 (by decide)))

theorem fz2_105_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨32, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 32 (by decide)))

theorem fz2_105_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨33, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 33 (by decide)))

theorem fz2_105_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨34, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 34 (by decide)))

theorem fz2_105_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨35, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 35 (by decide)))

theorem fz2_105_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨36, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 36 (by decide)))

theorem fz2_105_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨37, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 37 (by decide)))

theorem fz2_105_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨38, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 38 (by decide)))

theorem fz2_105_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨39, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 39 (by decide)))

theorem fz2_105_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨40, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 40 (by decide)))

theorem fz2_105_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨41, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 41 (by decide)))

theorem fz2_105_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨42, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 42 (by decide)))

theorem fz2_105_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨44, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 44 (by decide)))

theorem fz2_105_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨45, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 45 (by decide)))

theorem fz2_105_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨46, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 46 (by decide)))

theorem fz2_105_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨47, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 47 (by decide)))

theorem fz2_105_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨48, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 48 (by decide)))

theorem fz2_105_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨49, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 49 (by decide)))

theorem fz2_105_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨50, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 50 (by decide)))

theorem fz2_105_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨51, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 51 (by decide)))

theorem fz2_105_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨52, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 52 (by decide)))

theorem fz2_105_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨54, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 54 (by decide)))

theorem fz2_105_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨55, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 55 (by decide)))

theorem fz2_105_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨56, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 56 (by decide)))

theorem fz2_105_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨57, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 57 (by decide)))

theorem fz2_105_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨58, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 58 (by decide)))

theorem fz2_105_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨59, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 59 (by decide)))

theorem fz2_105_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨60, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 60 (by decide)))

theorem fz2_105_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨61, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 61 (by decide)))

theorem fz2_105_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨62, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 62 (by decide)))

theorem fz2_105_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨63, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 63 (by decide)))

theorem fz2_105_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨64, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 64 (by decide)))

theorem fz2_105_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨65, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 65 (by decide)))

theorem fz2_105_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨66, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 66 (by decide)))

theorem fz2_105_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨67, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 67 (by decide)))

theorem fz2_105_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨68, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 68 (by decide)))

theorem fz2_105_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨69, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 69 (by decide)))

theorem fz2_105_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨70, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 70 (by decide)))

theorem fz2_105_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨71, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 71 (by decide)))

theorem fz2_105_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨72, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 72 (by decide)))

theorem fz2_105_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨73, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 73 (by decide)))

theorem fz2_105_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨74, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 74 (by decide)))

theorem fz2_105_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨75, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 75 (by decide)))

theorem fz2_105_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨76, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 76 (by decide)))

theorem fz2_105_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨77, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 77 (by decide)))

theorem fz2_105_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨78, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 78 (by decide)))

theorem fz2_105_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨79, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 79 (by decide)))

theorem fz2_105_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨80, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 80 (by decide)))

theorem fz2_105_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨81, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 81 (by decide)))

theorem fz2_105_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨82, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 82 (by decide)))

theorem fz2_105_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨83, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 83 (by decide)))

theorem fz2_105_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨84, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 84 (by decide)))

theorem fz2_105_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨85, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 85 (by decide)))

theorem fz2_105_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨86, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 86 (by decide)))

theorem fz2_105_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨87, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 87 (by decide)))

theorem fz2_105_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨88, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 88 (by decide)))

theorem fz2_105_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨89, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 89 (by decide)))

theorem fz2_105_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨90, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 90 (by decide)))

theorem fz2_105_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨91, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 91 (by decide)))

theorem fz2_105_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨92, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 92 (by decide)))

theorem fz2_105_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨93, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 93 (by decide)))

theorem fz2_105_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨94, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 94 (by decide)))

theorem fz2_105_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨95, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 95 (by decide)))

theorem fz2_105_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨96, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 96 (by decide)))

theorem fz2_105_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨97, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 97 (by decide)))

theorem fz2_105_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨98, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 98 (by decide)))

theorem fz2_105_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨99, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 99 (by decide)))

theorem fz2_105_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨100, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 100 (by decide)))

theorem fz2_105_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨101, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 101 (by decide)))

theorem fz2_105_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨102, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 102 (by decide)))

theorem fz2_105_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨103, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 103 (by decide)))

theorem fz2_105_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨104, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 104 (by decide)))

theorem fz2_105_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨106, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 106 (by decide)))

theorem fz2_105_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨107, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 107 (by decide)))

theorem fz2_105_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨108, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 108 (by decide)))

theorem fz2_105_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨109, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 109 (by decide)))

theorem fz2_105_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨110, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 110 (by decide)))

theorem fz2_105_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨111, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 111 (by decide)))

theorem fz2_105_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨112, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 112 (by decide)))

theorem fz2_105_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨113, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 113 (by decide)))

theorem fz2_105_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨114, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 114 (by decide)))

theorem fz2_105_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK105)) = 0 :=
  Q2.repsFixedCard2 rK105 ⟨115, by decide⟩ Q2.R105_2 Q2.hpxR105_2 Q2.hcardq105_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_105) 115 (by decide)))

theorem fixz1_106 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK106) (retConj 1 (R106 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_106_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨1, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 1 (by decide)))

theorem fz1_106_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨2, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 2 (by decide)))

theorem fz1_106_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨3, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 3 (by decide)))

theorem fz1_106_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨4, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 4 (by decide)))

theorem fz1_106_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨5, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 5 (by decide)))

theorem fz1_106_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨6, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 6 (by decide)))

theorem fz1_106_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨7, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 7 (by decide)))

theorem fz1_106_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨8, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 8 (by decide)))

theorem fz1_106_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨9, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 9 (by decide)))

theorem fz1_106_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨11, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 11 (by decide)))

theorem fz1_106_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨13, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 13 (by decide)))

theorem fz1_106_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨14, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 14 (by decide)))

theorem fz1_106_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨15, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 15 (by decide)))

theorem fz1_106_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨16, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 16 (by decide)))

theorem fz1_106_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨17, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 17 (by decide)))

theorem fz1_106_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨18, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 18 (by decide)))

theorem fz1_106_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨19, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 19 (by decide)))

theorem fz1_106_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨20, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 20 (by decide)))

theorem fz1_106_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨21, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 21 (by decide)))

theorem fz1_106_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨22, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 22 (by decide)))

theorem fz1_106_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨23, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 23 (by decide)))

theorem fz1_106_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨24, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 24 (by decide)))

theorem fz1_106_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨25, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 25 (by decide)))

theorem fz1_106_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨26, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 26 (by decide)))

theorem fz1_106_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨27, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 27 (by decide)))

theorem fz1_106_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨28, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 28 (by decide)))

theorem fz1_106_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨29, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 29 (by decide)))

theorem fz1_106_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨30, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 30 (by decide)))

theorem fz1_106_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨31, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 31 (by decide)))

theorem fz1_106_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨32, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 32 (by decide)))

theorem fz1_106_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨33, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 33 (by decide)))

theorem fz1_106_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨34, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 34 (by decide)))

theorem fz1_106_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨35, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 35 (by decide)))

theorem fz1_106_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨36, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 36 (by decide)))

theorem fz1_106_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨37, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 37 (by decide)))

theorem fz1_106_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨38, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 38 (by decide)))

theorem fz1_106_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨39, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 39 (by decide)))

theorem fz1_106_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨40, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 40 (by decide)))

theorem fz1_106_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨41, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 41 (by decide)))

theorem fz1_106_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨42, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 42 (by decide)))

theorem fz1_106_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨43, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 43 (by decide)))

theorem fz1_106_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨45, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 45 (by decide)))

theorem fz1_106_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨46, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 46 (by decide)))

theorem fz1_106_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨47, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 47 (by decide)))

theorem fz1_106_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨48, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 48 (by decide)))

theorem fz1_106_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨49, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 49 (by decide)))

theorem fz1_106_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨50, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 50 (by decide)))

theorem fz1_106_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨51, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 51 (by decide)))

theorem fz1_106_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨52, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 52 (by decide)))

theorem fz1_106_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨54, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 54 (by decide)))

theorem fz1_106_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨55, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 55 (by decide)))

theorem fz1_106_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨56, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 56 (by decide)))

theorem fz1_106_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨57, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 57 (by decide)))

theorem fz1_106_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨58, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 58 (by decide)))

theorem fz1_106_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨59, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 59 (by decide)))

theorem fz1_106_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨60, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 60 (by decide)))

theorem fz1_106_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨61, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 61 (by decide)))

theorem fz1_106_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨62, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 62 (by decide)))

theorem fz1_106_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨63, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 63 (by decide)))

theorem fz1_106_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨64, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 64 (by decide)))

theorem fz1_106_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨65, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 65 (by decide)))

theorem fz1_106_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨66, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 66 (by decide)))

theorem fz1_106_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨67, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 67 (by decide)))

theorem fz1_106_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨68, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 68 (by decide)))

theorem fz1_106_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨69, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 69 (by decide)))

theorem fz1_106_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨70, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 70 (by decide)))

theorem fz1_106_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨71, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 71 (by decide)))

theorem fz1_106_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨72, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 72 (by decide)))

theorem fz1_106_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨73, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 73 (by decide)))

theorem fz1_106_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨74, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 74 (by decide)))

theorem fz1_106_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨75, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 75 (by decide)))

theorem fz1_106_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨76, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 76 (by decide)))

theorem fz1_106_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨77, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 77 (by decide)))

theorem fz1_106_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨78, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 78 (by decide)))

theorem fz1_106_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨79, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 79 (by decide)))

theorem fz1_106_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨80, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 80 (by decide)))

theorem fz1_106_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨81, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 81 (by decide)))

theorem fz1_106_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨82, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 82 (by decide)))

theorem fz1_106_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨83, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 83 (by decide)))

theorem fz1_106_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨84, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 84 (by decide)))

theorem fz1_106_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨85, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 85 (by decide)))

theorem fz1_106_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨86, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 86 (by decide)))

theorem fz1_106_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨87, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 87 (by decide)))

theorem fz1_106_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨88, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 88 (by decide)))

theorem fz1_106_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨89, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 89 (by decide)))

theorem fz1_106_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨90, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 90 (by decide)))

theorem fz1_106_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨91, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 91 (by decide)))

theorem fz1_106_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨92, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 92 (by decide)))

theorem fz1_106_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨93, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 93 (by decide)))

theorem fz1_106_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨94, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 94 (by decide)))

theorem fz1_106_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨95, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 95 (by decide)))

theorem fz1_106_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨96, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 96 (by decide)))

theorem fz1_106_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨97, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 97 (by decide)))

theorem fz1_106_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨98, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 98 (by decide)))

theorem fz1_106_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨99, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 99 (by decide)))

theorem fz1_106_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨100, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 100 (by decide)))

theorem fz1_106_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨101, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 101 (by decide)))

theorem fz1_106_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨102, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 102 (by decide)))

theorem fz1_106_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨103, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 103 (by decide)))

theorem fz1_106_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨104, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 104 (by decide)))

theorem fz1_106_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨105, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 105 (by decide)))

theorem fz1_106_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨107, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 107 (by decide)))

theorem fz1_106_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨108, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 108 (by decide)))

theorem fz1_106_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨109, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 109 (by decide)))

theorem fz1_106_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨110, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 110 (by decide)))

theorem fz1_106_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨111, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 111 (by decide)))

theorem fz1_106_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨112, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 112 (by decide)))

theorem fz1_106_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨113, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 113 (by decide)))

theorem fz1_106_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨114, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 114 (by decide)))

theorem fz1_106_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK106)) = 0 :=
  repsFixedCard rK106 ⟨115, by decide⟩ R106 hpxR106 hcardq106
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_106) 115 (by decide)))

theorem fixz2_106 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK106) (retConj 2 (Q2.R106_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_106_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨1, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 1 (by decide)))

theorem fz2_106_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨2, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 2 (by decide)))

theorem fz2_106_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨3, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 3 (by decide)))

theorem fz2_106_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨4, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 4 (by decide)))

theorem fz2_106_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨5, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 5 (by decide)))

theorem fz2_106_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨6, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 6 (by decide)))

theorem fz2_106_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨7, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 7 (by decide)))

theorem fz2_106_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨8, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 8 (by decide)))

theorem fz2_106_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨9, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 9 (by decide)))

theorem fz2_106_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨11, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 11 (by decide)))

theorem fz2_106_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨13, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 13 (by decide)))

theorem fz2_106_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨14, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 14 (by decide)))

theorem fz2_106_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨15, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 15 (by decide)))

theorem fz2_106_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨16, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 16 (by decide)))

theorem fz2_106_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨17, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 17 (by decide)))

theorem fz2_106_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨18, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 18 (by decide)))

theorem fz2_106_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨19, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 19 (by decide)))

theorem fz2_106_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨20, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 20 (by decide)))

theorem fz2_106_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨21, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 21 (by decide)))

theorem fz2_106_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨22, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 22 (by decide)))

theorem fz2_106_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨23, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 23 (by decide)))

theorem fz2_106_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨24, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 24 (by decide)))

theorem fz2_106_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨25, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 25 (by decide)))

theorem fz2_106_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨26, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 26 (by decide)))

theorem fz2_106_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨27, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 27 (by decide)))

theorem fz2_106_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨28, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 28 (by decide)))

theorem fz2_106_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨29, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 29 (by decide)))

theorem fz2_106_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨30, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 30 (by decide)))

theorem fz2_106_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨31, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 31 (by decide)))

theorem fz2_106_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨32, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 32 (by decide)))

theorem fz2_106_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨33, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 33 (by decide)))

theorem fz2_106_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨34, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 34 (by decide)))

theorem fz2_106_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨35, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 35 (by decide)))

theorem fz2_106_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨36, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 36 (by decide)))

theorem fz2_106_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨37, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 37 (by decide)))

theorem fz2_106_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨38, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 38 (by decide)))

theorem fz2_106_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨39, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 39 (by decide)))

theorem fz2_106_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨40, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 40 (by decide)))

theorem fz2_106_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨41, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 41 (by decide)))

theorem fz2_106_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨42, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 42 (by decide)))

theorem fz2_106_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨43, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 43 (by decide)))

theorem fz2_106_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨45, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 45 (by decide)))

theorem fz2_106_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨46, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 46 (by decide)))

theorem fz2_106_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨47, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 47 (by decide)))

theorem fz2_106_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨48, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 48 (by decide)))

theorem fz2_106_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨49, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 49 (by decide)))

theorem fz2_106_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨50, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 50 (by decide)))

theorem fz2_106_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨51, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 51 (by decide)))

theorem fz2_106_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨52, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 52 (by decide)))

theorem fz2_106_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨54, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 54 (by decide)))

theorem fz2_106_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨55, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 55 (by decide)))

theorem fz2_106_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨56, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 56 (by decide)))

theorem fz2_106_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨57, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 57 (by decide)))

theorem fz2_106_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨58, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 58 (by decide)))

theorem fz2_106_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨59, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 59 (by decide)))

theorem fz2_106_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨60, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 60 (by decide)))

theorem fz2_106_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨61, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 61 (by decide)))

theorem fz2_106_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨62, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 62 (by decide)))

theorem fz2_106_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨63, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 63 (by decide)))

theorem fz2_106_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨64, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 64 (by decide)))

theorem fz2_106_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨65, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 65 (by decide)))

theorem fz2_106_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨66, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 66 (by decide)))

theorem fz2_106_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨67, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 67 (by decide)))

theorem fz2_106_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨68, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 68 (by decide)))

theorem fz2_106_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨69, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 69 (by decide)))

theorem fz2_106_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨70, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 70 (by decide)))

theorem fz2_106_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨71, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 71 (by decide)))

theorem fz2_106_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨72, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 72 (by decide)))

theorem fz2_106_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨73, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 73 (by decide)))

theorem fz2_106_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨74, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 74 (by decide)))

theorem fz2_106_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨75, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 75 (by decide)))

theorem fz2_106_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨76, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 76 (by decide)))

theorem fz2_106_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨77, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 77 (by decide)))

theorem fz2_106_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨78, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 78 (by decide)))

theorem fz2_106_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨79, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 79 (by decide)))

theorem fz2_106_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨80, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 80 (by decide)))

theorem fz2_106_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨81, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 81 (by decide)))

theorem fz2_106_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨82, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 82 (by decide)))

theorem fz2_106_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨83, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 83 (by decide)))

theorem fz2_106_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨84, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 84 (by decide)))

theorem fz2_106_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨85, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 85 (by decide)))

theorem fz2_106_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨86, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 86 (by decide)))

theorem fz2_106_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨87, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 87 (by decide)))

theorem fz2_106_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨88, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 88 (by decide)))

theorem fz2_106_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨89, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 89 (by decide)))

theorem fz2_106_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨90, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 90 (by decide)))

theorem fz2_106_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨91, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 91 (by decide)))

theorem fz2_106_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨92, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 92 (by decide)))

theorem fz2_106_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨93, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 93 (by decide)))

theorem fz2_106_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨94, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 94 (by decide)))

theorem fz2_106_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨95, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 95 (by decide)))

theorem fz2_106_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨96, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 96 (by decide)))

theorem fz2_106_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨97, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 97 (by decide)))

theorem fz2_106_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨98, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 98 (by decide)))

theorem fz2_106_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨99, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 99 (by decide)))

theorem fz2_106_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨100, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 100 (by decide)))

theorem fz2_106_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨101, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 101 (by decide)))

theorem fz2_106_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨102, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 102 (by decide)))

theorem fz2_106_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨103, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 103 (by decide)))

theorem fz2_106_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨104, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 104 (by decide)))

theorem fz2_106_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨105, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 105 (by decide)))

theorem fz2_106_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨107, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 107 (by decide)))

theorem fz2_106_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨108, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 108 (by decide)))

theorem fz2_106_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨109, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 109 (by decide)))

theorem fz2_106_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨110, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 110 (by decide)))

theorem fz2_106_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨111, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 111 (by decide)))

theorem fz2_106_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨112, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 112 (by decide)))

theorem fz2_106_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨113, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 113 (by decide)))

theorem fz2_106_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨114, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 114 (by decide)))

theorem fz2_106_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK106)) = 0 :=
  Q2.repsFixedCard2 rK106 ⟨115, by decide⟩ Q2.R106_2 Q2.hpxR106_2 Q2.hcardq106_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_106) 115 (by decide)))

end LeanDring.P5Presentation
