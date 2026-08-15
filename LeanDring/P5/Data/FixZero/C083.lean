/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C024

/-!
# Species-table cells, off-support emptiness certificates, chunk 82

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

theorem fixz1_111 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK111) (retConj 1 (R111 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_111_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨1, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 1 (by decide)))

theorem fz1_111_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨2, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 2 (by decide)))

theorem fz1_111_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨3, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 3 (by decide)))

theorem fz1_111_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨4, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 4 (by decide)))

theorem fz1_111_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨5, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 5 (by decide)))

theorem fz1_111_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨6, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 6 (by decide)))

theorem fz1_111_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨7, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 7 (by decide)))

theorem fz1_111_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨8, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 8 (by decide)))

theorem fz1_111_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨9, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 9 (by decide)))

theorem fz1_111_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨11, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 11 (by decide)))

theorem fz1_111_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨13, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 13 (by decide)))

theorem fz1_111_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨14, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 14 (by decide)))

theorem fz1_111_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨15, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 15 (by decide)))

theorem fz1_111_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨16, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 16 (by decide)))

theorem fz1_111_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨17, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 17 (by decide)))

theorem fz1_111_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨18, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 18 (by decide)))

theorem fz1_111_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨19, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 19 (by decide)))

theorem fz1_111_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨20, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 20 (by decide)))

theorem fz1_111_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨21, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 21 (by decide)))

theorem fz1_111_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨22, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 22 (by decide)))

theorem fz1_111_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨23, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 23 (by decide)))

theorem fz1_111_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨24, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 24 (by decide)))

theorem fz1_111_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨25, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 25 (by decide)))

theorem fz1_111_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨26, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 26 (by decide)))

theorem fz1_111_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨27, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 27 (by decide)))

theorem fz1_111_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨28, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 28 (by decide)))

theorem fz1_111_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨29, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 29 (by decide)))

theorem fz1_111_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨30, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 30 (by decide)))

theorem fz1_111_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨31, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 31 (by decide)))

theorem fz1_111_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨32, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 32 (by decide)))

theorem fz1_111_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨33, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 33 (by decide)))

theorem fz1_111_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨34, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 34 (by decide)))

theorem fz1_111_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨35, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 35 (by decide)))

theorem fz1_111_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨36, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 36 (by decide)))

theorem fz1_111_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨37, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 37 (by decide)))

theorem fz1_111_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨38, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 38 (by decide)))

theorem fz1_111_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨39, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 39 (by decide)))

theorem fz1_111_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨40, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 40 (by decide)))

theorem fz1_111_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨41, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 41 (by decide)))

theorem fz1_111_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨42, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 42 (by decide)))

theorem fz1_111_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨43, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 43 (by decide)))

theorem fz1_111_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨44, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 44 (by decide)))

theorem fz1_111_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨45, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 45 (by decide)))

theorem fz1_111_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨46, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 46 (by decide)))

theorem fz1_111_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨47, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 47 (by decide)))

theorem fz1_111_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨48, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 48 (by decide)))

theorem fz1_111_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨50, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 50 (by decide)))

theorem fz1_111_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨51, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 51 (by decide)))

theorem fz1_111_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨52, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 52 (by decide)))

theorem fz1_111_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨54, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 54 (by decide)))

theorem fz1_111_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨55, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 55 (by decide)))

theorem fz1_111_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨56, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 56 (by decide)))

theorem fz1_111_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨57, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 57 (by decide)))

theorem fz1_111_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨58, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 58 (by decide)))

theorem fz1_111_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨59, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 59 (by decide)))

theorem fz1_111_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨60, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 60 (by decide)))

theorem fz1_111_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨61, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 61 (by decide)))

theorem fz1_111_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨62, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 62 (by decide)))

theorem fz1_111_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨63, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 63 (by decide)))

theorem fz1_111_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨64, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 64 (by decide)))

theorem fz1_111_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨65, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 65 (by decide)))

theorem fz1_111_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨66, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 66 (by decide)))

theorem fz1_111_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨67, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 67 (by decide)))

theorem fz1_111_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨68, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 68 (by decide)))

theorem fz1_111_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨69, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 69 (by decide)))

theorem fz1_111_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨70, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 70 (by decide)))

theorem fz1_111_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨71, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 71 (by decide)))

theorem fz1_111_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨72, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 72 (by decide)))

theorem fz1_111_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨73, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 73 (by decide)))

theorem fz1_111_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨74, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 74 (by decide)))

theorem fz1_111_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨75, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 75 (by decide)))

theorem fz1_111_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨76, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 76 (by decide)))

theorem fz1_111_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨77, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 77 (by decide)))

theorem fz1_111_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨78, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 78 (by decide)))

theorem fz1_111_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨79, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 79 (by decide)))

theorem fz1_111_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨80, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 80 (by decide)))

theorem fz1_111_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨81, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 81 (by decide)))

theorem fz1_111_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨82, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 82 (by decide)))

theorem fz1_111_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨83, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 83 (by decide)))

theorem fz1_111_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨84, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 84 (by decide)))

theorem fz1_111_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨85, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 85 (by decide)))

theorem fz1_111_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨86, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 86 (by decide)))

theorem fz1_111_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨87, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 87 (by decide)))

theorem fz1_111_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨88, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 88 (by decide)))

theorem fz1_111_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨89, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 89 (by decide)))

theorem fz1_111_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨90, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 90 (by decide)))

theorem fz1_111_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨91, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 91 (by decide)))

theorem fz1_111_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨92, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 92 (by decide)))

theorem fz1_111_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨93, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 93 (by decide)))

theorem fz1_111_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨94, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 94 (by decide)))

theorem fz1_111_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨95, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 95 (by decide)))

theorem fz1_111_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨96, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 96 (by decide)))

theorem fz1_111_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨97, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 97 (by decide)))

theorem fz1_111_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨98, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 98 (by decide)))

theorem fz1_111_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨99, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 99 (by decide)))

theorem fz1_111_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨100, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 100 (by decide)))

theorem fz1_111_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨101, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 101 (by decide)))

theorem fz1_111_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨102, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 102 (by decide)))

theorem fz1_111_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨103, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 103 (by decide)))

theorem fz1_111_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨104, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 104 (by decide)))

theorem fz1_111_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨105, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 105 (by decide)))

theorem fz1_111_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨106, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 106 (by decide)))

theorem fz1_111_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨107, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 107 (by decide)))

theorem fz1_111_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨108, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 108 (by decide)))

theorem fz1_111_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨109, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 109 (by decide)))

theorem fz1_111_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨110, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 110 (by decide)))

theorem fz1_111_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨112, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 112 (by decide)))

theorem fz1_111_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨113, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 113 (by decide)))

theorem fz1_111_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨114, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 114 (by decide)))

theorem fz1_111_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK111)) = 0 :=
  repsFixedCard rK111 ⟨115, by decide⟩ R111 hpxR111 hcardq111
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_111) 115 (by decide)))

theorem fixz2_111 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK111) (retConj 2 (Q2.R111_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_111_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨1, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 1 (by decide)))

theorem fz2_111_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨2, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 2 (by decide)))

theorem fz2_111_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨3, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 3 (by decide)))

theorem fz2_111_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨4, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 4 (by decide)))

theorem fz2_111_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨5, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 5 (by decide)))

theorem fz2_111_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨6, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 6 (by decide)))

theorem fz2_111_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨7, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 7 (by decide)))

theorem fz2_111_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨8, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 8 (by decide)))

theorem fz2_111_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨9, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 9 (by decide)))

theorem fz2_111_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨11, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 11 (by decide)))

theorem fz2_111_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨13, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 13 (by decide)))

theorem fz2_111_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨14, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 14 (by decide)))

theorem fz2_111_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨15, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 15 (by decide)))

theorem fz2_111_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨16, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 16 (by decide)))

theorem fz2_111_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨17, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 17 (by decide)))

theorem fz2_111_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨18, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 18 (by decide)))

theorem fz2_111_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨19, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 19 (by decide)))

theorem fz2_111_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨20, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 20 (by decide)))

theorem fz2_111_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨21, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 21 (by decide)))

theorem fz2_111_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨22, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 22 (by decide)))

theorem fz2_111_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨23, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 23 (by decide)))

theorem fz2_111_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨24, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 24 (by decide)))

theorem fz2_111_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨25, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 25 (by decide)))

theorem fz2_111_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨26, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 26 (by decide)))

theorem fz2_111_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨27, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 27 (by decide)))

theorem fz2_111_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨28, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 28 (by decide)))

theorem fz2_111_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨29, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 29 (by decide)))

theorem fz2_111_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨30, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 30 (by decide)))

theorem fz2_111_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨31, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 31 (by decide)))

theorem fz2_111_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨32, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 32 (by decide)))

theorem fz2_111_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨33, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 33 (by decide)))

theorem fz2_111_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨34, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 34 (by decide)))

theorem fz2_111_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨35, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 35 (by decide)))

theorem fz2_111_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨36, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 36 (by decide)))

theorem fz2_111_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨37, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 37 (by decide)))

theorem fz2_111_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨38, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 38 (by decide)))

theorem fz2_111_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨39, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 39 (by decide)))

theorem fz2_111_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨40, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 40 (by decide)))

theorem fz2_111_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨41, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 41 (by decide)))

theorem fz2_111_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨42, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 42 (by decide)))

theorem fz2_111_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨43, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 43 (by decide)))

theorem fz2_111_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨44, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 44 (by decide)))

theorem fz2_111_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨45, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 45 (by decide)))

theorem fz2_111_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨46, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 46 (by decide)))

theorem fz2_111_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨47, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 47 (by decide)))

theorem fz2_111_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨48, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 48 (by decide)))

theorem fz2_111_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨50, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 50 (by decide)))

theorem fz2_111_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨51, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 51 (by decide)))

theorem fz2_111_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨52, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 52 (by decide)))

theorem fz2_111_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨54, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 54 (by decide)))

theorem fz2_111_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨55, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 55 (by decide)))

theorem fz2_111_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨56, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 56 (by decide)))

theorem fz2_111_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨57, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 57 (by decide)))

theorem fz2_111_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨58, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 58 (by decide)))

theorem fz2_111_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨59, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 59 (by decide)))

theorem fz2_111_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨60, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 60 (by decide)))

theorem fz2_111_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨61, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 61 (by decide)))

theorem fz2_111_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨62, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 62 (by decide)))

theorem fz2_111_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨63, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 63 (by decide)))

theorem fz2_111_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨64, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 64 (by decide)))

theorem fz2_111_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨65, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 65 (by decide)))

theorem fz2_111_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨66, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 66 (by decide)))

theorem fz2_111_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨67, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 67 (by decide)))

theorem fz2_111_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨68, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 68 (by decide)))

theorem fz2_111_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨69, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 69 (by decide)))

theorem fz2_111_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨70, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 70 (by decide)))

theorem fz2_111_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨71, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 71 (by decide)))

theorem fz2_111_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨72, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 72 (by decide)))

theorem fz2_111_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨73, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 73 (by decide)))

theorem fz2_111_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨74, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 74 (by decide)))

theorem fz2_111_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨75, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 75 (by decide)))

theorem fz2_111_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨76, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 76 (by decide)))

theorem fz2_111_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨77, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 77 (by decide)))

theorem fz2_111_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨78, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 78 (by decide)))

theorem fz2_111_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨79, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 79 (by decide)))

theorem fz2_111_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨80, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 80 (by decide)))

theorem fz2_111_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨81, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 81 (by decide)))

theorem fz2_111_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨82, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 82 (by decide)))

theorem fz2_111_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨83, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 83 (by decide)))

theorem fz2_111_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨84, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 84 (by decide)))

theorem fz2_111_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨85, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 85 (by decide)))

theorem fz2_111_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨86, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 86 (by decide)))

theorem fz2_111_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨87, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 87 (by decide)))

theorem fz2_111_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨88, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 88 (by decide)))

theorem fz2_111_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨89, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 89 (by decide)))

theorem fz2_111_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨90, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 90 (by decide)))

theorem fz2_111_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨91, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 91 (by decide)))

theorem fz2_111_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨92, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 92 (by decide)))

theorem fz2_111_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨93, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 93 (by decide)))

theorem fz2_111_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨94, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 94 (by decide)))

theorem fz2_111_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨95, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 95 (by decide)))

theorem fz2_111_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨96, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 96 (by decide)))

theorem fz2_111_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨97, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 97 (by decide)))

theorem fz2_111_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨98, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 98 (by decide)))

theorem fz2_111_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨99, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 99 (by decide)))

theorem fz2_111_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨100, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 100 (by decide)))

theorem fz2_111_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨101, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 101 (by decide)))

theorem fz2_111_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨102, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 102 (by decide)))

theorem fz2_111_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨103, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 103 (by decide)))

theorem fz2_111_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨104, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 104 (by decide)))

theorem fz2_111_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨105, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 105 (by decide)))

theorem fz2_111_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨106, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 106 (by decide)))

theorem fz2_111_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨107, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 107 (by decide)))

theorem fz2_111_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨108, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 108 (by decide)))

theorem fz2_111_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨109, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 109 (by decide)))

theorem fz2_111_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨110, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 110 (by decide)))

theorem fz2_111_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨112, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 112 (by decide)))

theorem fz2_111_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨113, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 113 (by decide)))

theorem fz2_111_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨114, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 114 (by decide)))

theorem fz2_111_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK111)) = 0 :=
  Q2.repsFixedCard2 rK111 ⟨115, by decide⟩ Q2.R111_2 Q2.hpxR111_2 Q2.hcardq111_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_111) 115 (by decide)))

theorem fixz1_112 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK112) (retConj 1 (R112 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_112_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨1, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 1 (by decide)))

theorem fz1_112_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨2, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 2 (by decide)))

theorem fz1_112_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨3, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 3 (by decide)))

theorem fz1_112_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨4, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 4 (by decide)))

theorem fz1_112_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨5, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 5 (by decide)))

theorem fz1_112_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨6, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 6 (by decide)))

theorem fz1_112_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨7, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 7 (by decide)))

theorem fz1_112_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨8, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 8 (by decide)))

theorem fz1_112_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨9, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 9 (by decide)))

theorem fz1_112_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨11, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 11 (by decide)))

theorem fz1_112_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨13, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 13 (by decide)))

theorem fz1_112_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨14, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 14 (by decide)))

theorem fz1_112_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨15, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 15 (by decide)))

theorem fz1_112_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨16, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 16 (by decide)))

theorem fz1_112_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨17, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 17 (by decide)))

theorem fz1_112_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨18, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 18 (by decide)))

theorem fz1_112_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨19, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 19 (by decide)))

theorem fz1_112_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨20, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 20 (by decide)))

theorem fz1_112_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨21, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 21 (by decide)))

theorem fz1_112_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨22, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 22 (by decide)))

theorem fz1_112_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨23, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 23 (by decide)))

theorem fz1_112_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨24, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 24 (by decide)))

theorem fz1_112_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨25, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 25 (by decide)))

theorem fz1_112_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨26, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 26 (by decide)))

theorem fz1_112_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨27, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 27 (by decide)))

theorem fz1_112_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨28, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 28 (by decide)))

theorem fz1_112_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨29, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 29 (by decide)))

theorem fz1_112_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨30, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 30 (by decide)))

theorem fz1_112_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨31, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 31 (by decide)))

theorem fz1_112_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨32, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 32 (by decide)))

theorem fz1_112_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨33, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 33 (by decide)))

theorem fz1_112_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨34, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 34 (by decide)))

theorem fz1_112_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨35, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 35 (by decide)))

theorem fz1_112_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨36, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 36 (by decide)))

theorem fz1_112_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨37, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 37 (by decide)))

theorem fz1_112_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨38, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 38 (by decide)))

theorem fz1_112_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨39, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 39 (by decide)))

theorem fz1_112_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨40, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 40 (by decide)))

theorem fz1_112_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨41, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 41 (by decide)))

theorem fz1_112_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨42, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 42 (by decide)))

theorem fz1_112_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨43, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 43 (by decide)))

theorem fz1_112_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨44, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 44 (by decide)))

theorem fz1_112_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨45, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 45 (by decide)))

theorem fz1_112_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨46, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 46 (by decide)))

theorem fz1_112_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨47, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 47 (by decide)))

theorem fz1_112_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨48, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 48 (by decide)))

theorem fz1_112_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨49, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 49 (by decide)))

theorem fz1_112_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨51, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 51 (by decide)))

theorem fz1_112_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨52, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 52 (by decide)))

theorem fz1_112_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨54, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 54 (by decide)))

theorem fz1_112_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨55, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 55 (by decide)))

theorem fz1_112_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨56, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 56 (by decide)))

theorem fz1_112_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨57, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 57 (by decide)))

theorem fz1_112_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨58, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 58 (by decide)))

theorem fz1_112_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨59, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 59 (by decide)))

theorem fz1_112_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨60, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 60 (by decide)))

theorem fz1_112_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨61, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 61 (by decide)))

theorem fz1_112_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨62, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 62 (by decide)))

theorem fz1_112_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨63, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 63 (by decide)))

theorem fz1_112_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨64, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 64 (by decide)))

theorem fz1_112_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨65, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 65 (by decide)))

theorem fz1_112_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨66, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 66 (by decide)))

theorem fz1_112_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨67, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 67 (by decide)))

theorem fz1_112_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨68, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 68 (by decide)))

theorem fz1_112_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨69, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 69 (by decide)))

theorem fz1_112_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨70, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 70 (by decide)))

theorem fz1_112_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨71, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 71 (by decide)))

theorem fz1_112_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨72, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 72 (by decide)))

theorem fz1_112_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨73, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 73 (by decide)))

theorem fz1_112_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨74, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 74 (by decide)))

theorem fz1_112_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨75, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 75 (by decide)))

theorem fz1_112_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨76, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 76 (by decide)))

theorem fz1_112_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨77, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 77 (by decide)))

theorem fz1_112_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨78, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 78 (by decide)))

theorem fz1_112_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨79, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 79 (by decide)))

theorem fz1_112_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨80, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 80 (by decide)))

theorem fz1_112_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨81, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 81 (by decide)))

theorem fz1_112_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨82, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 82 (by decide)))

theorem fz1_112_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨83, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 83 (by decide)))

theorem fz1_112_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨84, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 84 (by decide)))

theorem fz1_112_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨85, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 85 (by decide)))

theorem fz1_112_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨86, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 86 (by decide)))

theorem fz1_112_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨87, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 87 (by decide)))

theorem fz1_112_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨88, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 88 (by decide)))

theorem fz1_112_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨89, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 89 (by decide)))

theorem fz1_112_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨90, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 90 (by decide)))

theorem fz1_112_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨91, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 91 (by decide)))

theorem fz1_112_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨92, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 92 (by decide)))

theorem fz1_112_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨93, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 93 (by decide)))

theorem fz1_112_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨94, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 94 (by decide)))

theorem fz1_112_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨95, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 95 (by decide)))

theorem fz1_112_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨96, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 96 (by decide)))

theorem fz1_112_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨97, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 97 (by decide)))

theorem fz1_112_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨98, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 98 (by decide)))

theorem fz1_112_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨99, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 99 (by decide)))

theorem fz1_112_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨100, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 100 (by decide)))

theorem fz1_112_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨101, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 101 (by decide)))

theorem fz1_112_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨102, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 102 (by decide)))

theorem fz1_112_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨103, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 103 (by decide)))

theorem fz1_112_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨104, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 104 (by decide)))

theorem fz1_112_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨105, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 105 (by decide)))

theorem fz1_112_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨106, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 106 (by decide)))

theorem fz1_112_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨107, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 107 (by decide)))

theorem fz1_112_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨108, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 108 (by decide)))

theorem fz1_112_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨109, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 109 (by decide)))

theorem fz1_112_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨110, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 110 (by decide)))

theorem fz1_112_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨111, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 111 (by decide)))

theorem fz1_112_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨113, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 113 (by decide)))

theorem fz1_112_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨114, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 114 (by decide)))

theorem fz1_112_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK112)) = 0 :=
  repsFixedCard rK112 ⟨115, by decide⟩ R112 hpxR112 hcardq112
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_112) 115 (by decide)))

theorem fixz2_112 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK112) (retConj 2 (Q2.R112_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_112_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨1, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 1 (by decide)))

theorem fz2_112_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨2, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 2 (by decide)))

theorem fz2_112_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨3, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 3 (by decide)))

theorem fz2_112_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨4, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 4 (by decide)))

theorem fz2_112_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨5, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 5 (by decide)))

theorem fz2_112_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨6, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 6 (by decide)))

theorem fz2_112_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨7, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 7 (by decide)))

theorem fz2_112_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨8, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 8 (by decide)))

theorem fz2_112_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨9, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 9 (by decide)))

theorem fz2_112_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨11, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 11 (by decide)))

theorem fz2_112_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨13, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 13 (by decide)))

theorem fz2_112_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨14, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 14 (by decide)))

theorem fz2_112_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨15, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 15 (by decide)))

theorem fz2_112_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨16, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 16 (by decide)))

theorem fz2_112_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨17, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 17 (by decide)))

theorem fz2_112_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨18, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 18 (by decide)))

theorem fz2_112_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨19, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 19 (by decide)))

theorem fz2_112_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨20, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 20 (by decide)))

theorem fz2_112_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨21, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 21 (by decide)))

theorem fz2_112_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨22, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 22 (by decide)))

theorem fz2_112_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨23, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 23 (by decide)))

theorem fz2_112_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨24, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 24 (by decide)))

theorem fz2_112_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨25, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 25 (by decide)))

theorem fz2_112_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨26, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 26 (by decide)))

theorem fz2_112_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨27, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 27 (by decide)))

theorem fz2_112_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨28, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 28 (by decide)))

theorem fz2_112_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨29, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 29 (by decide)))

theorem fz2_112_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨30, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 30 (by decide)))

theorem fz2_112_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨31, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 31 (by decide)))

theorem fz2_112_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨32, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 32 (by decide)))

theorem fz2_112_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨33, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 33 (by decide)))

theorem fz2_112_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨34, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 34 (by decide)))

theorem fz2_112_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨35, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 35 (by decide)))

theorem fz2_112_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨36, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 36 (by decide)))

theorem fz2_112_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨37, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 37 (by decide)))

theorem fz2_112_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨38, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 38 (by decide)))

theorem fz2_112_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨39, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 39 (by decide)))

theorem fz2_112_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨40, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 40 (by decide)))

theorem fz2_112_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨41, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 41 (by decide)))

theorem fz2_112_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨42, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 42 (by decide)))

theorem fz2_112_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨43, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 43 (by decide)))

theorem fz2_112_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨44, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 44 (by decide)))

theorem fz2_112_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨45, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 45 (by decide)))

theorem fz2_112_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨46, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 46 (by decide)))

theorem fz2_112_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨47, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 47 (by decide)))

theorem fz2_112_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨48, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 48 (by decide)))

theorem fz2_112_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨49, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 49 (by decide)))

theorem fz2_112_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨51, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 51 (by decide)))

theorem fz2_112_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨52, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 52 (by decide)))

theorem fz2_112_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨54, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 54 (by decide)))

theorem fz2_112_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨55, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 55 (by decide)))

theorem fz2_112_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨56, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 56 (by decide)))

theorem fz2_112_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨57, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 57 (by decide)))

theorem fz2_112_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨58, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 58 (by decide)))

theorem fz2_112_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨59, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 59 (by decide)))

theorem fz2_112_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨60, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 60 (by decide)))

theorem fz2_112_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨61, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 61 (by decide)))

theorem fz2_112_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨62, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 62 (by decide)))

theorem fz2_112_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨63, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 63 (by decide)))

theorem fz2_112_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨64, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 64 (by decide)))

theorem fz2_112_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨65, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 65 (by decide)))

theorem fz2_112_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨66, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 66 (by decide)))

theorem fz2_112_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨67, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 67 (by decide)))

theorem fz2_112_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨68, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 68 (by decide)))

theorem fz2_112_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨69, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 69 (by decide)))

theorem fz2_112_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨70, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 70 (by decide)))

theorem fz2_112_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨71, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 71 (by decide)))

theorem fz2_112_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨72, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 72 (by decide)))

theorem fz2_112_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨73, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 73 (by decide)))

theorem fz2_112_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨74, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 74 (by decide)))

theorem fz2_112_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨75, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 75 (by decide)))

theorem fz2_112_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨76, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 76 (by decide)))

theorem fz2_112_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨77, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 77 (by decide)))

theorem fz2_112_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨78, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 78 (by decide)))

theorem fz2_112_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨79, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 79 (by decide)))

theorem fz2_112_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨80, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 80 (by decide)))

theorem fz2_112_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨81, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 81 (by decide)))

theorem fz2_112_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨82, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 82 (by decide)))

theorem fz2_112_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨83, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 83 (by decide)))

theorem fz2_112_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨84, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 84 (by decide)))

theorem fz2_112_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨85, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 85 (by decide)))

theorem fz2_112_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨86, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 86 (by decide)))

theorem fz2_112_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨87, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 87 (by decide)))

theorem fz2_112_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨88, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 88 (by decide)))

theorem fz2_112_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨89, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 89 (by decide)))

theorem fz2_112_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨90, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 90 (by decide)))

theorem fz2_112_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨91, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 91 (by decide)))

theorem fz2_112_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨92, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 92 (by decide)))

theorem fz2_112_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨93, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 93 (by decide)))

theorem fz2_112_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨94, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 94 (by decide)))

theorem fz2_112_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨95, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 95 (by decide)))

theorem fz2_112_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨96, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 96 (by decide)))

theorem fz2_112_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨97, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 97 (by decide)))

theorem fz2_112_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨98, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 98 (by decide)))

theorem fz2_112_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨99, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 99 (by decide)))

theorem fz2_112_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨100, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 100 (by decide)))

theorem fz2_112_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨101, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 101 (by decide)))

theorem fz2_112_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨102, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 102 (by decide)))

theorem fz2_112_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨103, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 103 (by decide)))

theorem fz2_112_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨104, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 104 (by decide)))

theorem fz2_112_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨105, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 105 (by decide)))

theorem fz2_112_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨106, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 106 (by decide)))

theorem fz2_112_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨107, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 107 (by decide)))

theorem fz2_112_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨108, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 108 (by decide)))

theorem fz2_112_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨109, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 109 (by decide)))

theorem fz2_112_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨110, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 110 (by decide)))

theorem fz2_112_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨111, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 111 (by decide)))

theorem fz2_112_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨113, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 113 (by decide)))

theorem fz2_112_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨114, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 114 (by decide)))

theorem fz2_112_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK112)) = 0 :=
  Q2.repsFixedCard2 rK112 ⟨115, by decide⟩ Q2.R112_2 Q2.hpxR112_2 Q2.hcardq112_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_112) 115 (by decide)))

end LeanDring.P5Presentation
