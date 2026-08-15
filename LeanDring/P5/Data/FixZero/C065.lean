/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C018

/-!
# Species-table cells, off-support emptiness certificates, chunk 64

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

theorem fixz1_75 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK75) (retConj 1 (R75 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_75_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨1, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 1 (by decide)))

theorem fz1_75_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨2, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 2 (by decide)))

theorem fz1_75_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨3, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 3 (by decide)))

theorem fz1_75_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨4, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 4 (by decide)))

theorem fz1_75_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨5, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 5 (by decide)))

theorem fz1_75_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨6, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 6 (by decide)))

theorem fz1_75_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨7, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 7 (by decide)))

theorem fz1_75_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨8, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 8 (by decide)))

theorem fz1_75_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨10, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 10 (by decide)))

theorem fz1_75_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨11, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 11 (by decide)))

theorem fz1_75_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨13, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 13 (by decide)))

theorem fz1_75_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨14, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 14 (by decide)))

theorem fz1_75_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨15, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 15 (by decide)))

theorem fz1_75_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨16, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 16 (by decide)))

theorem fz1_75_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨17, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 17 (by decide)))

theorem fz1_75_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨18, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 18 (by decide)))

theorem fz1_75_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨19, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 19 (by decide)))

theorem fz1_75_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨20, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 20 (by decide)))

theorem fz1_75_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨21, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 21 (by decide)))

theorem fz1_75_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨22, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 22 (by decide)))

theorem fz1_75_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨23, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 23 (by decide)))

theorem fz1_75_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨24, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 24 (by decide)))

theorem fz1_75_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨25, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 25 (by decide)))

theorem fz1_75_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨26, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 26 (by decide)))

theorem fz1_75_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨28, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 28 (by decide)))

theorem fz1_75_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨29, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 29 (by decide)))

theorem fz1_75_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨30, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 30 (by decide)))

theorem fz1_75_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨31, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 31 (by decide)))

theorem fz1_75_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨33, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 33 (by decide)))

theorem fz1_75_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨34, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 34 (by decide)))

theorem fz1_75_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨35, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 35 (by decide)))

theorem fz1_75_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨36, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 36 (by decide)))

theorem fz1_75_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨38, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 38 (by decide)))

theorem fz1_75_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨39, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 39 (by decide)))

theorem fz1_75_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨40, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 40 (by decide)))

theorem fz1_75_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨41, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 41 (by decide)))

theorem fz1_75_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨43, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 43 (by decide)))

theorem fz1_75_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨44, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 44 (by decide)))

theorem fz1_75_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨45, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 45 (by decide)))

theorem fz1_75_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨46, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 46 (by decide)))

theorem fz1_75_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨48, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 48 (by decide)))

theorem fz1_75_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨49, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 49 (by decide)))

theorem fz1_75_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨50, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 50 (by decide)))

theorem fz1_75_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨51, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 51 (by decide)))

theorem fz1_75_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨53, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 53 (by decide)))

theorem fz1_75_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨54, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 54 (by decide)))

theorem fz1_75_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨55, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 55 (by decide)))

theorem fz1_75_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨56, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 56 (by decide)))

theorem fz1_75_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨57, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 57 (by decide)))

theorem fz1_75_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨58, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 58 (by decide)))

theorem fz1_75_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨59, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 59 (by decide)))

theorem fz1_75_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨60, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 60 (by decide)))

theorem fz1_75_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨61, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 61 (by decide)))

theorem fz1_75_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨62, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 62 (by decide)))

theorem fz1_75_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨63, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 63 (by decide)))

theorem fz1_75_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨64, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 64 (by decide)))

theorem fz1_75_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨65, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 65 (by decide)))

theorem fz1_75_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨66, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 66 (by decide)))

theorem fz1_75_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨67, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 67 (by decide)))

theorem fz1_75_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨68, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 68 (by decide)))

theorem fz1_75_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨69, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 69 (by decide)))

theorem fz1_75_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨70, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 70 (by decide)))

theorem fz1_75_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨71, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 71 (by decide)))

theorem fz1_75_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨72, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 72 (by decide)))

theorem fz1_75_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨73, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 73 (by decide)))

theorem fz1_75_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨74, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 74 (by decide)))

theorem fz1_75_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨76, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 76 (by decide)))

theorem fz1_75_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨77, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 77 (by decide)))

theorem fz1_75_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨78, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 78 (by decide)))

theorem fz1_75_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨79, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 79 (by decide)))

theorem fz1_75_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨80, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 80 (by decide)))

theorem fz1_75_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨81, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 81 (by decide)))

theorem fz1_75_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨82, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 82 (by decide)))

theorem fz1_75_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨83, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 83 (by decide)))

theorem fz1_75_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨84, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 84 (by decide)))

theorem fz1_75_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨85, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 85 (by decide)))

theorem fz1_75_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨86, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 86 (by decide)))

theorem fz1_75_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨87, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 87 (by decide)))

theorem fz1_75_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨88, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 88 (by decide)))

theorem fz1_75_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨89, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 89 (by decide)))

theorem fz1_75_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨90, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 90 (by decide)))

theorem fz1_75_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨91, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 91 (by decide)))

theorem fz1_75_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨92, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 92 (by decide)))

theorem fz1_75_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨93, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 93 (by decide)))

theorem fz1_75_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨94, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 94 (by decide)))

theorem fz1_75_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨95, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 95 (by decide)))

theorem fz1_75_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨96, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 96 (by decide)))

theorem fz1_75_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨97, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 97 (by decide)))

theorem fz1_75_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨98, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 98 (by decide)))

theorem fz1_75_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨99, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 99 (by decide)))

theorem fz1_75_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨100, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 100 (by decide)))

theorem fz1_75_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨101, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 101 (by decide)))

theorem fz1_75_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨102, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 102 (by decide)))

theorem fz1_75_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨103, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 103 (by decide)))

theorem fz1_75_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨104, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 104 (by decide)))

theorem fz1_75_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨105, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 105 (by decide)))

theorem fz1_75_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨106, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 106 (by decide)))

theorem fz1_75_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨107, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 107 (by decide)))

theorem fz1_75_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨108, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 108 (by decide)))

theorem fz1_75_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨109, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 109 (by decide)))

theorem fz1_75_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨110, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 110 (by decide)))

theorem fz1_75_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨111, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 111 (by decide)))

theorem fz1_75_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨112, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 112 (by decide)))

theorem fz1_75_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨113, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 113 (by decide)))

theorem fz1_75_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨114, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 114 (by decide)))

theorem fz1_75_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK75)) = 0 :=
  repsFixedCard rK75 ⟨115, by decide⟩ R75 hpxR75 hcardq75
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_75) 115 (by decide)))

theorem fixz2_75 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK75) (retConj 2 (Q2.R75_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_75_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨1, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 1 (by decide)))

theorem fz2_75_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨2, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 2 (by decide)))

theorem fz2_75_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨3, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 3 (by decide)))

theorem fz2_75_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨4, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 4 (by decide)))

theorem fz2_75_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨5, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 5 (by decide)))

theorem fz2_75_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨6, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 6 (by decide)))

theorem fz2_75_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨7, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 7 (by decide)))

theorem fz2_75_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨8, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 8 (by decide)))

theorem fz2_75_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨10, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 10 (by decide)))

theorem fz2_75_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨11, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 11 (by decide)))

theorem fz2_75_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨13, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 13 (by decide)))

theorem fz2_75_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨14, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 14 (by decide)))

theorem fz2_75_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨15, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 15 (by decide)))

theorem fz2_75_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨16, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 16 (by decide)))

theorem fz2_75_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨17, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 17 (by decide)))

theorem fz2_75_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨18, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 18 (by decide)))

theorem fz2_75_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨19, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 19 (by decide)))

theorem fz2_75_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨20, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 20 (by decide)))

theorem fz2_75_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨21, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 21 (by decide)))

theorem fz2_75_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨22, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 22 (by decide)))

theorem fz2_75_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨23, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 23 (by decide)))

theorem fz2_75_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨24, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 24 (by decide)))

theorem fz2_75_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨25, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 25 (by decide)))

theorem fz2_75_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨26, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 26 (by decide)))

theorem fz2_75_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨28, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 28 (by decide)))

theorem fz2_75_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨29, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 29 (by decide)))

theorem fz2_75_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨30, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 30 (by decide)))

theorem fz2_75_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨31, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 31 (by decide)))

theorem fz2_75_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨33, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 33 (by decide)))

theorem fz2_75_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨34, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 34 (by decide)))

theorem fz2_75_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨35, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 35 (by decide)))

theorem fz2_75_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨36, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 36 (by decide)))

theorem fz2_75_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨38, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 38 (by decide)))

theorem fz2_75_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨39, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 39 (by decide)))

theorem fz2_75_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨40, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 40 (by decide)))

theorem fz2_75_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨41, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 41 (by decide)))

theorem fz2_75_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨43, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 43 (by decide)))

theorem fz2_75_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨44, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 44 (by decide)))

theorem fz2_75_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨45, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 45 (by decide)))

theorem fz2_75_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨46, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 46 (by decide)))

theorem fz2_75_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨48, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 48 (by decide)))

theorem fz2_75_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨49, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 49 (by decide)))

theorem fz2_75_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨50, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 50 (by decide)))

theorem fz2_75_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨51, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 51 (by decide)))

theorem fz2_75_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨53, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 53 (by decide)))

theorem fz2_75_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨54, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 54 (by decide)))

theorem fz2_75_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨55, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 55 (by decide)))

theorem fz2_75_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨56, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 56 (by decide)))

theorem fz2_75_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨57, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 57 (by decide)))

theorem fz2_75_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨58, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 58 (by decide)))

theorem fz2_75_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨59, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 59 (by decide)))

theorem fz2_75_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨60, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 60 (by decide)))

theorem fz2_75_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨61, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 61 (by decide)))

theorem fz2_75_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨62, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 62 (by decide)))

theorem fz2_75_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨63, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 63 (by decide)))

theorem fz2_75_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨64, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 64 (by decide)))

theorem fz2_75_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨65, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 65 (by decide)))

theorem fz2_75_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨66, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 66 (by decide)))

theorem fz2_75_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨67, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 67 (by decide)))

theorem fz2_75_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨68, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 68 (by decide)))

theorem fz2_75_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨69, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 69 (by decide)))

theorem fz2_75_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨70, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 70 (by decide)))

theorem fz2_75_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨71, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 71 (by decide)))

theorem fz2_75_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨72, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 72 (by decide)))

theorem fz2_75_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨73, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 73 (by decide)))

theorem fz2_75_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨74, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 74 (by decide)))

theorem fz2_75_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨76, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 76 (by decide)))

theorem fz2_75_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨77, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 77 (by decide)))

theorem fz2_75_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨78, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 78 (by decide)))

theorem fz2_75_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨79, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 79 (by decide)))

theorem fz2_75_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨80, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 80 (by decide)))

theorem fz2_75_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨81, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 81 (by decide)))

theorem fz2_75_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨82, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 82 (by decide)))

theorem fz2_75_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨83, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 83 (by decide)))

theorem fz2_75_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨84, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 84 (by decide)))

theorem fz2_75_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨85, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 85 (by decide)))

theorem fz2_75_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨86, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 86 (by decide)))

theorem fz2_75_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨87, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 87 (by decide)))

theorem fz2_75_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨88, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 88 (by decide)))

theorem fz2_75_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨89, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 89 (by decide)))

theorem fz2_75_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨90, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 90 (by decide)))

theorem fz2_75_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨91, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 91 (by decide)))

theorem fz2_75_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨92, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 92 (by decide)))

theorem fz2_75_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨93, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 93 (by decide)))

theorem fz2_75_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨94, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 94 (by decide)))

theorem fz2_75_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨95, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 95 (by decide)))

theorem fz2_75_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨96, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 96 (by decide)))

theorem fz2_75_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨97, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 97 (by decide)))

theorem fz2_75_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨98, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 98 (by decide)))

theorem fz2_75_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨99, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 99 (by decide)))

theorem fz2_75_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨100, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 100 (by decide)))

theorem fz2_75_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨101, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 101 (by decide)))

theorem fz2_75_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨102, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 102 (by decide)))

theorem fz2_75_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨103, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 103 (by decide)))

theorem fz2_75_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨104, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 104 (by decide)))

theorem fz2_75_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨105, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 105 (by decide)))

theorem fz2_75_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨106, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 106 (by decide)))

theorem fz2_75_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨107, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 107 (by decide)))

theorem fz2_75_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨108, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 108 (by decide)))

theorem fz2_75_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨109, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 109 (by decide)))

theorem fz2_75_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨110, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 110 (by decide)))

theorem fz2_75_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨111, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 111 (by decide)))

theorem fz2_75_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨112, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 112 (by decide)))

theorem fz2_75_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨113, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 113 (by decide)))

theorem fz2_75_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨114, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 114 (by decide)))

theorem fz2_75_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK75)) = 0 :=
  Q2.repsFixedCard2 rK75 ⟨115, by decide⟩ Q2.R75_2 Q2.hpxR75_2 Q2.hcardq75_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_75) 115 (by decide)))

theorem fixz1_76 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK76) (retConj 1 (R76 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_76_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨2, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 2 (by decide)))

theorem fz1_76_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨3, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 3 (by decide)))

theorem fz1_76_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨4, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 4 (by decide)))

theorem fz1_76_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨5, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 5 (by decide)))

theorem fz1_76_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨6, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 6 (by decide)))

theorem fz1_76_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨7, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 7 (by decide)))

theorem fz1_76_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨8, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 8 (by decide)))

theorem fz1_76_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨9, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 9 (by decide)))

theorem fz1_76_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨10, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 10 (by decide)))

theorem fz1_76_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨11, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 11 (by decide)))

theorem fz1_76_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨13, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 13 (by decide)))

theorem fz1_76_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨14, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 14 (by decide)))

theorem fz1_76_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨15, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 15 (by decide)))

theorem fz1_76_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨16, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 16 (by decide)))

theorem fz1_76_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨17, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 17 (by decide)))

theorem fz1_76_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨18, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 18 (by decide)))

theorem fz1_76_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨20, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 20 (by decide)))

theorem fz1_76_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨21, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 21 (by decide)))

theorem fz1_76_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨22, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 22 (by decide)))

theorem fz1_76_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨23, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 23 (by decide)))

theorem fz1_76_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨24, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 24 (by decide)))

theorem fz1_76_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨25, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 25 (by decide)))

theorem fz1_76_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨26, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 26 (by decide)))

theorem fz1_76_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨27, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 27 (by decide)))

theorem fz1_76_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨28, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 28 (by decide)))

theorem fz1_76_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨29, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 29 (by decide)))

theorem fz1_76_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨30, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 30 (by decide)))

theorem fz1_76_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨31, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 31 (by decide)))

theorem fz1_76_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨33, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 33 (by decide)))

theorem fz1_76_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨34, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 34 (by decide)))

theorem fz1_76_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨35, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 35 (by decide)))

theorem fz1_76_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨36, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 36 (by decide)))

theorem fz1_76_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨38, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 38 (by decide)))

theorem fz1_76_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨39, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 39 (by decide)))

theorem fz1_76_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨40, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 40 (by decide)))

theorem fz1_76_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨41, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 41 (by decide)))

theorem fz1_76_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨43, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 43 (by decide)))

theorem fz1_76_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨44, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 44 (by decide)))

theorem fz1_76_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨45, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 45 (by decide)))

theorem fz1_76_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨46, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 46 (by decide)))

theorem fz1_76_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨48, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 48 (by decide)))

theorem fz1_76_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨49, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 49 (by decide)))

theorem fz1_76_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨50, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 50 (by decide)))

theorem fz1_76_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨51, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 51 (by decide)))

theorem fz1_76_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨53, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 53 (by decide)))

theorem fz1_76_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨54, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 54 (by decide)))

theorem fz1_76_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨55, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 55 (by decide)))

theorem fz1_76_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨56, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 56 (by decide)))

theorem fz1_76_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨57, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 57 (by decide)))

theorem fz1_76_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨58, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 58 (by decide)))

theorem fz1_76_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨59, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 59 (by decide)))

theorem fz1_76_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨60, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 60 (by decide)))

theorem fz1_76_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨61, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 61 (by decide)))

theorem fz1_76_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨62, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 62 (by decide)))

theorem fz1_76_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨63, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 63 (by decide)))

theorem fz1_76_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨64, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 64 (by decide)))

theorem fz1_76_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨65, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 65 (by decide)))

theorem fz1_76_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨66, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 66 (by decide)))

theorem fz1_76_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨67, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 67 (by decide)))

theorem fz1_76_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨68, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 68 (by decide)))

theorem fz1_76_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨69, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 69 (by decide)))

theorem fz1_76_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨70, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 70 (by decide)))

theorem fz1_76_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨71, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 71 (by decide)))

theorem fz1_76_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨72, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 72 (by decide)))

theorem fz1_76_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨73, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 73 (by decide)))

theorem fz1_76_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨74, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 74 (by decide)))

theorem fz1_76_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨75, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 75 (by decide)))

theorem fz1_76_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨77, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 77 (by decide)))

theorem fz1_76_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨78, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 78 (by decide)))

theorem fz1_76_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨79, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 79 (by decide)))

theorem fz1_76_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨80, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 80 (by decide)))

theorem fz1_76_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨81, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 81 (by decide)))

theorem fz1_76_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨82, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 82 (by decide)))

theorem fz1_76_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨83, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 83 (by decide)))

theorem fz1_76_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨84, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 84 (by decide)))

theorem fz1_76_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨85, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 85 (by decide)))

theorem fz1_76_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨86, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 86 (by decide)))

theorem fz1_76_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨87, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 87 (by decide)))

theorem fz1_76_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨88, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 88 (by decide)))

theorem fz1_76_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨89, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 89 (by decide)))

theorem fz1_76_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨90, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 90 (by decide)))

theorem fz1_76_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨91, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 91 (by decide)))

theorem fz1_76_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨92, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 92 (by decide)))

theorem fz1_76_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨93, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 93 (by decide)))

theorem fz1_76_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨94, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 94 (by decide)))

theorem fz1_76_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨95, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 95 (by decide)))

theorem fz1_76_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨96, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 96 (by decide)))

theorem fz1_76_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨97, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 97 (by decide)))

theorem fz1_76_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨98, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 98 (by decide)))

theorem fz1_76_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨99, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 99 (by decide)))

theorem fz1_76_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨100, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 100 (by decide)))

theorem fz1_76_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨101, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 101 (by decide)))

theorem fz1_76_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨102, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 102 (by decide)))

theorem fz1_76_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨103, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 103 (by decide)))

theorem fz1_76_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨104, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 104 (by decide)))

theorem fz1_76_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨105, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 105 (by decide)))

theorem fz1_76_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨106, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 106 (by decide)))

theorem fz1_76_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨107, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 107 (by decide)))

theorem fz1_76_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨108, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 108 (by decide)))

theorem fz1_76_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨109, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 109 (by decide)))

theorem fz1_76_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨110, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 110 (by decide)))

theorem fz1_76_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨111, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 111 (by decide)))

theorem fz1_76_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨112, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 112 (by decide)))

theorem fz1_76_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨113, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 113 (by decide)))

theorem fz1_76_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨114, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 114 (by decide)))

theorem fz1_76_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK76)) = 0 :=
  repsFixedCard rK76 ⟨115, by decide⟩ R76 hpxR76 hcardq76
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_76) 115 (by decide)))

theorem fixz2_76 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 48, 49, 50, 51, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK76) (retConj 2 (Q2.R76_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_76_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨2, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 2 (by decide)))

theorem fz2_76_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨3, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 3 (by decide)))

theorem fz2_76_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨4, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 4 (by decide)))

theorem fz2_76_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨5, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 5 (by decide)))

theorem fz2_76_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨6, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 6 (by decide)))

theorem fz2_76_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨7, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 7 (by decide)))

theorem fz2_76_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨8, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 8 (by decide)))

theorem fz2_76_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨9, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 9 (by decide)))

theorem fz2_76_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨10, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 10 (by decide)))

theorem fz2_76_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨11, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 11 (by decide)))

theorem fz2_76_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨13, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 13 (by decide)))

theorem fz2_76_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨14, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 14 (by decide)))

theorem fz2_76_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨15, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 15 (by decide)))

theorem fz2_76_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨16, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 16 (by decide)))

theorem fz2_76_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨17, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 17 (by decide)))

theorem fz2_76_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨18, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 18 (by decide)))

theorem fz2_76_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨20, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 20 (by decide)))

theorem fz2_76_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨21, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 21 (by decide)))

theorem fz2_76_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨22, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 22 (by decide)))

theorem fz2_76_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨23, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 23 (by decide)))

theorem fz2_76_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨24, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 24 (by decide)))

theorem fz2_76_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨25, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 25 (by decide)))

theorem fz2_76_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨26, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 26 (by decide)))

theorem fz2_76_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨27, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 27 (by decide)))

theorem fz2_76_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨28, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 28 (by decide)))

theorem fz2_76_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨29, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 29 (by decide)))

theorem fz2_76_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨30, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 30 (by decide)))

theorem fz2_76_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨31, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 31 (by decide)))

theorem fz2_76_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨33, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 33 (by decide)))

theorem fz2_76_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨34, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 34 (by decide)))

theorem fz2_76_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨35, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 35 (by decide)))

theorem fz2_76_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨36, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 36 (by decide)))

theorem fz2_76_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨38, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 38 (by decide)))

theorem fz2_76_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨39, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 39 (by decide)))

theorem fz2_76_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨40, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 40 (by decide)))

theorem fz2_76_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨41, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 41 (by decide)))

theorem fz2_76_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨43, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 43 (by decide)))

theorem fz2_76_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨44, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 44 (by decide)))

theorem fz2_76_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨45, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 45 (by decide)))

theorem fz2_76_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨46, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 46 (by decide)))

theorem fz2_76_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨48, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 48 (by decide)))

theorem fz2_76_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨49, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 49 (by decide)))

theorem fz2_76_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨50, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 50 (by decide)))

theorem fz2_76_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨51, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 51 (by decide)))

theorem fz2_76_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨53, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 53 (by decide)))

theorem fz2_76_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨54, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 54 (by decide)))

theorem fz2_76_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨55, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 55 (by decide)))

theorem fz2_76_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨56, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 56 (by decide)))

theorem fz2_76_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨57, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 57 (by decide)))

theorem fz2_76_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨58, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 58 (by decide)))

theorem fz2_76_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨59, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 59 (by decide)))

theorem fz2_76_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨60, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 60 (by decide)))

theorem fz2_76_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨61, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 61 (by decide)))

theorem fz2_76_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨62, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 62 (by decide)))

theorem fz2_76_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨63, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 63 (by decide)))

theorem fz2_76_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨64, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 64 (by decide)))

theorem fz2_76_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨65, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 65 (by decide)))

theorem fz2_76_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨66, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 66 (by decide)))

theorem fz2_76_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨67, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 67 (by decide)))

theorem fz2_76_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨68, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 68 (by decide)))

theorem fz2_76_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨69, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 69 (by decide)))

theorem fz2_76_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨70, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 70 (by decide)))

theorem fz2_76_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨71, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 71 (by decide)))

theorem fz2_76_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨72, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 72 (by decide)))

theorem fz2_76_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨73, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 73 (by decide)))

theorem fz2_76_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨74, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 74 (by decide)))

theorem fz2_76_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨75, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 75 (by decide)))

theorem fz2_76_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨77, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 77 (by decide)))

theorem fz2_76_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨78, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 78 (by decide)))

theorem fz2_76_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨79, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 79 (by decide)))

theorem fz2_76_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨80, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 80 (by decide)))

theorem fz2_76_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨81, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 81 (by decide)))

theorem fz2_76_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨82, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 82 (by decide)))

theorem fz2_76_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨83, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 83 (by decide)))

theorem fz2_76_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨84, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 84 (by decide)))

theorem fz2_76_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨85, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 85 (by decide)))

theorem fz2_76_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨86, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 86 (by decide)))

theorem fz2_76_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨87, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 87 (by decide)))

theorem fz2_76_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨88, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 88 (by decide)))

theorem fz2_76_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨89, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 89 (by decide)))

theorem fz2_76_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨90, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 90 (by decide)))

theorem fz2_76_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨91, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 91 (by decide)))

theorem fz2_76_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨92, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 92 (by decide)))

theorem fz2_76_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨93, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 93 (by decide)))

theorem fz2_76_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨94, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 94 (by decide)))

theorem fz2_76_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨95, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 95 (by decide)))

theorem fz2_76_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨96, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 96 (by decide)))

theorem fz2_76_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨97, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 97 (by decide)))

theorem fz2_76_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨98, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 98 (by decide)))

theorem fz2_76_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨99, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 99 (by decide)))

theorem fz2_76_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨100, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 100 (by decide)))

theorem fz2_76_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨101, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 101 (by decide)))

theorem fz2_76_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨102, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 102 (by decide)))

theorem fz2_76_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨103, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 103 (by decide)))

theorem fz2_76_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨104, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 104 (by decide)))

theorem fz2_76_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨105, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 105 (by decide)))

theorem fz2_76_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨106, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 106 (by decide)))

theorem fz2_76_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨107, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 107 (by decide)))

theorem fz2_76_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨108, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 108 (by decide)))

theorem fz2_76_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨109, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 109 (by decide)))

theorem fz2_76_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨110, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 110 (by decide)))

theorem fz2_76_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨111, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 111 (by decide)))

theorem fz2_76_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨112, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 112 (by decide)))

theorem fz2_76_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨113, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 113 (by decide)))

theorem fz2_76_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨114, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 114 (by decide)))

theorem fz2_76_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK76)) = 0 :=
  Q2.repsFixedCard2 rK76 ⟨115, by decide⟩ Q2.R76_2 Q2.hpxR76_2 Q2.hcardq76_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_76) 115 (by decide)))

end LeanDring.P5Presentation
