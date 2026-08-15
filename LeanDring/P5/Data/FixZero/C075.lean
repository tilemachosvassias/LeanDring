/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C022

/-!
# Species-table cells, off-support emptiness certificates, chunk 74

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

theorem fixz1_95 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK95) (retConj 1 (R95 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_95_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨1, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 1 (by decide)))

theorem fz1_95_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨2, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 2 (by decide)))

theorem fz1_95_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨3, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 3 (by decide)))

theorem fz1_95_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨4, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 4 (by decide)))

theorem fz1_95_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨5, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 5 (by decide)))

theorem fz1_95_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨6, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 6 (by decide)))

theorem fz1_95_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨7, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 7 (by decide)))

theorem fz1_95_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨8, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 8 (by decide)))

theorem fz1_95_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨9, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 9 (by decide)))

theorem fz1_95_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨11, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 11 (by decide)))

theorem fz1_95_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨13, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 13 (by decide)))

theorem fz1_95_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨14, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 14 (by decide)))

theorem fz1_95_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨15, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 15 (by decide)))

theorem fz1_95_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨16, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 16 (by decide)))

theorem fz1_95_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨17, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 17 (by decide)))

theorem fz1_95_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨18, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 18 (by decide)))

theorem fz1_95_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨19, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 19 (by decide)))

theorem fz1_95_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨20, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 20 (by decide)))

theorem fz1_95_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨21, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 21 (by decide)))

theorem fz1_95_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨22, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 22 (by decide)))

theorem fz1_95_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨23, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 23 (by decide)))

theorem fz1_95_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨24, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 24 (by decide)))

theorem fz1_95_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨25, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 25 (by decide)))

theorem fz1_95_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨26, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 26 (by decide)))

theorem fz1_95_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨27, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 27 (by decide)))

theorem fz1_95_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨28, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 28 (by decide)))

theorem fz1_95_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨29, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 29 (by decide)))

theorem fz1_95_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨30, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 30 (by decide)))

theorem fz1_95_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨31, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 31 (by decide)))

theorem fz1_95_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨32, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 32 (by decide)))

theorem fz1_95_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨34, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 34 (by decide)))

theorem fz1_95_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨35, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 35 (by decide)))

theorem fz1_95_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨36, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 36 (by decide)))

theorem fz1_95_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨37, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 37 (by decide)))

theorem fz1_95_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨38, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 38 (by decide)))

theorem fz1_95_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨39, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 39 (by decide)))

theorem fz1_95_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨40, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 40 (by decide)))

theorem fz1_95_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨41, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 41 (by decide)))

theorem fz1_95_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨42, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 42 (by decide)))

theorem fz1_95_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨43, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 43 (by decide)))

theorem fz1_95_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨44, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 44 (by decide)))

theorem fz1_95_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨45, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 45 (by decide)))

theorem fz1_95_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨46, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 46 (by decide)))

theorem fz1_95_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨47, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 47 (by decide)))

theorem fz1_95_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨48, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 48 (by decide)))

theorem fz1_95_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨49, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 49 (by decide)))

theorem fz1_95_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨50, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 50 (by decide)))

theorem fz1_95_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨51, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 51 (by decide)))

theorem fz1_95_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨52, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 52 (by decide)))

theorem fz1_95_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨54, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 54 (by decide)))

theorem fz1_95_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨55, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 55 (by decide)))

theorem fz1_95_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨56, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 56 (by decide)))

theorem fz1_95_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨57, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 57 (by decide)))

theorem fz1_95_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨58, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 58 (by decide)))

theorem fz1_95_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨59, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 59 (by decide)))

theorem fz1_95_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨60, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 60 (by decide)))

theorem fz1_95_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨61, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 61 (by decide)))

theorem fz1_95_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨62, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 62 (by decide)))

theorem fz1_95_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨63, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 63 (by decide)))

theorem fz1_95_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨64, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 64 (by decide)))

theorem fz1_95_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨65, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 65 (by decide)))

theorem fz1_95_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨66, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 66 (by decide)))

theorem fz1_95_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨67, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 67 (by decide)))

theorem fz1_95_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨68, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 68 (by decide)))

theorem fz1_95_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨69, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 69 (by decide)))

theorem fz1_95_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨70, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 70 (by decide)))

theorem fz1_95_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨71, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 71 (by decide)))

theorem fz1_95_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨72, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 72 (by decide)))

theorem fz1_95_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨73, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 73 (by decide)))

theorem fz1_95_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨74, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 74 (by decide)))

theorem fz1_95_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨75, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 75 (by decide)))

theorem fz1_95_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨76, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 76 (by decide)))

theorem fz1_95_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨77, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 77 (by decide)))

theorem fz1_95_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨78, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 78 (by decide)))

theorem fz1_95_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨79, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 79 (by decide)))

theorem fz1_95_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨80, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 80 (by decide)))

theorem fz1_95_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨81, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 81 (by decide)))

theorem fz1_95_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨82, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 82 (by decide)))

theorem fz1_95_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨83, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 83 (by decide)))

theorem fz1_95_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨84, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 84 (by decide)))

theorem fz1_95_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨85, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 85 (by decide)))

theorem fz1_95_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨86, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 86 (by decide)))

theorem fz1_95_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨87, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 87 (by decide)))

theorem fz1_95_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨88, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 88 (by decide)))

theorem fz1_95_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨89, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 89 (by decide)))

theorem fz1_95_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨90, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 90 (by decide)))

theorem fz1_95_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨91, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 91 (by decide)))

theorem fz1_95_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨92, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 92 (by decide)))

theorem fz1_95_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨93, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 93 (by decide)))

theorem fz1_95_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨94, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 94 (by decide)))

theorem fz1_95_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨96, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 96 (by decide)))

theorem fz1_95_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨97, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 97 (by decide)))

theorem fz1_95_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨98, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 98 (by decide)))

theorem fz1_95_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨99, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 99 (by decide)))

theorem fz1_95_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨100, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 100 (by decide)))

theorem fz1_95_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨101, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 101 (by decide)))

theorem fz1_95_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨102, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 102 (by decide)))

theorem fz1_95_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨103, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 103 (by decide)))

theorem fz1_95_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨104, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 104 (by decide)))

theorem fz1_95_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨105, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 105 (by decide)))

theorem fz1_95_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨106, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 106 (by decide)))

theorem fz1_95_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨107, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 107 (by decide)))

theorem fz1_95_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨108, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 108 (by decide)))

theorem fz1_95_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨109, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 109 (by decide)))

theorem fz1_95_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨110, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 110 (by decide)))

theorem fz1_95_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨111, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 111 (by decide)))

theorem fz1_95_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨112, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 112 (by decide)))

theorem fz1_95_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨113, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 113 (by decide)))

theorem fz1_95_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨114, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 114 (by decide)))

theorem fz1_95_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK95)) = 0 :=
  repsFixedCard rK95 ⟨115, by decide⟩ R95 hpxR95 hcardq95
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_95) 115 (by decide)))

theorem fixz2_95 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK95) (retConj 2 (Q2.R95_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_95_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨1, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 1 (by decide)))

theorem fz2_95_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨2, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 2 (by decide)))

theorem fz2_95_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨3, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 3 (by decide)))

theorem fz2_95_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨4, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 4 (by decide)))

theorem fz2_95_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨5, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 5 (by decide)))

theorem fz2_95_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨6, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 6 (by decide)))

theorem fz2_95_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨7, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 7 (by decide)))

theorem fz2_95_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨8, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 8 (by decide)))

theorem fz2_95_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨9, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 9 (by decide)))

theorem fz2_95_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨11, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 11 (by decide)))

theorem fz2_95_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨13, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 13 (by decide)))

theorem fz2_95_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨14, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 14 (by decide)))

theorem fz2_95_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨15, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 15 (by decide)))

theorem fz2_95_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨16, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 16 (by decide)))

theorem fz2_95_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨17, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 17 (by decide)))

theorem fz2_95_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨18, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 18 (by decide)))

theorem fz2_95_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨19, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 19 (by decide)))

theorem fz2_95_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨20, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 20 (by decide)))

theorem fz2_95_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨21, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 21 (by decide)))

theorem fz2_95_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨22, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 22 (by decide)))

theorem fz2_95_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨23, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 23 (by decide)))

theorem fz2_95_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨24, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 24 (by decide)))

theorem fz2_95_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨25, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 25 (by decide)))

theorem fz2_95_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨26, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 26 (by decide)))

theorem fz2_95_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨27, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 27 (by decide)))

theorem fz2_95_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨28, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 28 (by decide)))

theorem fz2_95_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨29, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 29 (by decide)))

theorem fz2_95_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨30, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 30 (by decide)))

theorem fz2_95_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨31, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 31 (by decide)))

theorem fz2_95_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨32, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 32 (by decide)))

theorem fz2_95_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨34, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 34 (by decide)))

theorem fz2_95_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨35, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 35 (by decide)))

theorem fz2_95_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨36, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 36 (by decide)))

theorem fz2_95_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨37, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 37 (by decide)))

theorem fz2_95_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨38, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 38 (by decide)))

theorem fz2_95_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨39, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 39 (by decide)))

theorem fz2_95_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨40, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 40 (by decide)))

theorem fz2_95_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨41, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 41 (by decide)))

theorem fz2_95_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨42, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 42 (by decide)))

theorem fz2_95_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨43, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 43 (by decide)))

theorem fz2_95_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨44, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 44 (by decide)))

theorem fz2_95_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨45, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 45 (by decide)))

theorem fz2_95_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨46, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 46 (by decide)))

theorem fz2_95_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨47, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 47 (by decide)))

theorem fz2_95_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨48, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 48 (by decide)))

theorem fz2_95_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨49, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 49 (by decide)))

theorem fz2_95_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨50, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 50 (by decide)))

theorem fz2_95_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨51, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 51 (by decide)))

theorem fz2_95_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨52, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 52 (by decide)))

theorem fz2_95_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨54, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 54 (by decide)))

theorem fz2_95_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨55, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 55 (by decide)))

theorem fz2_95_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨56, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 56 (by decide)))

theorem fz2_95_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨57, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 57 (by decide)))

theorem fz2_95_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨58, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 58 (by decide)))

theorem fz2_95_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨59, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 59 (by decide)))

theorem fz2_95_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨60, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 60 (by decide)))

theorem fz2_95_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨61, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 61 (by decide)))

theorem fz2_95_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨62, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 62 (by decide)))

theorem fz2_95_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨63, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 63 (by decide)))

theorem fz2_95_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨64, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 64 (by decide)))

theorem fz2_95_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨65, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 65 (by decide)))

theorem fz2_95_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨66, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 66 (by decide)))

theorem fz2_95_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨67, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 67 (by decide)))

theorem fz2_95_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨68, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 68 (by decide)))

theorem fz2_95_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨69, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 69 (by decide)))

theorem fz2_95_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨70, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 70 (by decide)))

theorem fz2_95_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨71, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 71 (by decide)))

theorem fz2_95_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨72, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 72 (by decide)))

theorem fz2_95_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨73, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 73 (by decide)))

theorem fz2_95_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨74, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 74 (by decide)))

theorem fz2_95_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨75, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 75 (by decide)))

theorem fz2_95_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨76, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 76 (by decide)))

theorem fz2_95_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨77, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 77 (by decide)))

theorem fz2_95_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨78, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 78 (by decide)))

theorem fz2_95_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨79, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 79 (by decide)))

theorem fz2_95_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨80, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 80 (by decide)))

theorem fz2_95_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨81, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 81 (by decide)))

theorem fz2_95_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨82, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 82 (by decide)))

theorem fz2_95_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨83, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 83 (by decide)))

theorem fz2_95_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨84, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 84 (by decide)))

theorem fz2_95_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨85, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 85 (by decide)))

theorem fz2_95_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨86, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 86 (by decide)))

theorem fz2_95_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨87, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 87 (by decide)))

theorem fz2_95_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨88, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 88 (by decide)))

theorem fz2_95_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨89, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 89 (by decide)))

theorem fz2_95_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨90, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 90 (by decide)))

theorem fz2_95_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨91, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 91 (by decide)))

theorem fz2_95_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨92, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 92 (by decide)))

theorem fz2_95_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨93, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 93 (by decide)))

theorem fz2_95_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨94, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 94 (by decide)))

theorem fz2_95_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨96, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 96 (by decide)))

theorem fz2_95_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨97, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 97 (by decide)))

theorem fz2_95_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨98, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 98 (by decide)))

theorem fz2_95_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨99, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 99 (by decide)))

theorem fz2_95_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨100, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 100 (by decide)))

theorem fz2_95_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨101, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 101 (by decide)))

theorem fz2_95_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨102, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 102 (by decide)))

theorem fz2_95_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨103, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 103 (by decide)))

theorem fz2_95_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨104, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 104 (by decide)))

theorem fz2_95_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨105, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 105 (by decide)))

theorem fz2_95_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨106, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 106 (by decide)))

theorem fz2_95_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨107, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 107 (by decide)))

theorem fz2_95_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨108, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 108 (by decide)))

theorem fz2_95_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨109, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 109 (by decide)))

theorem fz2_95_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨110, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 110 (by decide)))

theorem fz2_95_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨111, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 111 (by decide)))

theorem fz2_95_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨112, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 112 (by decide)))

theorem fz2_95_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨113, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 113 (by decide)))

theorem fz2_95_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨114, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 114 (by decide)))

theorem fz2_95_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK95)) = 0 :=
  Q2.repsFixedCard2 rK95 ⟨115, by decide⟩ Q2.R95_2 Q2.hpxR95_2 Q2.hcardq95_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_95) 115 (by decide)))

theorem fixz1_96 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK96) (retConj 1 (R96 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_96_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨1, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 1 (by decide)))

theorem fz1_96_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨2, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 2 (by decide)))

theorem fz1_96_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨3, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 3 (by decide)))

theorem fz1_96_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨4, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 4 (by decide)))

theorem fz1_96_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨5, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 5 (by decide)))

theorem fz1_96_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨6, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 6 (by decide)))

theorem fz1_96_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨7, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 7 (by decide)))

theorem fz1_96_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨8, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 8 (by decide)))

theorem fz1_96_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨9, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 9 (by decide)))

theorem fz1_96_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨11, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 11 (by decide)))

theorem fz1_96_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨13, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 13 (by decide)))

theorem fz1_96_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨14, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 14 (by decide)))

theorem fz1_96_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨15, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 15 (by decide)))

theorem fz1_96_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨16, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 16 (by decide)))

theorem fz1_96_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨17, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 17 (by decide)))

theorem fz1_96_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨18, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 18 (by decide)))

theorem fz1_96_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨19, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 19 (by decide)))

theorem fz1_96_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨20, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 20 (by decide)))

theorem fz1_96_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨21, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 21 (by decide)))

theorem fz1_96_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨22, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 22 (by decide)))

theorem fz1_96_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨23, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 23 (by decide)))

theorem fz1_96_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨24, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 24 (by decide)))

theorem fz1_96_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨25, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 25 (by decide)))

theorem fz1_96_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨26, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 26 (by decide)))

theorem fz1_96_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨27, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 27 (by decide)))

theorem fz1_96_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨28, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 28 (by decide)))

theorem fz1_96_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨29, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 29 (by decide)))

theorem fz1_96_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨30, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 30 (by decide)))

theorem fz1_96_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨31, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 31 (by decide)))

theorem fz1_96_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨32, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 32 (by decide)))

theorem fz1_96_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨33, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 33 (by decide)))

theorem fz1_96_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨35, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 35 (by decide)))

theorem fz1_96_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨36, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 36 (by decide)))

theorem fz1_96_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨37, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 37 (by decide)))

theorem fz1_96_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨38, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 38 (by decide)))

theorem fz1_96_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨39, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 39 (by decide)))

theorem fz1_96_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨40, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 40 (by decide)))

theorem fz1_96_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨41, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 41 (by decide)))

theorem fz1_96_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨42, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 42 (by decide)))

theorem fz1_96_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨43, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 43 (by decide)))

theorem fz1_96_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨44, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 44 (by decide)))

theorem fz1_96_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨45, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 45 (by decide)))

theorem fz1_96_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨46, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 46 (by decide)))

theorem fz1_96_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨47, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 47 (by decide)))

theorem fz1_96_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨48, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 48 (by decide)))

theorem fz1_96_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨49, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 49 (by decide)))

theorem fz1_96_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨50, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 50 (by decide)))

theorem fz1_96_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨51, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 51 (by decide)))

theorem fz1_96_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨52, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 52 (by decide)))

theorem fz1_96_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨54, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 54 (by decide)))

theorem fz1_96_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨55, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 55 (by decide)))

theorem fz1_96_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨56, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 56 (by decide)))

theorem fz1_96_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨57, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 57 (by decide)))

theorem fz1_96_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨58, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 58 (by decide)))

theorem fz1_96_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨59, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 59 (by decide)))

theorem fz1_96_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨60, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 60 (by decide)))

theorem fz1_96_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨61, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 61 (by decide)))

theorem fz1_96_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨62, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 62 (by decide)))

theorem fz1_96_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨63, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 63 (by decide)))

theorem fz1_96_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨64, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 64 (by decide)))

theorem fz1_96_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨65, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 65 (by decide)))

theorem fz1_96_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨66, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 66 (by decide)))

theorem fz1_96_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨67, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 67 (by decide)))

theorem fz1_96_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨68, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 68 (by decide)))

theorem fz1_96_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨69, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 69 (by decide)))

theorem fz1_96_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨70, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 70 (by decide)))

theorem fz1_96_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨71, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 71 (by decide)))

theorem fz1_96_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨72, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 72 (by decide)))

theorem fz1_96_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨73, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 73 (by decide)))

theorem fz1_96_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨74, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 74 (by decide)))

theorem fz1_96_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨75, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 75 (by decide)))

theorem fz1_96_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨76, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 76 (by decide)))

theorem fz1_96_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨77, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 77 (by decide)))

theorem fz1_96_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨78, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 78 (by decide)))

theorem fz1_96_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨79, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 79 (by decide)))

theorem fz1_96_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨80, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 80 (by decide)))

theorem fz1_96_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨81, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 81 (by decide)))

theorem fz1_96_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨82, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 82 (by decide)))

theorem fz1_96_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨83, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 83 (by decide)))

theorem fz1_96_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨84, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 84 (by decide)))

theorem fz1_96_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨85, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 85 (by decide)))

theorem fz1_96_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨86, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 86 (by decide)))

theorem fz1_96_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨87, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 87 (by decide)))

theorem fz1_96_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨88, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 88 (by decide)))

theorem fz1_96_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨89, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 89 (by decide)))

theorem fz1_96_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨90, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 90 (by decide)))

theorem fz1_96_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨91, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 91 (by decide)))

theorem fz1_96_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨92, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 92 (by decide)))

theorem fz1_96_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨93, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 93 (by decide)))

theorem fz1_96_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨94, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 94 (by decide)))

theorem fz1_96_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨95, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 95 (by decide)))

theorem fz1_96_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨97, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 97 (by decide)))

theorem fz1_96_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨98, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 98 (by decide)))

theorem fz1_96_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨99, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 99 (by decide)))

theorem fz1_96_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨100, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 100 (by decide)))

theorem fz1_96_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨101, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 101 (by decide)))

theorem fz1_96_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨102, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 102 (by decide)))

theorem fz1_96_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨103, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 103 (by decide)))

theorem fz1_96_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨104, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 104 (by decide)))

theorem fz1_96_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨105, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 105 (by decide)))

theorem fz1_96_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨106, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 106 (by decide)))

theorem fz1_96_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨107, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 107 (by decide)))

theorem fz1_96_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨108, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 108 (by decide)))

theorem fz1_96_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨109, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 109 (by decide)))

theorem fz1_96_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨110, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 110 (by decide)))

theorem fz1_96_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨111, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 111 (by decide)))

theorem fz1_96_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨112, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 112 (by decide)))

theorem fz1_96_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨113, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 113 (by decide)))

theorem fz1_96_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨114, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 114 (by decide)))

theorem fz1_96_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK96)) = 0 :=
  repsFixedCard rK96 ⟨115, by decide⟩ R96 hpxR96 hcardq96
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_96) 115 (by decide)))

theorem fixz2_96 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK96) (retConj 2 (Q2.R96_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_96_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨1, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 1 (by decide)))

theorem fz2_96_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨2, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 2 (by decide)))

theorem fz2_96_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨3, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 3 (by decide)))

theorem fz2_96_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨4, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 4 (by decide)))

theorem fz2_96_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨5, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 5 (by decide)))

theorem fz2_96_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨6, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 6 (by decide)))

theorem fz2_96_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨7, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 7 (by decide)))

theorem fz2_96_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨8, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 8 (by decide)))

theorem fz2_96_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨9, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 9 (by decide)))

theorem fz2_96_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨11, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 11 (by decide)))

theorem fz2_96_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨13, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 13 (by decide)))

theorem fz2_96_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨14, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 14 (by decide)))

theorem fz2_96_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨15, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 15 (by decide)))

theorem fz2_96_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨16, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 16 (by decide)))

theorem fz2_96_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨17, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 17 (by decide)))

theorem fz2_96_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨18, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 18 (by decide)))

theorem fz2_96_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨19, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 19 (by decide)))

theorem fz2_96_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨20, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 20 (by decide)))

theorem fz2_96_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨21, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 21 (by decide)))

theorem fz2_96_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨22, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 22 (by decide)))

theorem fz2_96_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨23, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 23 (by decide)))

theorem fz2_96_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨24, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 24 (by decide)))

theorem fz2_96_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨25, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 25 (by decide)))

theorem fz2_96_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨26, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 26 (by decide)))

theorem fz2_96_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨27, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 27 (by decide)))

theorem fz2_96_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨28, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 28 (by decide)))

theorem fz2_96_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨29, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 29 (by decide)))

theorem fz2_96_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨30, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 30 (by decide)))

theorem fz2_96_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨31, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 31 (by decide)))

theorem fz2_96_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨32, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 32 (by decide)))

theorem fz2_96_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨33, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 33 (by decide)))

theorem fz2_96_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨35, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 35 (by decide)))

theorem fz2_96_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨36, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 36 (by decide)))

theorem fz2_96_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨37, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 37 (by decide)))

theorem fz2_96_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨38, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 38 (by decide)))

theorem fz2_96_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨39, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 39 (by decide)))

theorem fz2_96_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨40, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 40 (by decide)))

theorem fz2_96_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨41, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 41 (by decide)))

theorem fz2_96_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨42, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 42 (by decide)))

theorem fz2_96_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨43, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 43 (by decide)))

theorem fz2_96_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨44, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 44 (by decide)))

theorem fz2_96_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨45, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 45 (by decide)))

theorem fz2_96_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨46, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 46 (by decide)))

theorem fz2_96_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨47, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 47 (by decide)))

theorem fz2_96_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨48, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 48 (by decide)))

theorem fz2_96_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨49, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 49 (by decide)))

theorem fz2_96_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨50, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 50 (by decide)))

theorem fz2_96_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨51, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 51 (by decide)))

theorem fz2_96_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨52, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 52 (by decide)))

theorem fz2_96_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨54, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 54 (by decide)))

theorem fz2_96_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨55, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 55 (by decide)))

theorem fz2_96_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨56, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 56 (by decide)))

theorem fz2_96_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨57, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 57 (by decide)))

theorem fz2_96_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨58, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 58 (by decide)))

theorem fz2_96_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨59, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 59 (by decide)))

theorem fz2_96_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨60, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 60 (by decide)))

theorem fz2_96_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨61, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 61 (by decide)))

theorem fz2_96_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨62, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 62 (by decide)))

theorem fz2_96_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨63, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 63 (by decide)))

theorem fz2_96_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨64, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 64 (by decide)))

theorem fz2_96_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨65, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 65 (by decide)))

theorem fz2_96_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨66, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 66 (by decide)))

theorem fz2_96_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨67, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 67 (by decide)))

theorem fz2_96_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨68, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 68 (by decide)))

theorem fz2_96_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨69, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 69 (by decide)))

theorem fz2_96_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨70, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 70 (by decide)))

theorem fz2_96_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨71, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 71 (by decide)))

theorem fz2_96_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨72, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 72 (by decide)))

theorem fz2_96_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨73, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 73 (by decide)))

theorem fz2_96_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨74, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 74 (by decide)))

theorem fz2_96_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨75, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 75 (by decide)))

theorem fz2_96_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨76, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 76 (by decide)))

theorem fz2_96_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨77, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 77 (by decide)))

theorem fz2_96_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨78, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 78 (by decide)))

theorem fz2_96_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨79, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 79 (by decide)))

theorem fz2_96_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨80, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 80 (by decide)))

theorem fz2_96_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨81, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 81 (by decide)))

theorem fz2_96_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨82, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 82 (by decide)))

theorem fz2_96_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨83, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 83 (by decide)))

theorem fz2_96_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨84, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 84 (by decide)))

theorem fz2_96_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨85, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 85 (by decide)))

theorem fz2_96_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨86, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 86 (by decide)))

theorem fz2_96_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨87, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 87 (by decide)))

theorem fz2_96_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨88, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 88 (by decide)))

theorem fz2_96_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨89, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 89 (by decide)))

theorem fz2_96_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨90, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 90 (by decide)))

theorem fz2_96_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨91, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 91 (by decide)))

theorem fz2_96_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨92, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 92 (by decide)))

theorem fz2_96_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨93, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 93 (by decide)))

theorem fz2_96_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨94, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 94 (by decide)))

theorem fz2_96_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨95, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 95 (by decide)))

theorem fz2_96_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨97, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 97 (by decide)))

theorem fz2_96_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨98, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 98 (by decide)))

theorem fz2_96_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨99, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 99 (by decide)))

theorem fz2_96_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨100, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 100 (by decide)))

theorem fz2_96_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨101, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 101 (by decide)))

theorem fz2_96_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨102, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 102 (by decide)))

theorem fz2_96_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨103, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 103 (by decide)))

theorem fz2_96_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨104, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 104 (by decide)))

theorem fz2_96_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨105, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 105 (by decide)))

theorem fz2_96_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨106, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 106 (by decide)))

theorem fz2_96_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨107, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 107 (by decide)))

theorem fz2_96_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨108, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 108 (by decide)))

theorem fz2_96_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨109, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 109 (by decide)))

theorem fz2_96_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨110, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 110 (by decide)))

theorem fz2_96_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨111, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 111 (by decide)))

theorem fz2_96_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨112, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 112 (by decide)))

theorem fz2_96_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨113, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 113 (by decide)))

theorem fz2_96_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨114, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 114 (by decide)))

theorem fz2_96_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK96)) = 0 :=
  Q2.repsFixedCard2 rK96 ⟨115, by decide⟩ Q2.R96_2 Q2.hpxR96_2 Q2.hcardq96_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_96) 115 (by decide)))

end LeanDring.P5Presentation
