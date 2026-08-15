/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C034
import LeanDring.P5.Data.EntryK.C035
import LeanDring.P5.Data.EntryK.C036
import LeanDring.P5.Data.EntryK.C037
import LeanDring.P5.Data.EntryK.C038

/-!
# Species-table cells, off-support emptiness certificates, chunk 86

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

theorem fixz1_130 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 35, 37, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 93, 94, 95, 96, 97, 99, 101, 102, 103, 104, 105, 107, 108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK130) (retConj 1 (R130 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_130_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨1, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 1 (by decide)))

theorem fz1_130_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨2, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 2 (by decide)))

theorem fz1_130_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨4, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 4 (by decide)))

theorem fz1_130_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨5, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 5 (by decide)))

theorem fz1_130_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨6, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 6 (by decide)))

theorem fz1_130_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨7, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 7 (by decide)))

theorem fz1_130_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨8, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 8 (by decide)))

theorem fz1_130_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨9, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 9 (by decide)))

theorem fz1_130_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨11, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 11 (by decide)))

theorem fz1_130_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨13, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 13 (by decide)))

theorem fz1_130_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨14, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 14 (by decide)))

theorem fz1_130_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨15, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 15 (by decide)))

theorem fz1_130_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨16, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 16 (by decide)))

theorem fz1_130_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨17, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 17 (by decide)))

theorem fz1_130_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨18, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 18 (by decide)))

theorem fz1_130_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨19, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 19 (by decide)))

theorem fz1_130_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨20, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 20 (by decide)))

theorem fz1_130_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨22, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 22 (by decide)))

theorem fz1_130_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨23, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 23 (by decide)))

theorem fz1_130_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨24, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 24 (by decide)))

theorem fz1_130_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨25, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 25 (by decide)))

theorem fz1_130_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨26, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 26 (by decide)))

theorem fz1_130_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨27, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 27 (by decide)))

theorem fz1_130_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨28, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 28 (by decide)))

theorem fz1_130_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨29, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 29 (by decide)))

theorem fz1_130_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨31, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 31 (by decide)))

theorem fz1_130_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨32, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 32 (by decide)))

theorem fz1_130_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨33, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 33 (by decide)))

theorem fz1_130_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨34, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 34 (by decide)))

theorem fz1_130_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨35, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 35 (by decide)))

theorem fz1_130_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨37, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 37 (by decide)))

theorem fz1_130_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨39, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 39 (by decide)))

theorem fz1_130_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨40, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 40 (by decide)))

theorem fz1_130_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨41, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 41 (by decide)))

theorem fz1_130_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨42, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 42 (by decide)))

theorem fz1_130_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨43, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 43 (by decide)))

theorem fz1_130_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨45, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 45 (by decide)))

theorem fz1_130_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨46, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 46 (by decide)))

theorem fz1_130_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨47, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 47 (by decide)))

theorem fz1_130_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨48, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 48 (by decide)))

theorem fz1_130_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨49, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 49 (by decide)))

theorem fz1_130_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨50, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 50 (by decide)))

theorem fz1_130_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨51, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 51 (by decide)))

theorem fz1_130_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨54, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 54 (by decide)))

theorem fz1_130_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨55, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 55 (by decide)))

theorem fz1_130_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨56, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 56 (by decide)))

theorem fz1_130_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨57, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 57 (by decide)))

theorem fz1_130_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨58, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 58 (by decide)))

theorem fz1_130_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨59, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 59 (by decide)))

theorem fz1_130_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨60, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 60 (by decide)))

theorem fz1_130_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨61, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 61 (by decide)))

theorem fz1_130_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨62, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 62 (by decide)))

theorem fz1_130_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨63, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 63 (by decide)))

theorem fz1_130_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨64, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 64 (by decide)))

theorem fz1_130_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨65, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 65 (by decide)))

theorem fz1_130_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨66, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 66 (by decide)))

theorem fz1_130_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨67, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 67 (by decide)))

theorem fz1_130_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨68, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 68 (by decide)))

theorem fz1_130_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨69, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 69 (by decide)))

theorem fz1_130_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨70, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 70 (by decide)))

theorem fz1_130_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨71, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 71 (by decide)))

theorem fz1_130_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨72, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 72 (by decide)))

theorem fz1_130_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨73, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 73 (by decide)))

theorem fz1_130_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨74, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 74 (by decide)))

theorem fz1_130_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨75, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 75 (by decide)))

theorem fz1_130_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨76, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 76 (by decide)))

theorem fz1_130_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨77, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 77 (by decide)))

theorem fz1_130_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨78, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 78 (by decide)))

theorem fz1_130_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨79, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 79 (by decide)))

theorem fz1_130_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨80, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 80 (by decide)))

theorem fz1_130_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨81, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 81 (by decide)))

theorem fz1_130_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨83, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 83 (by decide)))

theorem fz1_130_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨84, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 84 (by decide)))

theorem fz1_130_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨85, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 85 (by decide)))

theorem fz1_130_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨86, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 86 (by decide)))

theorem fz1_130_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨87, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 87 (by decide)))

theorem fz1_130_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨88, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 88 (by decide)))

theorem fz1_130_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨89, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 89 (by decide)))

theorem fz1_130_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨90, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 90 (by decide)))

theorem fz1_130_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨91, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 91 (by decide)))

theorem fz1_130_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨93, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 93 (by decide)))

theorem fz1_130_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨94, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 94 (by decide)))

theorem fz1_130_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨95, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 95 (by decide)))

theorem fz1_130_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨96, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 96 (by decide)))

theorem fz1_130_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨97, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 97 (by decide)))

theorem fz1_130_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨99, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 99 (by decide)))

theorem fz1_130_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨101, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 101 (by decide)))

theorem fz1_130_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨102, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 102 (by decide)))

theorem fz1_130_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨103, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 103 (by decide)))

theorem fz1_130_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨104, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 104 (by decide)))

theorem fz1_130_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨105, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 105 (by decide)))

theorem fz1_130_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨107, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 107 (by decide)))

theorem fz1_130_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨108, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 108 (by decide)))

theorem fz1_130_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨109, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 109 (by decide)))

theorem fz1_130_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨110, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 110 (by decide)))

theorem fz1_130_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨111, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 111 (by decide)))

theorem fz1_130_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨112, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 112 (by decide)))

theorem fz1_130_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨113, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 113 (by decide)))

theorem fz1_130_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨115, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 115 (by decide)))

theorem fz1_130_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨116, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 116 (by decide)))

theorem fz1_130_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨117, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 117 (by decide)))

theorem fz1_130_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨118, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 118 (by decide)))

theorem fz1_130_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨119, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 119 (by decide)))

theorem fz1_130_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨120, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 120 (by decide)))

theorem fz1_130_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨121, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 121 (by decide)))

theorem fz1_130_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨122, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 122 (by decide)))

theorem fz1_130_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨123, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 123 (by decide)))

theorem fz1_130_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨124, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 124 (by decide)))

theorem fz1_130_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨125, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 125 (by decide)))

theorem fz1_130_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨126, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 126 (by decide)))

theorem fz1_130_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨127, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 127 (by decide)))

theorem fz1_130_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨128, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 128 (by decide)))

theorem fz1_130_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨129, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 129 (by decide)))

theorem fz1_130_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨131, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 131 (by decide)))

theorem fz1_130_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨132, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 132 (by decide)))

theorem fz1_130_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨133, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 133 (by decide)))

theorem fz1_130_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨134, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 134 (by decide)))

theorem fz1_130_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨135, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 135 (by decide)))

theorem fz1_130_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨136, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 136 (by decide)))

theorem fz1_130_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨137, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 137 (by decide)))

theorem fz1_130_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨138, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 138 (by decide)))

theorem fz1_130_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨139, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 139 (by decide)))

theorem fz1_130_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨140, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 140 (by decide)))

theorem fz1_130_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨141, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 141 (by decide)))

theorem fz1_130_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨142, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 142 (by decide)))

theorem fz1_130_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨143, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 143 (by decide)))

theorem fz1_130_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨144, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 144 (by decide)))

theorem fz1_130_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨145, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 145 (by decide)))

theorem fz1_130_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK130)) = 0 :=
  repsFixedCard rK130 ⟨146, by decide⟩ R130 hpxR130 hcardq130
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_130) 146 (by decide)))

theorem fixz2_130 : ([1, 2, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 35, 37, 39, 40, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 86, 87, 88, 89, 90, 91, 93, 94, 95, 96, 97, 99, 101, 102, 103, 104, 105, 107, 108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK130) (retConj 2 (Q2.R130_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_130_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨1, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 1 (by decide)))

theorem fz2_130_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨2, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 2 (by decide)))

theorem fz2_130_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨4, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 4 (by decide)))

theorem fz2_130_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨5, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 5 (by decide)))

theorem fz2_130_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨6, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 6 (by decide)))

theorem fz2_130_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨7, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 7 (by decide)))

theorem fz2_130_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨8, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 8 (by decide)))

theorem fz2_130_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨9, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 9 (by decide)))

theorem fz2_130_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨11, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 11 (by decide)))

theorem fz2_130_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨13, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 13 (by decide)))

theorem fz2_130_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨14, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 14 (by decide)))

theorem fz2_130_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨15, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 15 (by decide)))

theorem fz2_130_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨16, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 16 (by decide)))

theorem fz2_130_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨17, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 17 (by decide)))

theorem fz2_130_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨18, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 18 (by decide)))

theorem fz2_130_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨19, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 19 (by decide)))

theorem fz2_130_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨20, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 20 (by decide)))

theorem fz2_130_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨22, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 22 (by decide)))

theorem fz2_130_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨23, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 23 (by decide)))

theorem fz2_130_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨24, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 24 (by decide)))

theorem fz2_130_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨25, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 25 (by decide)))

theorem fz2_130_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨26, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 26 (by decide)))

theorem fz2_130_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨27, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 27 (by decide)))

theorem fz2_130_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨28, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 28 (by decide)))

theorem fz2_130_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨29, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 29 (by decide)))

theorem fz2_130_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨31, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 31 (by decide)))

theorem fz2_130_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨32, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 32 (by decide)))

theorem fz2_130_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨33, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 33 (by decide)))

theorem fz2_130_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨34, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 34 (by decide)))

theorem fz2_130_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨35, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 35 (by decide)))

theorem fz2_130_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨37, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 37 (by decide)))

theorem fz2_130_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨39, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 39 (by decide)))

theorem fz2_130_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨40, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 40 (by decide)))

theorem fz2_130_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨41, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 41 (by decide)))

theorem fz2_130_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨42, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 42 (by decide)))

theorem fz2_130_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨43, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 43 (by decide)))

theorem fz2_130_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨45, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 45 (by decide)))

theorem fz2_130_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨46, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 46 (by decide)))

theorem fz2_130_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨47, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 47 (by decide)))

theorem fz2_130_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨48, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 48 (by decide)))

theorem fz2_130_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨49, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 49 (by decide)))

theorem fz2_130_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨50, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 50 (by decide)))

theorem fz2_130_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨51, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 51 (by decide)))

theorem fz2_130_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨54, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 54 (by decide)))

theorem fz2_130_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨55, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 55 (by decide)))

theorem fz2_130_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨56, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 56 (by decide)))

theorem fz2_130_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨57, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 57 (by decide)))

theorem fz2_130_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨58, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 58 (by decide)))

theorem fz2_130_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨59, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 59 (by decide)))

theorem fz2_130_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨60, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 60 (by decide)))

theorem fz2_130_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨61, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 61 (by decide)))

theorem fz2_130_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨62, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 62 (by decide)))

theorem fz2_130_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨63, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 63 (by decide)))

theorem fz2_130_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨64, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 64 (by decide)))

theorem fz2_130_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨65, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 65 (by decide)))

theorem fz2_130_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨66, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 66 (by decide)))

theorem fz2_130_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨67, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 67 (by decide)))

theorem fz2_130_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨68, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 68 (by decide)))

theorem fz2_130_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨69, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 69 (by decide)))

theorem fz2_130_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨70, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 70 (by decide)))

theorem fz2_130_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨71, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 71 (by decide)))

theorem fz2_130_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨72, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 72 (by decide)))

theorem fz2_130_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨73, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 73 (by decide)))

theorem fz2_130_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨74, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 74 (by decide)))

theorem fz2_130_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨75, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 75 (by decide)))

theorem fz2_130_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨76, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 76 (by decide)))

theorem fz2_130_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨77, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 77 (by decide)))

theorem fz2_130_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨78, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 78 (by decide)))

theorem fz2_130_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨79, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 79 (by decide)))

theorem fz2_130_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨80, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 80 (by decide)))

theorem fz2_130_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨81, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 81 (by decide)))

theorem fz2_130_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨83, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 83 (by decide)))

theorem fz2_130_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨84, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 84 (by decide)))

theorem fz2_130_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨85, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 85 (by decide)))

theorem fz2_130_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨86, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 86 (by decide)))

theorem fz2_130_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨87, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 87 (by decide)))

theorem fz2_130_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨88, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 88 (by decide)))

theorem fz2_130_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨89, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 89 (by decide)))

theorem fz2_130_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨90, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 90 (by decide)))

theorem fz2_130_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨91, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 91 (by decide)))

theorem fz2_130_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨93, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 93 (by decide)))

theorem fz2_130_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨94, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 94 (by decide)))

theorem fz2_130_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨95, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 95 (by decide)))

theorem fz2_130_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨96, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 96 (by decide)))

theorem fz2_130_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨97, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 97 (by decide)))

theorem fz2_130_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨99, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 99 (by decide)))

theorem fz2_130_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨101, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 101 (by decide)))

theorem fz2_130_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨102, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 102 (by decide)))

theorem fz2_130_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨103, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 103 (by decide)))

theorem fz2_130_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨104, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 104 (by decide)))

theorem fz2_130_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨105, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 105 (by decide)))

theorem fz2_130_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨107, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 107 (by decide)))

theorem fz2_130_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨108, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 108 (by decide)))

theorem fz2_130_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨109, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 109 (by decide)))

theorem fz2_130_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨110, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 110 (by decide)))

theorem fz2_130_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨111, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 111 (by decide)))

theorem fz2_130_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨112, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 112 (by decide)))

theorem fz2_130_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨113, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 113 (by decide)))

theorem fz2_130_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨115, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 115 (by decide)))

theorem fz2_130_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨116, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 116 (by decide)))

theorem fz2_130_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨117, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 117 (by decide)))

theorem fz2_130_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨118, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 118 (by decide)))

theorem fz2_130_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨119, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 119 (by decide)))

theorem fz2_130_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨120, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 120 (by decide)))

theorem fz2_130_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨121, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 121 (by decide)))

theorem fz2_130_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨122, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 122 (by decide)))

theorem fz2_130_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨123, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 123 (by decide)))

theorem fz2_130_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨124, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 124 (by decide)))

theorem fz2_130_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨125, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 125 (by decide)))

theorem fz2_130_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨126, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 126 (by decide)))

theorem fz2_130_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨127, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 127 (by decide)))

theorem fz2_130_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨128, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 128 (by decide)))

theorem fz2_130_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨129, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 129 (by decide)))

theorem fz2_130_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨131, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 131 (by decide)))

theorem fz2_130_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨132, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 132 (by decide)))

theorem fz2_130_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨133, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 133 (by decide)))

theorem fz2_130_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨134, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 134 (by decide)))

theorem fz2_130_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨135, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 135 (by decide)))

theorem fz2_130_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨136, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 136 (by decide)))

theorem fz2_130_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨137, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 137 (by decide)))

theorem fz2_130_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨138, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 138 (by decide)))

theorem fz2_130_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨139, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 139 (by decide)))

theorem fz2_130_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨140, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 140 (by decide)))

theorem fz2_130_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨141, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 141 (by decide)))

theorem fz2_130_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨142, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 142 (by decide)))

theorem fz2_130_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨143, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 143 (by decide)))

theorem fz2_130_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨144, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 144 (by decide)))

theorem fz2_130_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨145, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 145 (by decide)))

theorem fz2_130_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK130)) = 0 :=
  Q2.repsFixedCard2 rK130 ⟨146, by decide⟩ Q2.R130_2 Q2.hpxR130_2 Q2.hcardq130_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_130) 146 (by decide)))

theorem fixz1_131 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 91, 93, 94, 95, 97, 98, 99, 100, 101, 102, 103, 105, 106, 107, 109, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK131) (retConj 1 (R131 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_131_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨1, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 1 (by decide)))

theorem fz1_131_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨2, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 2 (by decide)))

theorem fz1_131_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨3, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 3 (by decide)))

theorem fz1_131_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨5, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 5 (by decide)))

theorem fz1_131_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨6, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 6 (by decide)))

theorem fz1_131_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨7, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 7 (by decide)))

theorem fz1_131_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨8, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 8 (by decide)))

theorem fz1_131_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨9, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 9 (by decide)))

theorem fz1_131_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨11, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 11 (by decide)))

theorem fz1_131_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨13, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 13 (by decide)))

theorem fz1_131_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨14, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 14 (by decide)))

theorem fz1_131_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨15, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 15 (by decide)))

theorem fz1_131_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨16, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 16 (by decide)))

theorem fz1_131_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨17, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 17 (by decide)))

theorem fz1_131_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨18, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 18 (by decide)))

theorem fz1_131_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨19, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 19 (by decide)))

theorem fz1_131_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨20, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 20 (by decide)))

theorem fz1_131_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨21, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 21 (by decide)))

theorem fz1_131_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨23, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 23 (by decide)))

theorem fz1_131_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨24, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 24 (by decide)))

theorem fz1_131_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨25, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 25 (by decide)))

theorem fz1_131_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨26, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 26 (by decide)))

theorem fz1_131_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨27, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 27 (by decide)))

theorem fz1_131_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨28, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 28 (by decide)))

theorem fz1_131_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨29, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 29 (by decide)))

theorem fz1_131_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨31, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 31 (by decide)))

theorem fz1_131_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨32, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 32 (by decide)))

theorem fz1_131_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨33, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 33 (by decide)))

theorem fz1_131_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨35, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 35 (by decide)))

theorem fz1_131_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨36, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 36 (by decide)))

theorem fz1_131_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨37, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 37 (by decide)))

theorem fz1_131_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨38, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 38 (by decide)))

theorem fz1_131_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨39, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 39 (by decide)))

theorem fz1_131_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨40, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 40 (by decide)))

theorem fz1_131_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨41, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 41 (by decide)))

theorem fz1_131_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨43, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 43 (by decide)))

theorem fz1_131_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨44, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 44 (by decide)))

theorem fz1_131_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨45, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 45 (by decide)))

theorem fz1_131_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨47, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 47 (by decide)))

theorem fz1_131_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨49, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 49 (by decide)))

theorem fz1_131_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨50, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 50 (by decide)))

theorem fz1_131_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨51, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 51 (by decide)))

theorem fz1_131_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨52, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 52 (by decide)))

theorem fz1_131_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨54, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 54 (by decide)))

theorem fz1_131_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨55, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 55 (by decide)))

theorem fz1_131_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨56, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 56 (by decide)))

theorem fz1_131_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨57, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 57 (by decide)))

theorem fz1_131_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨58, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 58 (by decide)))

theorem fz1_131_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨59, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 59 (by decide)))

theorem fz1_131_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨60, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 60 (by decide)))

theorem fz1_131_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨61, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 61 (by decide)))

theorem fz1_131_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨62, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 62 (by decide)))

theorem fz1_131_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨63, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 63 (by decide)))

theorem fz1_131_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨64, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 64 (by decide)))

theorem fz1_131_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨65, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 65 (by decide)))

theorem fz1_131_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨66, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 66 (by decide)))

theorem fz1_131_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨67, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 67 (by decide)))

theorem fz1_131_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨68, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 68 (by decide)))

theorem fz1_131_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨69, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 69 (by decide)))

theorem fz1_131_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨70, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 70 (by decide)))

theorem fz1_131_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨71, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 71 (by decide)))

theorem fz1_131_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨72, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 72 (by decide)))

theorem fz1_131_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨73, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 73 (by decide)))

theorem fz1_131_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨74, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 74 (by decide)))

theorem fz1_131_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨75, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 75 (by decide)))

theorem fz1_131_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨76, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 76 (by decide)))

theorem fz1_131_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨77, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 77 (by decide)))

theorem fz1_131_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨78, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 78 (by decide)))

theorem fz1_131_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨79, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 79 (by decide)))

theorem fz1_131_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨80, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 80 (by decide)))

theorem fz1_131_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨81, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 81 (by decide)))

theorem fz1_131_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨82, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 82 (by decide)))

theorem fz1_131_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨84, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 84 (by decide)))

theorem fz1_131_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨85, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 85 (by decide)))

theorem fz1_131_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨86, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 86 (by decide)))

theorem fz1_131_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨87, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 87 (by decide)))

theorem fz1_131_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨88, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 88 (by decide)))

theorem fz1_131_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨89, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 89 (by decide)))

theorem fz1_131_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨90, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 90 (by decide)))

theorem fz1_131_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨91, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 91 (by decide)))

theorem fz1_131_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨93, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 93 (by decide)))

theorem fz1_131_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨94, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 94 (by decide)))

theorem fz1_131_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨95, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 95 (by decide)))

theorem fz1_131_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨97, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 97 (by decide)))

theorem fz1_131_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨98, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 98 (by decide)))

theorem fz1_131_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨99, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 99 (by decide)))

theorem fz1_131_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨100, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 100 (by decide)))

theorem fz1_131_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨101, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 101 (by decide)))

theorem fz1_131_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨102, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 102 (by decide)))

theorem fz1_131_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨103, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 103 (by decide)))

theorem fz1_131_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨105, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 105 (by decide)))

theorem fz1_131_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨106, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 106 (by decide)))

theorem fz1_131_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨107, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 107 (by decide)))

theorem fz1_131_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨109, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 109 (by decide)))

theorem fz1_131_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨111, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 111 (by decide)))

theorem fz1_131_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨112, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 112 (by decide)))

theorem fz1_131_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨113, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 113 (by decide)))

theorem fz1_131_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨114, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 114 (by decide)))

theorem fz1_131_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨115, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 115 (by decide)))

theorem fz1_131_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨116, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 116 (by decide)))

theorem fz1_131_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨117, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 117 (by decide)))

theorem fz1_131_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨118, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 118 (by decide)))

theorem fz1_131_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨119, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 119 (by decide)))

theorem fz1_131_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨120, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 120 (by decide)))

theorem fz1_131_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨121, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 121 (by decide)))

theorem fz1_131_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨122, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 122 (by decide)))

theorem fz1_131_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨123, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 123 (by decide)))

theorem fz1_131_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨124, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 124 (by decide)))

theorem fz1_131_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨125, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 125 (by decide)))

theorem fz1_131_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨126, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 126 (by decide)))

theorem fz1_131_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨127, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 127 (by decide)))

theorem fz1_131_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨128, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 128 (by decide)))

theorem fz1_131_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨129, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 129 (by decide)))

theorem fz1_131_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨130, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 130 (by decide)))

theorem fz1_131_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨132, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 132 (by decide)))

theorem fz1_131_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨133, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 133 (by decide)))

theorem fz1_131_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨134, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 134 (by decide)))

theorem fz1_131_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨135, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 135 (by decide)))

theorem fz1_131_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨136, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 136 (by decide)))

theorem fz1_131_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨137, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 137 (by decide)))

theorem fz1_131_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨138, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 138 (by decide)))

theorem fz1_131_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨139, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 139 (by decide)))

theorem fz1_131_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨140, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 140 (by decide)))

theorem fz1_131_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨141, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 141 (by decide)))

theorem fz1_131_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨142, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 142 (by decide)))

theorem fz1_131_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨143, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 143 (by decide)))

theorem fz1_131_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨144, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 144 (by decide)))

theorem fz1_131_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨145, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 145 (by decide)))

theorem fz1_131_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK131)) = 0 :=
  repsFixedCard rK131 ⟨146, by decide⟩ R131 hpxR131 hcardq131
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_131) 146 (by decide)))

theorem fixz2_131 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 47, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 91, 93, 94, 95, 97, 98, 99, 100, 101, 102, 103, 105, 106, 107, 109, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK131) (retConj 2 (Q2.R131_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_131_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨1, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 1 (by decide)))

theorem fz2_131_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨2, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 2 (by decide)))

theorem fz2_131_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨3, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 3 (by decide)))

theorem fz2_131_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨5, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 5 (by decide)))

theorem fz2_131_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨6, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 6 (by decide)))

theorem fz2_131_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨7, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 7 (by decide)))

theorem fz2_131_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨8, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 8 (by decide)))

theorem fz2_131_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨9, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 9 (by decide)))

theorem fz2_131_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨11, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 11 (by decide)))

theorem fz2_131_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨13, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 13 (by decide)))

theorem fz2_131_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨14, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 14 (by decide)))

theorem fz2_131_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨15, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 15 (by decide)))

theorem fz2_131_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨16, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 16 (by decide)))

theorem fz2_131_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨17, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 17 (by decide)))

theorem fz2_131_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨18, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 18 (by decide)))

theorem fz2_131_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨19, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 19 (by decide)))

theorem fz2_131_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨20, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 20 (by decide)))

theorem fz2_131_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨21, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 21 (by decide)))

theorem fz2_131_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨23, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 23 (by decide)))

theorem fz2_131_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨24, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 24 (by decide)))

theorem fz2_131_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨25, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 25 (by decide)))

theorem fz2_131_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨26, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 26 (by decide)))

theorem fz2_131_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨27, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 27 (by decide)))

theorem fz2_131_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨28, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 28 (by decide)))

theorem fz2_131_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨29, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 29 (by decide)))

theorem fz2_131_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨31, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 31 (by decide)))

theorem fz2_131_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨32, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 32 (by decide)))

theorem fz2_131_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨33, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 33 (by decide)))

theorem fz2_131_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨35, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 35 (by decide)))

theorem fz2_131_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨36, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 36 (by decide)))

theorem fz2_131_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨37, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 37 (by decide)))

theorem fz2_131_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨38, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 38 (by decide)))

theorem fz2_131_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨39, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 39 (by decide)))

theorem fz2_131_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨40, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 40 (by decide)))

theorem fz2_131_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨41, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 41 (by decide)))

theorem fz2_131_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨43, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 43 (by decide)))

theorem fz2_131_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨44, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 44 (by decide)))

theorem fz2_131_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨45, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 45 (by decide)))

theorem fz2_131_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨47, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 47 (by decide)))

theorem fz2_131_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨49, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 49 (by decide)))

theorem fz2_131_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨50, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 50 (by decide)))

theorem fz2_131_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨51, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 51 (by decide)))

theorem fz2_131_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨52, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 52 (by decide)))

theorem fz2_131_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨54, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 54 (by decide)))

theorem fz2_131_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨55, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 55 (by decide)))

theorem fz2_131_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨56, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 56 (by decide)))

theorem fz2_131_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨57, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 57 (by decide)))

theorem fz2_131_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨58, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 58 (by decide)))

theorem fz2_131_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨59, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 59 (by decide)))

theorem fz2_131_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨60, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 60 (by decide)))

theorem fz2_131_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨61, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 61 (by decide)))

theorem fz2_131_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨62, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 62 (by decide)))

theorem fz2_131_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨63, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 63 (by decide)))

theorem fz2_131_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨64, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 64 (by decide)))

theorem fz2_131_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨65, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 65 (by decide)))

theorem fz2_131_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨66, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 66 (by decide)))

theorem fz2_131_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨67, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 67 (by decide)))

theorem fz2_131_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨68, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 68 (by decide)))

theorem fz2_131_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨69, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 69 (by decide)))

theorem fz2_131_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨70, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 70 (by decide)))

theorem fz2_131_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨71, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 71 (by decide)))

theorem fz2_131_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨72, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 72 (by decide)))

theorem fz2_131_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨73, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 73 (by decide)))

theorem fz2_131_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨74, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 74 (by decide)))

theorem fz2_131_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨75, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 75 (by decide)))

theorem fz2_131_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨76, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 76 (by decide)))

theorem fz2_131_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨77, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 77 (by decide)))

theorem fz2_131_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨78, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 78 (by decide)))

theorem fz2_131_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨79, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 79 (by decide)))

theorem fz2_131_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨80, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 80 (by decide)))

theorem fz2_131_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨81, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 81 (by decide)))

theorem fz2_131_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨82, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 82 (by decide)))

theorem fz2_131_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨84, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 84 (by decide)))

theorem fz2_131_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨85, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 85 (by decide)))

theorem fz2_131_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨86, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 86 (by decide)))

theorem fz2_131_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨87, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 87 (by decide)))

theorem fz2_131_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨88, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 88 (by decide)))

theorem fz2_131_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨89, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 89 (by decide)))

theorem fz2_131_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨90, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 90 (by decide)))

theorem fz2_131_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨91, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 91 (by decide)))

theorem fz2_131_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨93, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 93 (by decide)))

theorem fz2_131_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨94, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 94 (by decide)))

theorem fz2_131_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨95, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 95 (by decide)))

theorem fz2_131_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨97, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 97 (by decide)))

theorem fz2_131_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨98, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 98 (by decide)))

theorem fz2_131_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨99, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 99 (by decide)))

theorem fz2_131_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨100, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 100 (by decide)))

theorem fz2_131_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨101, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 101 (by decide)))

theorem fz2_131_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨102, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 102 (by decide)))

theorem fz2_131_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨103, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 103 (by decide)))

theorem fz2_131_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨105, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 105 (by decide)))

theorem fz2_131_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨106, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 106 (by decide)))

theorem fz2_131_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨107, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 107 (by decide)))

theorem fz2_131_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨109, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 109 (by decide)))

theorem fz2_131_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨111, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 111 (by decide)))

theorem fz2_131_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨112, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 112 (by decide)))

theorem fz2_131_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨113, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 113 (by decide)))

theorem fz2_131_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨114, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 114 (by decide)))

theorem fz2_131_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨115, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 115 (by decide)))

theorem fz2_131_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨116, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 116 (by decide)))

theorem fz2_131_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨117, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 117 (by decide)))

theorem fz2_131_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨118, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 118 (by decide)))

theorem fz2_131_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨119, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 119 (by decide)))

theorem fz2_131_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨120, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 120 (by decide)))

theorem fz2_131_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨121, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 121 (by decide)))

theorem fz2_131_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨122, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 122 (by decide)))

theorem fz2_131_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨123, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 123 (by decide)))

theorem fz2_131_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨124, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 124 (by decide)))

theorem fz2_131_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨125, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 125 (by decide)))

theorem fz2_131_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨126, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 126 (by decide)))

theorem fz2_131_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨127, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 127 (by decide)))

theorem fz2_131_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨128, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 128 (by decide)))

theorem fz2_131_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨129, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 129 (by decide)))

theorem fz2_131_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨130, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 130 (by decide)))

theorem fz2_131_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨132, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 132 (by decide)))

theorem fz2_131_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨133, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 133 (by decide)))

theorem fz2_131_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨134, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 134 (by decide)))

theorem fz2_131_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨135, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 135 (by decide)))

theorem fz2_131_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨136, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 136 (by decide)))

theorem fz2_131_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨137, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 137 (by decide)))

theorem fz2_131_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨138, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 138 (by decide)))

theorem fz2_131_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨139, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 139 (by decide)))

theorem fz2_131_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨140, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 140 (by decide)))

theorem fz2_131_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨141, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 141 (by decide)))

theorem fz2_131_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨142, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 142 (by decide)))

theorem fz2_131_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨143, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 143 (by decide)))

theorem fz2_131_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨144, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 144 (by decide)))

theorem fz2_131_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨145, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 145 (by decide)))

theorem fz2_131_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK131)) = 0 :=
  Q2.repsFixedCard2 rK131 ⟨146, by decide⟩ Q2.R131_2 Q2.hpxR131_2 Q2.hcardq131_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_131) 146 (by decide)))

theorem fixz1_132 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 98, 99, 101, 102, 103, 104, 105, 106, 107, 108, 110, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK132) (retConj 1 (R132 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_132_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨1, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 1 (by decide)))

theorem fz1_132_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨2, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 2 (by decide)))

theorem fz1_132_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨3, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 3 (by decide)))

theorem fz1_132_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨5, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 5 (by decide)))

theorem fz1_132_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨6, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 6 (by decide)))

theorem fz1_132_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨7, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 7 (by decide)))

theorem fz1_132_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨8, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 8 (by decide)))

theorem fz1_132_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨9, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 9 (by decide)))

theorem fz1_132_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨11, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 11 (by decide)))

theorem fz1_132_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨13, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 13 (by decide)))

theorem fz1_132_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨14, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 14 (by decide)))

theorem fz1_132_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨15, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 15 (by decide)))

theorem fz1_132_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨16, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 16 (by decide)))

theorem fz1_132_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨17, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 17 (by decide)))

theorem fz1_132_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨18, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 18 (by decide)))

theorem fz1_132_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨19, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 19 (by decide)))

theorem fz1_132_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨20, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 20 (by decide)))

theorem fz1_132_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨21, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 21 (by decide)))

theorem fz1_132_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨23, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 23 (by decide)))

theorem fz1_132_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨24, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 24 (by decide)))

theorem fz1_132_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨25, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 25 (by decide)))

theorem fz1_132_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨26, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 26 (by decide)))

theorem fz1_132_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨27, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 27 (by decide)))

theorem fz1_132_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨28, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 28 (by decide)))

theorem fz1_132_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨29, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 29 (by decide)))

theorem fz1_132_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨30, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 30 (by decide)))

theorem fz1_132_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨32, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 32 (by decide)))

theorem fz1_132_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨33, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 33 (by decide)))

theorem fz1_132_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨34, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 34 (by decide)))

theorem fz1_132_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨36, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 36 (by decide)))

theorem fz1_132_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨37, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 37 (by decide)))

theorem fz1_132_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨39, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 39 (by decide)))

theorem fz1_132_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨40, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 40 (by decide)))

theorem fz1_132_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨41, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 41 (by decide)))

theorem fz1_132_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨42, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 42 (by decide)))

theorem fz1_132_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨43, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 43 (by decide)))

theorem fz1_132_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨44, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 44 (by decide)))

theorem fz1_132_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨45, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 45 (by decide)))

theorem fz1_132_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨46, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 46 (by decide)))

theorem fz1_132_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨48, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 48 (by decide)))

theorem fz1_132_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨50, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 50 (by decide)))

theorem fz1_132_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨51, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 51 (by decide)))

theorem fz1_132_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨52, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 52 (by decide)))

theorem fz1_132_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨54, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 54 (by decide)))

theorem fz1_132_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨55, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 55 (by decide)))

theorem fz1_132_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨56, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 56 (by decide)))

theorem fz1_132_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨57, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 57 (by decide)))

theorem fz1_132_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨58, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 58 (by decide)))

theorem fz1_132_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨59, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 59 (by decide)))

theorem fz1_132_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨60, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 60 (by decide)))

theorem fz1_132_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨61, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 61 (by decide)))

theorem fz1_132_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨62, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 62 (by decide)))

theorem fz1_132_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨63, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 63 (by decide)))

theorem fz1_132_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨64, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 64 (by decide)))

theorem fz1_132_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨65, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 65 (by decide)))

theorem fz1_132_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨66, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 66 (by decide)))

theorem fz1_132_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨67, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 67 (by decide)))

theorem fz1_132_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨68, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 68 (by decide)))

theorem fz1_132_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨69, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 69 (by decide)))

theorem fz1_132_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨70, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 70 (by decide)))

theorem fz1_132_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨71, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 71 (by decide)))

theorem fz1_132_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨72, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 72 (by decide)))

theorem fz1_132_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨73, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 73 (by decide)))

theorem fz1_132_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨74, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 74 (by decide)))

theorem fz1_132_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨75, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 75 (by decide)))

theorem fz1_132_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨76, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 76 (by decide)))

theorem fz1_132_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨77, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 77 (by decide)))

theorem fz1_132_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨78, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 78 (by decide)))

theorem fz1_132_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨79, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 79 (by decide)))

theorem fz1_132_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨80, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 80 (by decide)))

theorem fz1_132_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨81, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 81 (by decide)))

theorem fz1_132_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨82, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 82 (by decide)))

theorem fz1_132_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨84, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 84 (by decide)))

theorem fz1_132_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨85, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 85 (by decide)))

theorem fz1_132_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨86, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 86 (by decide)))

theorem fz1_132_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨87, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 87 (by decide)))

theorem fz1_132_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨88, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 88 (by decide)))

theorem fz1_132_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨89, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 89 (by decide)))

theorem fz1_132_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨90, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 90 (by decide)))

theorem fz1_132_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨91, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 91 (by decide)))

theorem fz1_132_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨92, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 92 (by decide)))

theorem fz1_132_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨94, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 94 (by decide)))

theorem fz1_132_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨95, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 95 (by decide)))

theorem fz1_132_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨96, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 96 (by decide)))

theorem fz1_132_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨98, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 98 (by decide)))

theorem fz1_132_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨99, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 99 (by decide)))

theorem fz1_132_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨101, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 101 (by decide)))

theorem fz1_132_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨102, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 102 (by decide)))

theorem fz1_132_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨103, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 103 (by decide)))

theorem fz1_132_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨104, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 104 (by decide)))

theorem fz1_132_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨105, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 105 (by decide)))

theorem fz1_132_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨106, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 106 (by decide)))

theorem fz1_132_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨107, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 107 (by decide)))

theorem fz1_132_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨108, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 108 (by decide)))

theorem fz1_132_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨110, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 110 (by decide)))

theorem fz1_132_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨112, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 112 (by decide)))

theorem fz1_132_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨113, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 113 (by decide)))

theorem fz1_132_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨114, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 114 (by decide)))

theorem fz1_132_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨115, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 115 (by decide)))

theorem fz1_132_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨116, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 116 (by decide)))

theorem fz1_132_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨117, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 117 (by decide)))

theorem fz1_132_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨118, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 118 (by decide)))

theorem fz1_132_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨119, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 119 (by decide)))

theorem fz1_132_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨120, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 120 (by decide)))

theorem fz1_132_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨121, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 121 (by decide)))

theorem fz1_132_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨122, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 122 (by decide)))

theorem fz1_132_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨123, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 123 (by decide)))

theorem fz1_132_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨124, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 124 (by decide)))

theorem fz1_132_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨125, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 125 (by decide)))

theorem fz1_132_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨126, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 126 (by decide)))

theorem fz1_132_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨127, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 127 (by decide)))

theorem fz1_132_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨128, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 128 (by decide)))

theorem fz1_132_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨129, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 129 (by decide)))

theorem fz1_132_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨130, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 130 (by decide)))

theorem fz1_132_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨131, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 131 (by decide)))

theorem fz1_132_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨133, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 133 (by decide)))

theorem fz1_132_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨134, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 134 (by decide)))

theorem fz1_132_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨135, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 135 (by decide)))

theorem fz1_132_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨136, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 136 (by decide)))

theorem fz1_132_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨137, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 137 (by decide)))

theorem fz1_132_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨138, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 138 (by decide)))

theorem fz1_132_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨139, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 139 (by decide)))

theorem fz1_132_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨140, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 140 (by decide)))

theorem fz1_132_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨141, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 141 (by decide)))

theorem fz1_132_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨142, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 142 (by decide)))

theorem fz1_132_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨143, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 143 (by decide)))

theorem fz1_132_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨144, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 144 (by decide)))

theorem fz1_132_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨145, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 145 (by decide)))

theorem fz1_132_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK132)) = 0 :=
  repsFixedCard rK132 ⟨146, by decide⟩ R132 hpxR132 hcardq132
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_132) 146 (by decide)))

theorem fixz2_132 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 91, 92, 94, 95, 96, 98, 99, 101, 102, 103, 104, 105, 106, 107, 108, 110, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK132) (retConj 2 (Q2.R132_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_132_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨1, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 1 (by decide)))

theorem fz2_132_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨2, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 2 (by decide)))

theorem fz2_132_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨3, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 3 (by decide)))

theorem fz2_132_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨5, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 5 (by decide)))

theorem fz2_132_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨6, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 6 (by decide)))

theorem fz2_132_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨7, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 7 (by decide)))

theorem fz2_132_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨8, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 8 (by decide)))

theorem fz2_132_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨9, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 9 (by decide)))

theorem fz2_132_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨11, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 11 (by decide)))

theorem fz2_132_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨13, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 13 (by decide)))

theorem fz2_132_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨14, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 14 (by decide)))

theorem fz2_132_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨15, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 15 (by decide)))

theorem fz2_132_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨16, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 16 (by decide)))

theorem fz2_132_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨17, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 17 (by decide)))

theorem fz2_132_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨18, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 18 (by decide)))

theorem fz2_132_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨19, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 19 (by decide)))

theorem fz2_132_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨20, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 20 (by decide)))

theorem fz2_132_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨21, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 21 (by decide)))

theorem fz2_132_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨23, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 23 (by decide)))

theorem fz2_132_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨24, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 24 (by decide)))

theorem fz2_132_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨25, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 25 (by decide)))

theorem fz2_132_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨26, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 26 (by decide)))

theorem fz2_132_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨27, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 27 (by decide)))

theorem fz2_132_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨28, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 28 (by decide)))

theorem fz2_132_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨29, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 29 (by decide)))

theorem fz2_132_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨30, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 30 (by decide)))

theorem fz2_132_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨32, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 32 (by decide)))

theorem fz2_132_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨33, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 33 (by decide)))

theorem fz2_132_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨34, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 34 (by decide)))

theorem fz2_132_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨36, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 36 (by decide)))

theorem fz2_132_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨37, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 37 (by decide)))

theorem fz2_132_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨39, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 39 (by decide)))

theorem fz2_132_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨40, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 40 (by decide)))

theorem fz2_132_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨41, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 41 (by decide)))

theorem fz2_132_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨42, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 42 (by decide)))

theorem fz2_132_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨43, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 43 (by decide)))

theorem fz2_132_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨44, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 44 (by decide)))

theorem fz2_132_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨45, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 45 (by decide)))

theorem fz2_132_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨46, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 46 (by decide)))

theorem fz2_132_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨48, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 48 (by decide)))

theorem fz2_132_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨50, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 50 (by decide)))

theorem fz2_132_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨51, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 51 (by decide)))

theorem fz2_132_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨52, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 52 (by decide)))

theorem fz2_132_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨54, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 54 (by decide)))

theorem fz2_132_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨55, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 55 (by decide)))

theorem fz2_132_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨56, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 56 (by decide)))

theorem fz2_132_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨57, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 57 (by decide)))

theorem fz2_132_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨58, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 58 (by decide)))

theorem fz2_132_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨59, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 59 (by decide)))

theorem fz2_132_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨60, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 60 (by decide)))

theorem fz2_132_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨61, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 61 (by decide)))

theorem fz2_132_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨62, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 62 (by decide)))

theorem fz2_132_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨63, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 63 (by decide)))

theorem fz2_132_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨64, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 64 (by decide)))

theorem fz2_132_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨65, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 65 (by decide)))

theorem fz2_132_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨66, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 66 (by decide)))

theorem fz2_132_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨67, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 67 (by decide)))

theorem fz2_132_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨68, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 68 (by decide)))

theorem fz2_132_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨69, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 69 (by decide)))

theorem fz2_132_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨70, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 70 (by decide)))

theorem fz2_132_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨71, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 71 (by decide)))

theorem fz2_132_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨72, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 72 (by decide)))

theorem fz2_132_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨73, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 73 (by decide)))

theorem fz2_132_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨74, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 74 (by decide)))

theorem fz2_132_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨75, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 75 (by decide)))

theorem fz2_132_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨76, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 76 (by decide)))

theorem fz2_132_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨77, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 77 (by decide)))

theorem fz2_132_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨78, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 78 (by decide)))

theorem fz2_132_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨79, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 79 (by decide)))

theorem fz2_132_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨80, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 80 (by decide)))

theorem fz2_132_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨81, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 81 (by decide)))

theorem fz2_132_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨82, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 82 (by decide)))

theorem fz2_132_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨84, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 84 (by decide)))

theorem fz2_132_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨85, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 85 (by decide)))

theorem fz2_132_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨86, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 86 (by decide)))

theorem fz2_132_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨87, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 87 (by decide)))

theorem fz2_132_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨88, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 88 (by decide)))

theorem fz2_132_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨89, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 89 (by decide)))

theorem fz2_132_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨90, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 90 (by decide)))

theorem fz2_132_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨91, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 91 (by decide)))

theorem fz2_132_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨92, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 92 (by decide)))

theorem fz2_132_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨94, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 94 (by decide)))

theorem fz2_132_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨95, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 95 (by decide)))

theorem fz2_132_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨96, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 96 (by decide)))

theorem fz2_132_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨98, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 98 (by decide)))

theorem fz2_132_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨99, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 99 (by decide)))

theorem fz2_132_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨101, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 101 (by decide)))

theorem fz2_132_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨102, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 102 (by decide)))

theorem fz2_132_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨103, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 103 (by decide)))

theorem fz2_132_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨104, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 104 (by decide)))

theorem fz2_132_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨105, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 105 (by decide)))

theorem fz2_132_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨106, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 106 (by decide)))

theorem fz2_132_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨107, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 107 (by decide)))

theorem fz2_132_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨108, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 108 (by decide)))

theorem fz2_132_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨110, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 110 (by decide)))

theorem fz2_132_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨112, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 112 (by decide)))

theorem fz2_132_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨113, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 113 (by decide)))

theorem fz2_132_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨114, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 114 (by decide)))

theorem fz2_132_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨115, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 115 (by decide)))

theorem fz2_132_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨116, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 116 (by decide)))

theorem fz2_132_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨117, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 117 (by decide)))

theorem fz2_132_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨118, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 118 (by decide)))

theorem fz2_132_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨119, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 119 (by decide)))

theorem fz2_132_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨120, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 120 (by decide)))

theorem fz2_132_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨121, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 121 (by decide)))

theorem fz2_132_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨122, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 122 (by decide)))

theorem fz2_132_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨123, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 123 (by decide)))

theorem fz2_132_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨124, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 124 (by decide)))

theorem fz2_132_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨125, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 125 (by decide)))

theorem fz2_132_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨126, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 126 (by decide)))

theorem fz2_132_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨127, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 127 (by decide)))

theorem fz2_132_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨128, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 128 (by decide)))

theorem fz2_132_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨129, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 129 (by decide)))

theorem fz2_132_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨130, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 130 (by decide)))

theorem fz2_132_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨131, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 131 (by decide)))

theorem fz2_132_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨133, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 133 (by decide)))

theorem fz2_132_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨134, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 134 (by decide)))

theorem fz2_132_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨135, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 135 (by decide)))

theorem fz2_132_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨136, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 136 (by decide)))

theorem fz2_132_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨137, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 137 (by decide)))

theorem fz2_132_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨138, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 138 (by decide)))

theorem fz2_132_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨139, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 139 (by decide)))

theorem fz2_132_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨140, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 140 (by decide)))

theorem fz2_132_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨141, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 141 (by decide)))

theorem fz2_132_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨142, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 142 (by decide)))

theorem fz2_132_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨143, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 143 (by decide)))

theorem fz2_132_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨144, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 144 (by decide)))

theorem fz2_132_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨145, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 145 (by decide)))

theorem fz2_132_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK132)) = 0 :=
  Q2.repsFixedCard2 rK132 ⟨146, by decide⟩ Q2.R132_2 Q2.hpxR132_2 Q2.hcardq132_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_132) 146 (by decide)))

theorem fixz1_133 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 37, 38, 40, 41, 42, 44, 45, 46, 47, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 97, 99, 100, 102, 103, 104, 106, 107, 108, 109, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK133) (retConj 1 (R133 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_133_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨1, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 1 (by decide)))

theorem fz1_133_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨2, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 2 (by decide)))

theorem fz1_133_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨3, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 3 (by decide)))

theorem fz1_133_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨5, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 5 (by decide)))

theorem fz1_133_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨6, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 6 (by decide)))

theorem fz1_133_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨7, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 7 (by decide)))

theorem fz1_133_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨8, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 8 (by decide)))

theorem fz1_133_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨9, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 9 (by decide)))

theorem fz1_133_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨11, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 11 (by decide)))

theorem fz1_133_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨13, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 13 (by decide)))

theorem fz1_133_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨14, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 14 (by decide)))

theorem fz1_133_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨15, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 15 (by decide)))

theorem fz1_133_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨16, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 16 (by decide)))

theorem fz1_133_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨17, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 17 (by decide)))

theorem fz1_133_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨18, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 18 (by decide)))

theorem fz1_133_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨19, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 19 (by decide)))

theorem fz1_133_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨20, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 20 (by decide)))

theorem fz1_133_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨21, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 21 (by decide)))

theorem fz1_133_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨23, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 23 (by decide)))

theorem fz1_133_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨24, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 24 (by decide)))

theorem fz1_133_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨25, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 25 (by decide)))

theorem fz1_133_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨26, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 26 (by decide)))

theorem fz1_133_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨27, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 27 (by decide)))

theorem fz1_133_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨28, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 28 (by decide)))

theorem fz1_133_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨29, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 29 (by decide)))

theorem fz1_133_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨30, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 30 (by decide)))

theorem fz1_133_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨31, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 31 (by decide)))

theorem fz1_133_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨33, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 33 (by decide)))

theorem fz1_133_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨34, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 34 (by decide)))

theorem fz1_133_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨35, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 35 (by decide)))

theorem fz1_133_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨37, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 37 (by decide)))

theorem fz1_133_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨38, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 38 (by decide)))

theorem fz1_133_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨40, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 40 (by decide)))

theorem fz1_133_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨41, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 41 (by decide)))

theorem fz1_133_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨42, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 42 (by decide)))

theorem fz1_133_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨44, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 44 (by decide)))

theorem fz1_133_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨45, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 45 (by decide)))

theorem fz1_133_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨46, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 46 (by decide)))

theorem fz1_133_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨47, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 47 (by decide)))

theorem fz1_133_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨48, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 48 (by decide)))

theorem fz1_133_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨49, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 49 (by decide)))

theorem fz1_133_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨51, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 51 (by decide)))

theorem fz1_133_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨52, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 52 (by decide)))

theorem fz1_133_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨54, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 54 (by decide)))

theorem fz1_133_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨55, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 55 (by decide)))

theorem fz1_133_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨56, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 56 (by decide)))

theorem fz1_133_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨57, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 57 (by decide)))

theorem fz1_133_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨58, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 58 (by decide)))

theorem fz1_133_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨59, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 59 (by decide)))

theorem fz1_133_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨60, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 60 (by decide)))

theorem fz1_133_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨61, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 61 (by decide)))

theorem fz1_133_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨62, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 62 (by decide)))

theorem fz1_133_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨63, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 63 (by decide)))

theorem fz1_133_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨64, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 64 (by decide)))

theorem fz1_133_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨65, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 65 (by decide)))

theorem fz1_133_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨66, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 66 (by decide)))

theorem fz1_133_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨67, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 67 (by decide)))

theorem fz1_133_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨68, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 68 (by decide)))

theorem fz1_133_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨69, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 69 (by decide)))

theorem fz1_133_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨70, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 70 (by decide)))

theorem fz1_133_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨71, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 71 (by decide)))

theorem fz1_133_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨72, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 72 (by decide)))

theorem fz1_133_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨73, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 73 (by decide)))

theorem fz1_133_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨74, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 74 (by decide)))

theorem fz1_133_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨75, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 75 (by decide)))

theorem fz1_133_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨76, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 76 (by decide)))

theorem fz1_133_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨77, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 77 (by decide)))

theorem fz1_133_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨78, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 78 (by decide)))

theorem fz1_133_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨79, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 79 (by decide)))

theorem fz1_133_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨80, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 80 (by decide)))

theorem fz1_133_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨81, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 81 (by decide)))

theorem fz1_133_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨82, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 82 (by decide)))

theorem fz1_133_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨84, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 84 (by decide)))

theorem fz1_133_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨85, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 85 (by decide)))

theorem fz1_133_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨86, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 86 (by decide)))

theorem fz1_133_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨87, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 87 (by decide)))

theorem fz1_133_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨88, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 88 (by decide)))

theorem fz1_133_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨89, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 89 (by decide)))

theorem fz1_133_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨90, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 90 (by decide)))

theorem fz1_133_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨91, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 91 (by decide)))

theorem fz1_133_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨92, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 92 (by decide)))

theorem fz1_133_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨93, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 93 (by decide)))

theorem fz1_133_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨95, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 95 (by decide)))

theorem fz1_133_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨96, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 96 (by decide)))

theorem fz1_133_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨97, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 97 (by decide)))

theorem fz1_133_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨99, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 99 (by decide)))

theorem fz1_133_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨100, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 100 (by decide)))

theorem fz1_133_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨102, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 102 (by decide)))

theorem fz1_133_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨103, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 103 (by decide)))

theorem fz1_133_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨104, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 104 (by decide)))

theorem fz1_133_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨106, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 106 (by decide)))

theorem fz1_133_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨107, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 107 (by decide)))

theorem fz1_133_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨108, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 108 (by decide)))

theorem fz1_133_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨109, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 109 (by decide)))

theorem fz1_133_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨110, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 110 (by decide)))

theorem fz1_133_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨111, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 111 (by decide)))

theorem fz1_133_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨113, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 113 (by decide)))

theorem fz1_133_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨114, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 114 (by decide)))

theorem fz1_133_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨115, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 115 (by decide)))

theorem fz1_133_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨116, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 116 (by decide)))

theorem fz1_133_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨117, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 117 (by decide)))

theorem fz1_133_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨118, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 118 (by decide)))

theorem fz1_133_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨119, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 119 (by decide)))

theorem fz1_133_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨120, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 120 (by decide)))

theorem fz1_133_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨121, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 121 (by decide)))

theorem fz1_133_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨122, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 122 (by decide)))

theorem fz1_133_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨123, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 123 (by decide)))

theorem fz1_133_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨124, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 124 (by decide)))

theorem fz1_133_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨125, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 125 (by decide)))

theorem fz1_133_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨126, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 126 (by decide)))

theorem fz1_133_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨127, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 127 (by decide)))

theorem fz1_133_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨128, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 128 (by decide)))

theorem fz1_133_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨129, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 129 (by decide)))

theorem fz1_133_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨130, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 130 (by decide)))

theorem fz1_133_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨131, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 131 (by decide)))

theorem fz1_133_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨132, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 132 (by decide)))

theorem fz1_133_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨134, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 134 (by decide)))

theorem fz1_133_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨135, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 135 (by decide)))

theorem fz1_133_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨136, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 136 (by decide)))

theorem fz1_133_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨137, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 137 (by decide)))

theorem fz1_133_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨138, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 138 (by decide)))

theorem fz1_133_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨139, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 139 (by decide)))

theorem fz1_133_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨140, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 140 (by decide)))

theorem fz1_133_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨141, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 141 (by decide)))

theorem fz1_133_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨142, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 142 (by decide)))

theorem fz1_133_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨143, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 143 (by decide)))

theorem fz1_133_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨144, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 144 (by decide)))

theorem fz1_133_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨145, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 145 (by decide)))

theorem fz1_133_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK133)) = 0 :=
  repsFixedCard rK133 ⟨146, by decide⟩ R133 hpxR133 hcardq133
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_133) 146 (by decide)))

theorem fixz2_133 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 34, 35, 37, 38, 40, 41, 42, 44, 45, 46, 47, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 95, 96, 97, 99, 100, 102, 103, 104, 106, 107, 108, 109, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK133) (retConj 2 (Q2.R133_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_133_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨1, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 1 (by decide)))

theorem fz2_133_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨2, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 2 (by decide)))

theorem fz2_133_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨3, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 3 (by decide)))

theorem fz2_133_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨5, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 5 (by decide)))

theorem fz2_133_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨6, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 6 (by decide)))

theorem fz2_133_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨7, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 7 (by decide)))

theorem fz2_133_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨8, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 8 (by decide)))

theorem fz2_133_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨9, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 9 (by decide)))

theorem fz2_133_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨11, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 11 (by decide)))

theorem fz2_133_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨13, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 13 (by decide)))

theorem fz2_133_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨14, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 14 (by decide)))

theorem fz2_133_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨15, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 15 (by decide)))

theorem fz2_133_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨16, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 16 (by decide)))

theorem fz2_133_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨17, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 17 (by decide)))

theorem fz2_133_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨18, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 18 (by decide)))

theorem fz2_133_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨19, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 19 (by decide)))

theorem fz2_133_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨20, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 20 (by decide)))

theorem fz2_133_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨21, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 21 (by decide)))

theorem fz2_133_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨23, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 23 (by decide)))

theorem fz2_133_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨24, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 24 (by decide)))

theorem fz2_133_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨25, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 25 (by decide)))

theorem fz2_133_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨26, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 26 (by decide)))

theorem fz2_133_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨27, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 27 (by decide)))

theorem fz2_133_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨28, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 28 (by decide)))

theorem fz2_133_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨29, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 29 (by decide)))

theorem fz2_133_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨30, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 30 (by decide)))

theorem fz2_133_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨31, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 31 (by decide)))

theorem fz2_133_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨33, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 33 (by decide)))

theorem fz2_133_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨34, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 34 (by decide)))

theorem fz2_133_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨35, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 35 (by decide)))

theorem fz2_133_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨37, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 37 (by decide)))

theorem fz2_133_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨38, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 38 (by decide)))

theorem fz2_133_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨40, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 40 (by decide)))

theorem fz2_133_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨41, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 41 (by decide)))

theorem fz2_133_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨42, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 42 (by decide)))

theorem fz2_133_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨44, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 44 (by decide)))

theorem fz2_133_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨45, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 45 (by decide)))

theorem fz2_133_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨46, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 46 (by decide)))

theorem fz2_133_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨47, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 47 (by decide)))

theorem fz2_133_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨48, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 48 (by decide)))

theorem fz2_133_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨49, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 49 (by decide)))

theorem fz2_133_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨51, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 51 (by decide)))

theorem fz2_133_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨52, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 52 (by decide)))

theorem fz2_133_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨54, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 54 (by decide)))

theorem fz2_133_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨55, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 55 (by decide)))

theorem fz2_133_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨56, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 56 (by decide)))

theorem fz2_133_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨57, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 57 (by decide)))

theorem fz2_133_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨58, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 58 (by decide)))

theorem fz2_133_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨59, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 59 (by decide)))

theorem fz2_133_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨60, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 60 (by decide)))

theorem fz2_133_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨61, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 61 (by decide)))

theorem fz2_133_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨62, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 62 (by decide)))

theorem fz2_133_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨63, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 63 (by decide)))

theorem fz2_133_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨64, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 64 (by decide)))

theorem fz2_133_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨65, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 65 (by decide)))

theorem fz2_133_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨66, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 66 (by decide)))

theorem fz2_133_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨67, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 67 (by decide)))

theorem fz2_133_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨68, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 68 (by decide)))

theorem fz2_133_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨69, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 69 (by decide)))

theorem fz2_133_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨70, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 70 (by decide)))

theorem fz2_133_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨71, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 71 (by decide)))

theorem fz2_133_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨72, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 72 (by decide)))

theorem fz2_133_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨73, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 73 (by decide)))

theorem fz2_133_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨74, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 74 (by decide)))

theorem fz2_133_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨75, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 75 (by decide)))

theorem fz2_133_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨76, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 76 (by decide)))

theorem fz2_133_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨77, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 77 (by decide)))

theorem fz2_133_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨78, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 78 (by decide)))

theorem fz2_133_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨79, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 79 (by decide)))

theorem fz2_133_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨80, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 80 (by decide)))

theorem fz2_133_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨81, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 81 (by decide)))

theorem fz2_133_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨82, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 82 (by decide)))

theorem fz2_133_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨84, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 84 (by decide)))

theorem fz2_133_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨85, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 85 (by decide)))

theorem fz2_133_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨86, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 86 (by decide)))

theorem fz2_133_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨87, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 87 (by decide)))

theorem fz2_133_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨88, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 88 (by decide)))

theorem fz2_133_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨89, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 89 (by decide)))

theorem fz2_133_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨90, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 90 (by decide)))

theorem fz2_133_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨91, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 91 (by decide)))

theorem fz2_133_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨92, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 92 (by decide)))

theorem fz2_133_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨93, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 93 (by decide)))

theorem fz2_133_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨95, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 95 (by decide)))

theorem fz2_133_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨96, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 96 (by decide)))

theorem fz2_133_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨97, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 97 (by decide)))

theorem fz2_133_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨99, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 99 (by decide)))

theorem fz2_133_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨100, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 100 (by decide)))

theorem fz2_133_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨102, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 102 (by decide)))

theorem fz2_133_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨103, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 103 (by decide)))

theorem fz2_133_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨104, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 104 (by decide)))

theorem fz2_133_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨106, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 106 (by decide)))

theorem fz2_133_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨107, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 107 (by decide)))

theorem fz2_133_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨108, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 108 (by decide)))

theorem fz2_133_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨109, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 109 (by decide)))

theorem fz2_133_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨110, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 110 (by decide)))

theorem fz2_133_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨111, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 111 (by decide)))

theorem fz2_133_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨113, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 113 (by decide)))

theorem fz2_133_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨114, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 114 (by decide)))

theorem fz2_133_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨115, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 115 (by decide)))

theorem fz2_133_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨116, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 116 (by decide)))

theorem fz2_133_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨117, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 117 (by decide)))

theorem fz2_133_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨118, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 118 (by decide)))

theorem fz2_133_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨119, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 119 (by decide)))

theorem fz2_133_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨120, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 120 (by decide)))

theorem fz2_133_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨121, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 121 (by decide)))

theorem fz2_133_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨122, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 122 (by decide)))

theorem fz2_133_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨123, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 123 (by decide)))

theorem fz2_133_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨124, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 124 (by decide)))

theorem fz2_133_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨125, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 125 (by decide)))

theorem fz2_133_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨126, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 126 (by decide)))

theorem fz2_133_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨127, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 127 (by decide)))

theorem fz2_133_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨128, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 128 (by decide)))

theorem fz2_133_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨129, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 129 (by decide)))

theorem fz2_133_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨130, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 130 (by decide)))

theorem fz2_133_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨131, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 131 (by decide)))

theorem fz2_133_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨132, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 132 (by decide)))

theorem fz2_133_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨134, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 134 (by decide)))

theorem fz2_133_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨135, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 135 (by decide)))

theorem fz2_133_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨136, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 136 (by decide)))

theorem fz2_133_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨137, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 137 (by decide)))

theorem fz2_133_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨138, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 138 (by decide)))

theorem fz2_133_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨139, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 139 (by decide)))

theorem fz2_133_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨140, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 140 (by decide)))

theorem fz2_133_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨141, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 141 (by decide)))

theorem fz2_133_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨142, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 142 (by decide)))

theorem fz2_133_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨143, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 143 (by decide)))

theorem fz2_133_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨144, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 144 (by decide)))

theorem fz2_133_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨145, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 145 (by decide)))

theorem fz2_133_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK133)) = 0 :=
  Q2.repsFixedCard2 rK133 ⟨146, by decide⟩ Q2.R133_2 Q2.hpxR133_2 Q2.hcardq133_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_133) 146 (by decide)))

theorem fixz1_134 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 41, 42, 43, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 91, 92, 93, 94, 95, 96, 97, 98, 100, 101, 103, 104, 105, 107, 108, 109, 110, 111, 112, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK134) (retConj 1 (R134 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_134_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨1, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 1 (by decide)))

theorem fz1_134_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨2, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 2 (by decide)))

theorem fz1_134_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨3, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 3 (by decide)))

theorem fz1_134_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨5, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 5 (by decide)))

theorem fz1_134_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨6, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 6 (by decide)))

theorem fz1_134_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨7, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 7 (by decide)))

theorem fz1_134_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨8, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 8 (by decide)))

theorem fz1_134_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨9, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 9 (by decide)))

theorem fz1_134_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨11, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 11 (by decide)))

theorem fz1_134_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨13, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 13 (by decide)))

theorem fz1_134_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨14, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 14 (by decide)))

theorem fz1_134_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨15, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 15 (by decide)))

theorem fz1_134_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨16, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 16 (by decide)))

theorem fz1_134_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨17, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 17 (by decide)))

theorem fz1_134_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨18, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 18 (by decide)))

theorem fz1_134_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨19, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 19 (by decide)))

theorem fz1_134_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨20, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 20 (by decide)))

theorem fz1_134_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨21, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 21 (by decide)))

theorem fz1_134_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨23, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 23 (by decide)))

theorem fz1_134_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨24, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 24 (by decide)))

theorem fz1_134_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨25, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 25 (by decide)))

theorem fz1_134_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨26, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 26 (by decide)))

theorem fz1_134_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨27, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 27 (by decide)))

theorem fz1_134_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨29, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 29 (by decide)))

theorem fz1_134_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨30, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 30 (by decide)))

theorem fz1_134_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨31, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 31 (by decide)))

theorem fz1_134_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨32, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 32 (by decide)))

theorem fz1_134_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨33, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 33 (by decide)))

theorem fz1_134_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨34, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 34 (by decide)))

theorem fz1_134_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨35, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 35 (by decide)))

theorem fz1_134_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨36, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 36 (by decide)))

theorem fz1_134_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨38, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 38 (by decide)))

theorem fz1_134_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨39, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 39 (by decide)))

theorem fz1_134_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨41, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 41 (by decide)))

theorem fz1_134_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨42, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 42 (by decide)))

theorem fz1_134_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨43, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 43 (by decide)))

theorem fz1_134_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨45, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 45 (by decide)))

theorem fz1_134_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨46, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 46 (by decide)))

theorem fz1_134_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨47, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 47 (by decide)))

theorem fz1_134_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨48, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 48 (by decide)))

theorem fz1_134_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨49, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 49 (by decide)))

theorem fz1_134_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨50, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 50 (by decide)))

theorem fz1_134_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨52, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 52 (by decide)))

theorem fz1_134_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨54, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 54 (by decide)))

theorem fz1_134_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨55, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 55 (by decide)))

theorem fz1_134_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨56, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 56 (by decide)))

theorem fz1_134_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨57, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 57 (by decide)))

theorem fz1_134_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨58, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 58 (by decide)))

theorem fz1_134_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨59, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 59 (by decide)))

theorem fz1_134_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨60, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 60 (by decide)))

theorem fz1_134_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨61, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 61 (by decide)))

theorem fz1_134_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨62, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 62 (by decide)))

theorem fz1_134_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨63, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 63 (by decide)))

theorem fz1_134_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨64, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 64 (by decide)))

theorem fz1_134_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨65, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 65 (by decide)))

theorem fz1_134_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨66, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 66 (by decide)))

theorem fz1_134_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨67, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 67 (by decide)))

theorem fz1_134_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨68, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 68 (by decide)))

theorem fz1_134_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨69, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 69 (by decide)))

theorem fz1_134_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨70, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 70 (by decide)))

theorem fz1_134_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨71, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 71 (by decide)))

theorem fz1_134_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨72, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 72 (by decide)))

theorem fz1_134_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨73, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 73 (by decide)))

theorem fz1_134_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨74, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 74 (by decide)))

theorem fz1_134_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨75, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 75 (by decide)))

theorem fz1_134_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨76, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 76 (by decide)))

theorem fz1_134_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨77, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 77 (by decide)))

theorem fz1_134_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨78, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 78 (by decide)))

theorem fz1_134_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨79, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 79 (by decide)))

theorem fz1_134_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨80, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 80 (by decide)))

theorem fz1_134_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨81, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 81 (by decide)))

theorem fz1_134_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨82, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 82 (by decide)))

theorem fz1_134_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨84, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 84 (by decide)))

theorem fz1_134_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨85, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 85 (by decide)))

theorem fz1_134_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨86, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 86 (by decide)))

theorem fz1_134_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨87, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 87 (by decide)))

theorem fz1_134_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨88, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 88 (by decide)))

theorem fz1_134_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨89, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 89 (by decide)))

theorem fz1_134_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨91, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 91 (by decide)))

theorem fz1_134_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨92, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 92 (by decide)))

theorem fz1_134_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨93, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 93 (by decide)))

theorem fz1_134_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨94, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 94 (by decide)))

theorem fz1_134_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨95, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 95 (by decide)))

theorem fz1_134_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨96, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 96 (by decide)))

theorem fz1_134_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨97, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 97 (by decide)))

theorem fz1_134_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨98, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 98 (by decide)))

theorem fz1_134_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨100, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 100 (by decide)))

theorem fz1_134_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨101, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 101 (by decide)))

theorem fz1_134_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨103, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 103 (by decide)))

theorem fz1_134_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨104, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 104 (by decide)))

theorem fz1_134_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨105, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 105 (by decide)))

theorem fz1_134_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨107, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 107 (by decide)))

theorem fz1_134_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨108, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 108 (by decide)))

theorem fz1_134_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨109, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 109 (by decide)))

theorem fz1_134_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨110, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 110 (by decide)))

theorem fz1_134_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨111, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 111 (by decide)))

theorem fz1_134_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨112, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 112 (by decide)))

theorem fz1_134_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨114, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 114 (by decide)))

theorem fz1_134_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨115, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 115 (by decide)))

theorem fz1_134_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨116, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 116 (by decide)))

theorem fz1_134_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨117, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 117 (by decide)))

theorem fz1_134_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨118, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 118 (by decide)))

theorem fz1_134_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨119, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 119 (by decide)))

theorem fz1_134_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨120, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 120 (by decide)))

theorem fz1_134_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨121, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 121 (by decide)))

theorem fz1_134_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨122, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 122 (by decide)))

theorem fz1_134_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨123, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 123 (by decide)))

theorem fz1_134_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨124, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 124 (by decide)))

theorem fz1_134_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨125, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 125 (by decide)))

theorem fz1_134_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨126, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 126 (by decide)))

theorem fz1_134_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨127, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 127 (by decide)))

theorem fz1_134_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨128, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 128 (by decide)))

theorem fz1_134_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨129, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 129 (by decide)))

theorem fz1_134_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨130, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 130 (by decide)))

theorem fz1_134_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨131, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 131 (by decide)))

theorem fz1_134_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨132, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 132 (by decide)))

theorem fz1_134_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨133, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 133 (by decide)))

theorem fz1_134_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨135, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 135 (by decide)))

theorem fz1_134_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨136, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 136 (by decide)))

theorem fz1_134_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨137, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 137 (by decide)))

theorem fz1_134_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨138, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 138 (by decide)))

theorem fz1_134_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨139, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 139 (by decide)))

theorem fz1_134_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨140, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 140 (by decide)))

theorem fz1_134_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨141, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 141 (by decide)))

theorem fz1_134_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨142, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 142 (by decide)))

theorem fz1_134_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨143, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 143 (by decide)))

theorem fz1_134_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨144, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 144 (by decide)))

theorem fz1_134_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨145, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 145 (by decide)))

theorem fz1_134_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK134)) = 0 :=
  repsFixedCard rK134 ⟨146, by decide⟩ R134 hpxR134 hcardq134
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_134) 146 (by decide)))

theorem fixz2_134 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 38, 39, 41, 42, 43, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 91, 92, 93, 94, 95, 96, 97, 98, 100, 101, 103, 104, 105, 107, 108, 109, 110, 111, 112, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK134) (retConj 2 (Q2.R134_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_134_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨1, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 1 (by decide)))

theorem fz2_134_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨2, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 2 (by decide)))

theorem fz2_134_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨3, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 3 (by decide)))

theorem fz2_134_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨5, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 5 (by decide)))

theorem fz2_134_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨6, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 6 (by decide)))

theorem fz2_134_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨7, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 7 (by decide)))

theorem fz2_134_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨8, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 8 (by decide)))

theorem fz2_134_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨9, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 9 (by decide)))

theorem fz2_134_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨11, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 11 (by decide)))

theorem fz2_134_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨13, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 13 (by decide)))

theorem fz2_134_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨14, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 14 (by decide)))

theorem fz2_134_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨15, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 15 (by decide)))

theorem fz2_134_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨16, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 16 (by decide)))

theorem fz2_134_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨17, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 17 (by decide)))

theorem fz2_134_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨18, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 18 (by decide)))

theorem fz2_134_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨19, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 19 (by decide)))

theorem fz2_134_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨20, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 20 (by decide)))

theorem fz2_134_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨21, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 21 (by decide)))

theorem fz2_134_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨23, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 23 (by decide)))

theorem fz2_134_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨24, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 24 (by decide)))

theorem fz2_134_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨25, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 25 (by decide)))

theorem fz2_134_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨26, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 26 (by decide)))

theorem fz2_134_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨27, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 27 (by decide)))

theorem fz2_134_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨29, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 29 (by decide)))

theorem fz2_134_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨30, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 30 (by decide)))

theorem fz2_134_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨31, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 31 (by decide)))

theorem fz2_134_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨32, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 32 (by decide)))

theorem fz2_134_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨33, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 33 (by decide)))

theorem fz2_134_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨34, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 34 (by decide)))

theorem fz2_134_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨35, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 35 (by decide)))

theorem fz2_134_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨36, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 36 (by decide)))

theorem fz2_134_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨38, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 38 (by decide)))

theorem fz2_134_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨39, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 39 (by decide)))

theorem fz2_134_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨41, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 41 (by decide)))

theorem fz2_134_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨42, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 42 (by decide)))

theorem fz2_134_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨43, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 43 (by decide)))

theorem fz2_134_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨45, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 45 (by decide)))

theorem fz2_134_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨46, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 46 (by decide)))

theorem fz2_134_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨47, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 47 (by decide)))

theorem fz2_134_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨48, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 48 (by decide)))

theorem fz2_134_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨49, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 49 (by decide)))

theorem fz2_134_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨50, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 50 (by decide)))

theorem fz2_134_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨52, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 52 (by decide)))

theorem fz2_134_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨54, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 54 (by decide)))

theorem fz2_134_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨55, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 55 (by decide)))

theorem fz2_134_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨56, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 56 (by decide)))

theorem fz2_134_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨57, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 57 (by decide)))

theorem fz2_134_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨58, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 58 (by decide)))

theorem fz2_134_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨59, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 59 (by decide)))

theorem fz2_134_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨60, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 60 (by decide)))

theorem fz2_134_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨61, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 61 (by decide)))

theorem fz2_134_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨62, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 62 (by decide)))

theorem fz2_134_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨63, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 63 (by decide)))

theorem fz2_134_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨64, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 64 (by decide)))

theorem fz2_134_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨65, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 65 (by decide)))

theorem fz2_134_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨66, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 66 (by decide)))

theorem fz2_134_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨67, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 67 (by decide)))

theorem fz2_134_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨68, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 68 (by decide)))

theorem fz2_134_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨69, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 69 (by decide)))

theorem fz2_134_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨70, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 70 (by decide)))

theorem fz2_134_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨71, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 71 (by decide)))

theorem fz2_134_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨72, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 72 (by decide)))

theorem fz2_134_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨73, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 73 (by decide)))

theorem fz2_134_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨74, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 74 (by decide)))

theorem fz2_134_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨75, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 75 (by decide)))

theorem fz2_134_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨76, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 76 (by decide)))

theorem fz2_134_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨77, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 77 (by decide)))

theorem fz2_134_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨78, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 78 (by decide)))

theorem fz2_134_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨79, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 79 (by decide)))

theorem fz2_134_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨80, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 80 (by decide)))

theorem fz2_134_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨81, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 81 (by decide)))

theorem fz2_134_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨82, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 82 (by decide)))

theorem fz2_134_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨84, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 84 (by decide)))

theorem fz2_134_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨85, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 85 (by decide)))

theorem fz2_134_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨86, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 86 (by decide)))

theorem fz2_134_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨87, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 87 (by decide)))

theorem fz2_134_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨88, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 88 (by decide)))

theorem fz2_134_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨89, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 89 (by decide)))

theorem fz2_134_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨91, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 91 (by decide)))

theorem fz2_134_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨92, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 92 (by decide)))

theorem fz2_134_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨93, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 93 (by decide)))

theorem fz2_134_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨94, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 94 (by decide)))

theorem fz2_134_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨95, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 95 (by decide)))

theorem fz2_134_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨96, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 96 (by decide)))

theorem fz2_134_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨97, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 97 (by decide)))

theorem fz2_134_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨98, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 98 (by decide)))

theorem fz2_134_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨100, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 100 (by decide)))

theorem fz2_134_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨101, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 101 (by decide)))

theorem fz2_134_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨103, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 103 (by decide)))

theorem fz2_134_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨104, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 104 (by decide)))

theorem fz2_134_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨105, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 105 (by decide)))

theorem fz2_134_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨107, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 107 (by decide)))

theorem fz2_134_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨108, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 108 (by decide)))

theorem fz2_134_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨109, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 109 (by decide)))

theorem fz2_134_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨110, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 110 (by decide)))

theorem fz2_134_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨111, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 111 (by decide)))

theorem fz2_134_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨112, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 112 (by decide)))

theorem fz2_134_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨114, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 114 (by decide)))

theorem fz2_134_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨115, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 115 (by decide)))

theorem fz2_134_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨116, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 116 (by decide)))

theorem fz2_134_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨117, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 117 (by decide)))

theorem fz2_134_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨118, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 118 (by decide)))

theorem fz2_134_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨119, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 119 (by decide)))

theorem fz2_134_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨120, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 120 (by decide)))

theorem fz2_134_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨121, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 121 (by decide)))

theorem fz2_134_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨122, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 122 (by decide)))

theorem fz2_134_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨123, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 123 (by decide)))

theorem fz2_134_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨124, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 124 (by decide)))

theorem fz2_134_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨125, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 125 (by decide)))

theorem fz2_134_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨126, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 126 (by decide)))

theorem fz2_134_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨127, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 127 (by decide)))

theorem fz2_134_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨128, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 128 (by decide)))

theorem fz2_134_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨129, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 129 (by decide)))

theorem fz2_134_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨130, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 130 (by decide)))

theorem fz2_134_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨131, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 131 (by decide)))

theorem fz2_134_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨132, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 132 (by decide)))

theorem fz2_134_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨133, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 133 (by decide)))

theorem fz2_134_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨135, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 135 (by decide)))

theorem fz2_134_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨136, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 136 (by decide)))

theorem fz2_134_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨137, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 137 (by decide)))

theorem fz2_134_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨138, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 138 (by decide)))

theorem fz2_134_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨139, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 139 (by decide)))

theorem fz2_134_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨140, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 140 (by decide)))

theorem fz2_134_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨141, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 141 (by decide)))

theorem fz2_134_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨142, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 142 (by decide)))

theorem fz2_134_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨143, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 143 (by decide)))

theorem fz2_134_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨144, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 144 (by decide)))

theorem fz2_134_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨145, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 145 (by decide)))

theorem fz2_134_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK134)) = 0 :=
  Q2.repsFixedCard2 rK134 ⟨146, by decide⟩ Q2.R134_2 Q2.hpxR134_2 Q2.hcardq134_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_134) 146 (by decide)))

theorem fixz1_135 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 30, 31, 32, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 46, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 96, 97, 98, 99, 100, 101, 102, 104, 105, 106, 108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK135) (retConj 1 (R135 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_135_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨1, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 1 (by decide)))

theorem fz1_135_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨2, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 2 (by decide)))

theorem fz1_135_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨3, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 3 (by decide)))

theorem fz1_135_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨5, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 5 (by decide)))

theorem fz1_135_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨6, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 6 (by decide)))

theorem fz1_135_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨7, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 7 (by decide)))

theorem fz1_135_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨8, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 8 (by decide)))

theorem fz1_135_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨9, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 9 (by decide)))

theorem fz1_135_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨11, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 11 (by decide)))

theorem fz1_135_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨13, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 13 (by decide)))

theorem fz1_135_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨14, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 14 (by decide)))

theorem fz1_135_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨15, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 15 (by decide)))

theorem fz1_135_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨16, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 16 (by decide)))

theorem fz1_135_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨17, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 17 (by decide)))

theorem fz1_135_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨18, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 18 (by decide)))

theorem fz1_135_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨19, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 19 (by decide)))

theorem fz1_135_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨20, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 20 (by decide)))

theorem fz1_135_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨21, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 21 (by decide)))

theorem fz1_135_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨23, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 23 (by decide)))

theorem fz1_135_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨24, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 24 (by decide)))

theorem fz1_135_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨25, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 25 (by decide)))

theorem fz1_135_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨26, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 26 (by decide)))

theorem fz1_135_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨27, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 27 (by decide)))

theorem fz1_135_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨28, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 28 (by decide)))

theorem fz1_135_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨30, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 30 (by decide)))

theorem fz1_135_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨31, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 31 (by decide)))

theorem fz1_135_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨32, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 32 (by decide)))

theorem fz1_135_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨34, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 34 (by decide)))

theorem fz1_135_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨35, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 35 (by decide)))

theorem fz1_135_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨36, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 36 (by decide)))

theorem fz1_135_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨37, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 37 (by decide)))

theorem fz1_135_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨38, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 38 (by decide)))

theorem fz1_135_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨39, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 39 (by decide)))

theorem fz1_135_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨40, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 40 (by decide)))

theorem fz1_135_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨42, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 42 (by decide)))

theorem fz1_135_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨43, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 43 (by decide)))

theorem fz1_135_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨44, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 44 (by decide)))

theorem fz1_135_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨46, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 46 (by decide)))

theorem fz1_135_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨47, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 47 (by decide)))

theorem fz1_135_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨48, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 48 (by decide)))

theorem fz1_135_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨49, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 49 (by decide)))

theorem fz1_135_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨50, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 50 (by decide)))

theorem fz1_135_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨51, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 51 (by decide)))

theorem fz1_135_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨54, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 54 (by decide)))

theorem fz1_135_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨55, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 55 (by decide)))

theorem fz1_135_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨56, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 56 (by decide)))

theorem fz1_135_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨57, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 57 (by decide)))

theorem fz1_135_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨58, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 58 (by decide)))

theorem fz1_135_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨59, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 59 (by decide)))

theorem fz1_135_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨60, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 60 (by decide)))

theorem fz1_135_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨61, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 61 (by decide)))

theorem fz1_135_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨62, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 62 (by decide)))

theorem fz1_135_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨63, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 63 (by decide)))

theorem fz1_135_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨64, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 64 (by decide)))

theorem fz1_135_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨65, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 65 (by decide)))

theorem fz1_135_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨66, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 66 (by decide)))

theorem fz1_135_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨67, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 67 (by decide)))

theorem fz1_135_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨68, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 68 (by decide)))

theorem fz1_135_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨69, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 69 (by decide)))

theorem fz1_135_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨70, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 70 (by decide)))

theorem fz1_135_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨71, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 71 (by decide)))

theorem fz1_135_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨72, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 72 (by decide)))

theorem fz1_135_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨73, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 73 (by decide)))

theorem fz1_135_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨74, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 74 (by decide)))

theorem fz1_135_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨75, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 75 (by decide)))

theorem fz1_135_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨76, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 76 (by decide)))

theorem fz1_135_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨77, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 77 (by decide)))

theorem fz1_135_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨78, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 78 (by decide)))

theorem fz1_135_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨79, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 79 (by decide)))

theorem fz1_135_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨80, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 80 (by decide)))

theorem fz1_135_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨81, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 81 (by decide)))

theorem fz1_135_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨82, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 82 (by decide)))

theorem fz1_135_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨84, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 84 (by decide)))

theorem fz1_135_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨85, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 85 (by decide)))

theorem fz1_135_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨86, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 86 (by decide)))

theorem fz1_135_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨87, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 87 (by decide)))

theorem fz1_135_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨88, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 88 (by decide)))

theorem fz1_135_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨89, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 89 (by decide)))

theorem fz1_135_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨90, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 90 (by decide)))

theorem fz1_135_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨92, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 92 (by decide)))

theorem fz1_135_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨93, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 93 (by decide)))

theorem fz1_135_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨94, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 94 (by decide)))

theorem fz1_135_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨96, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 96 (by decide)))

theorem fz1_135_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨97, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 97 (by decide)))

theorem fz1_135_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨98, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 98 (by decide)))

theorem fz1_135_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨99, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 99 (by decide)))

theorem fz1_135_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨100, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 100 (by decide)))

theorem fz1_135_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨101, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 101 (by decide)))

theorem fz1_135_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨102, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 102 (by decide)))

theorem fz1_135_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨104, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 104 (by decide)))

theorem fz1_135_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨105, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 105 (by decide)))

theorem fz1_135_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨106, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 106 (by decide)))

theorem fz1_135_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨108, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 108 (by decide)))

theorem fz1_135_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨109, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 109 (by decide)))

theorem fz1_135_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨110, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 110 (by decide)))

theorem fz1_135_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨111, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 111 (by decide)))

theorem fz1_135_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨112, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 112 (by decide)))

theorem fz1_135_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨113, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 113 (by decide)))

theorem fz1_135_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨115, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 115 (by decide)))

theorem fz1_135_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨116, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 116 (by decide)))

theorem fz1_135_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨117, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 117 (by decide)))

theorem fz1_135_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨118, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 118 (by decide)))

theorem fz1_135_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨119, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 119 (by decide)))

theorem fz1_135_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨120, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 120 (by decide)))

theorem fz1_135_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨121, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 121 (by decide)))

theorem fz1_135_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨122, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 122 (by decide)))

theorem fz1_135_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨123, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 123 (by decide)))

theorem fz1_135_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨124, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 124 (by decide)))

theorem fz1_135_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨125, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 125 (by decide)))

theorem fz1_135_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨126, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 126 (by decide)))

theorem fz1_135_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨127, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 127 (by decide)))

theorem fz1_135_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨128, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 128 (by decide)))

theorem fz1_135_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨129, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 129 (by decide)))

theorem fz1_135_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨130, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 130 (by decide)))

theorem fz1_135_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨131, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 131 (by decide)))

theorem fz1_135_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨132, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 132 (by decide)))

theorem fz1_135_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨133, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 133 (by decide)))

theorem fz1_135_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨134, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 134 (by decide)))

theorem fz1_135_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨136, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 136 (by decide)))

theorem fz1_135_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨137, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 137 (by decide)))

theorem fz1_135_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨138, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 138 (by decide)))

theorem fz1_135_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨139, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 139 (by decide)))

theorem fz1_135_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨140, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 140 (by decide)))

theorem fz1_135_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨141, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 141 (by decide)))

theorem fz1_135_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨142, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 142 (by decide)))

theorem fz1_135_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨143, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 143 (by decide)))

theorem fz1_135_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨144, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 144 (by decide)))

theorem fz1_135_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨145, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 145 (by decide)))

theorem fz1_135_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK135)) = 0 :=
  repsFixedCard rK135 ⟨146, by decide⟩ R135 hpxR135 hcardq135
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_135) 146 (by decide)))

theorem fixz2_135 : ([1, 2, 3, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 25, 26, 27, 28, 30, 31, 32, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 46, 47, 48, 49, 50, 51, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 85, 86, 87, 88, 89, 90, 92, 93, 94, 96, 97, 98, 99, 100, 101, 102, 104, 105, 106, 108, 109, 110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK135) (retConj 2 (Q2.R135_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_135_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨1, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 1 (by decide)))

theorem fz2_135_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨2, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 2 (by decide)))

theorem fz2_135_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨3, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 3 (by decide)))

theorem fz2_135_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨5, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 5 (by decide)))

theorem fz2_135_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨6, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 6 (by decide)))

theorem fz2_135_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨7, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 7 (by decide)))

theorem fz2_135_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨8, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 8 (by decide)))

theorem fz2_135_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨9, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 9 (by decide)))

theorem fz2_135_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨11, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 11 (by decide)))

theorem fz2_135_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨13, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 13 (by decide)))

theorem fz2_135_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨14, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 14 (by decide)))

theorem fz2_135_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨15, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 15 (by decide)))

theorem fz2_135_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨16, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 16 (by decide)))

theorem fz2_135_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨17, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 17 (by decide)))

theorem fz2_135_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨18, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 18 (by decide)))

theorem fz2_135_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨19, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 19 (by decide)))

theorem fz2_135_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨20, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 20 (by decide)))

theorem fz2_135_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨21, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 21 (by decide)))

theorem fz2_135_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨23, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 23 (by decide)))

theorem fz2_135_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨24, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 24 (by decide)))

theorem fz2_135_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨25, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 25 (by decide)))

theorem fz2_135_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨26, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 26 (by decide)))

theorem fz2_135_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨27, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 27 (by decide)))

theorem fz2_135_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨28, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 28 (by decide)))

theorem fz2_135_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨30, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 30 (by decide)))

theorem fz2_135_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨31, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 31 (by decide)))

theorem fz2_135_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨32, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 32 (by decide)))

theorem fz2_135_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨34, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 34 (by decide)))

theorem fz2_135_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨35, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 35 (by decide)))

theorem fz2_135_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨36, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 36 (by decide)))

theorem fz2_135_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨37, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 37 (by decide)))

theorem fz2_135_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨38, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 38 (by decide)))

theorem fz2_135_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨39, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 39 (by decide)))

theorem fz2_135_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨40, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 40 (by decide)))

theorem fz2_135_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨42, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 42 (by decide)))

theorem fz2_135_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨43, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 43 (by decide)))

theorem fz2_135_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨44, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 44 (by decide)))

theorem fz2_135_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨46, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 46 (by decide)))

theorem fz2_135_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨47, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 47 (by decide)))

theorem fz2_135_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨48, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 48 (by decide)))

theorem fz2_135_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨49, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 49 (by decide)))

theorem fz2_135_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨50, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 50 (by decide)))

theorem fz2_135_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨51, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 51 (by decide)))

theorem fz2_135_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨54, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 54 (by decide)))

theorem fz2_135_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨55, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 55 (by decide)))

theorem fz2_135_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨56, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 56 (by decide)))

theorem fz2_135_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨57, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 57 (by decide)))

theorem fz2_135_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨58, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 58 (by decide)))

theorem fz2_135_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨59, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 59 (by decide)))

theorem fz2_135_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨60, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 60 (by decide)))

theorem fz2_135_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨61, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 61 (by decide)))

theorem fz2_135_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨62, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 62 (by decide)))

theorem fz2_135_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨63, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 63 (by decide)))

theorem fz2_135_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨64, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 64 (by decide)))

theorem fz2_135_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨65, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 65 (by decide)))

theorem fz2_135_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨66, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 66 (by decide)))

theorem fz2_135_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨67, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 67 (by decide)))

theorem fz2_135_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨68, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 68 (by decide)))

theorem fz2_135_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨69, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 69 (by decide)))

theorem fz2_135_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨70, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 70 (by decide)))

theorem fz2_135_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨71, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 71 (by decide)))

theorem fz2_135_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨72, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 72 (by decide)))

theorem fz2_135_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨73, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 73 (by decide)))

theorem fz2_135_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨74, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 74 (by decide)))

theorem fz2_135_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨75, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 75 (by decide)))

theorem fz2_135_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨76, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 76 (by decide)))

theorem fz2_135_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨77, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 77 (by decide)))

theorem fz2_135_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨78, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 78 (by decide)))

theorem fz2_135_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨79, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 79 (by decide)))

theorem fz2_135_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨80, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 80 (by decide)))

theorem fz2_135_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨81, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 81 (by decide)))

theorem fz2_135_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨82, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 82 (by decide)))

theorem fz2_135_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨84, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 84 (by decide)))

theorem fz2_135_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨85, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 85 (by decide)))

theorem fz2_135_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨86, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 86 (by decide)))

theorem fz2_135_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨87, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 87 (by decide)))

theorem fz2_135_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨88, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 88 (by decide)))

theorem fz2_135_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨89, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 89 (by decide)))

theorem fz2_135_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨90, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 90 (by decide)))

theorem fz2_135_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨92, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 92 (by decide)))

theorem fz2_135_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨93, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 93 (by decide)))

theorem fz2_135_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨94, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 94 (by decide)))

theorem fz2_135_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨96, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 96 (by decide)))

theorem fz2_135_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨97, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 97 (by decide)))

theorem fz2_135_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨98, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 98 (by decide)))

theorem fz2_135_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨99, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 99 (by decide)))

theorem fz2_135_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨100, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 100 (by decide)))

theorem fz2_135_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨101, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 101 (by decide)))

theorem fz2_135_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨102, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 102 (by decide)))

theorem fz2_135_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨104, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 104 (by decide)))

theorem fz2_135_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨105, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 105 (by decide)))

theorem fz2_135_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨106, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 106 (by decide)))

theorem fz2_135_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨108, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 108 (by decide)))

theorem fz2_135_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨109, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 109 (by decide)))

theorem fz2_135_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨110, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 110 (by decide)))

theorem fz2_135_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨111, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 111 (by decide)))

theorem fz2_135_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨112, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 112 (by decide)))

theorem fz2_135_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨113, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 113 (by decide)))

theorem fz2_135_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨115, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 115 (by decide)))

theorem fz2_135_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨116, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 116 (by decide)))

theorem fz2_135_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨117, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 117 (by decide)))

theorem fz2_135_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨118, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 118 (by decide)))

theorem fz2_135_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨119, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 119 (by decide)))

theorem fz2_135_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨120, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 120 (by decide)))

theorem fz2_135_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨121, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 121 (by decide)))

theorem fz2_135_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨122, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 122 (by decide)))

theorem fz2_135_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨123, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 123 (by decide)))

theorem fz2_135_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨124, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 124 (by decide)))

theorem fz2_135_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨125, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 125 (by decide)))

theorem fz2_135_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨126, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 126 (by decide)))

theorem fz2_135_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨127, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 127 (by decide)))

theorem fz2_135_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨128, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 128 (by decide)))

theorem fz2_135_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨129, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 129 (by decide)))

theorem fz2_135_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨130, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 130 (by decide)))

theorem fz2_135_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨131, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 131 (by decide)))

theorem fz2_135_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨132, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 132 (by decide)))

theorem fz2_135_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨133, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 133 (by decide)))

theorem fz2_135_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨134, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 134 (by decide)))

theorem fz2_135_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨136, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 136 (by decide)))

theorem fz2_135_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨137, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 137 (by decide)))

theorem fz2_135_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨138, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 138 (by decide)))

theorem fz2_135_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨139, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 139 (by decide)))

theorem fz2_135_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨140, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 140 (by decide)))

theorem fz2_135_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨141, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 141 (by decide)))

theorem fz2_135_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨142, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 142 (by decide)))

theorem fz2_135_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨143, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 143 (by decide)))

theorem fz2_135_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨144, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 144 (by decide)))

theorem fz2_135_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨145, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 145 (by decide)))

theorem fz2_135_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK135)) = 0 :=
  Q2.repsFixedCard2 rK135 ⟨146, by decide⟩ Q2.R135_2 Q2.hpxR135_2 Q2.hcardq135_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_135) 146 (by decide)))

theorem fixz1_136 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 42, 43, 44, 45, 46, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 97, 99, 100, 101, 103, 104, 105, 106, 107, 108, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK136) (retConj 1 (R136 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_136_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨1, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 1 (by decide)))

theorem fz1_136_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨2, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 2 (by decide)))

theorem fz1_136_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨3, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 3 (by decide)))

theorem fz1_136_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨4, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 4 (by decide)))

theorem fz1_136_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨6, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 6 (by decide)))

theorem fz1_136_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨7, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 7 (by decide)))

theorem fz1_136_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨8, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 8 (by decide)))

theorem fz1_136_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨9, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 9 (by decide)))

theorem fz1_136_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨11, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 11 (by decide)))

theorem fz1_136_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨13, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 13 (by decide)))

theorem fz1_136_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨14, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 14 (by decide)))

theorem fz1_136_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨15, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 15 (by decide)))

theorem fz1_136_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨16, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 16 (by decide)))

theorem fz1_136_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨17, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 17 (by decide)))

theorem fz1_136_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨18, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 18 (by decide)))

theorem fz1_136_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨19, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 19 (by decide)))

theorem fz1_136_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨20, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 20 (by decide)))

theorem fz1_136_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨21, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 21 (by decide)))

theorem fz1_136_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨22, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 22 (by decide)))

theorem fz1_136_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨24, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 24 (by decide)))

theorem fz1_136_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨25, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 25 (by decide)))

theorem fz1_136_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨26, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 26 (by decide)))

theorem fz1_136_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨27, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 27 (by decide)))

theorem fz1_136_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨28, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 28 (by decide)))

theorem fz1_136_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨30, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 30 (by decide)))

theorem fz1_136_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨31, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 31 (by decide)))

theorem fz1_136_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨32, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 32 (by decide)))

theorem fz1_136_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨33, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 33 (by decide)))

theorem fz1_136_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨34, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 34 (by decide)))

theorem fz1_136_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨35, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 35 (by decide)))

theorem fz1_136_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨37, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 37 (by decide)))

theorem fz1_136_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨38, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 38 (by decide)))

theorem fz1_136_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨39, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 39 (by decide)))

theorem fz1_136_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨41, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 41 (by decide)))

theorem fz1_136_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨42, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 42 (by decide)))

theorem fz1_136_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨43, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 43 (by decide)))

theorem fz1_136_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨44, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 44 (by decide)))

theorem fz1_136_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨45, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 45 (by decide)))

theorem fz1_136_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨46, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 46 (by decide)))

theorem fz1_136_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨49, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 49 (by decide)))

theorem fz1_136_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨50, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 50 (by decide)))

theorem fz1_136_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨51, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 51 (by decide)))

theorem fz1_136_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨52, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 52 (by decide)))

theorem fz1_136_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨54, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 54 (by decide)))

theorem fz1_136_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨55, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 55 (by decide)))

theorem fz1_136_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨56, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 56 (by decide)))

theorem fz1_136_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨57, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 57 (by decide)))

theorem fz1_136_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨58, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 58 (by decide)))

theorem fz1_136_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨59, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 59 (by decide)))

theorem fz1_136_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨60, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 60 (by decide)))

theorem fz1_136_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨61, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 61 (by decide)))

theorem fz1_136_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨62, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 62 (by decide)))

theorem fz1_136_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨63, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 63 (by decide)))

theorem fz1_136_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨64, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 64 (by decide)))

theorem fz1_136_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨65, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 65 (by decide)))

theorem fz1_136_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨66, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 66 (by decide)))

theorem fz1_136_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨67, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 67 (by decide)))

theorem fz1_136_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨68, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 68 (by decide)))

theorem fz1_136_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨69, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 69 (by decide)))

theorem fz1_136_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨70, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 70 (by decide)))

theorem fz1_136_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨71, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 71 (by decide)))

theorem fz1_136_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨72, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 72 (by decide)))

theorem fz1_136_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨73, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 73 (by decide)))

theorem fz1_136_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨74, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 74 (by decide)))

theorem fz1_136_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨75, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 75 (by decide)))

theorem fz1_136_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨76, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 76 (by decide)))

theorem fz1_136_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨77, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 77 (by decide)))

theorem fz1_136_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨78, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 78 (by decide)))

theorem fz1_136_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨79, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 79 (by decide)))

theorem fz1_136_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨80, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 80 (by decide)))

theorem fz1_136_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨81, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 81 (by decide)))

theorem fz1_136_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨82, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 82 (by decide)))

theorem fz1_136_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨83, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 83 (by decide)))

theorem fz1_136_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨85, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 85 (by decide)))

theorem fz1_136_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨86, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 86 (by decide)))

theorem fz1_136_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨87, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 87 (by decide)))

theorem fz1_136_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨88, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 88 (by decide)))

theorem fz1_136_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨89, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 89 (by decide)))

theorem fz1_136_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨90, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 90 (by decide)))

theorem fz1_136_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨92, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 92 (by decide)))

theorem fz1_136_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨93, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 93 (by decide)))

theorem fz1_136_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨94, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 94 (by decide)))

theorem fz1_136_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨95, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 95 (by decide)))

theorem fz1_136_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨96, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 96 (by decide)))

theorem fz1_136_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨97, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 97 (by decide)))

theorem fz1_136_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨99, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 99 (by decide)))

theorem fz1_136_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨100, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 100 (by decide)))

theorem fz1_136_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨101, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 101 (by decide)))

theorem fz1_136_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨103, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 103 (by decide)))

theorem fz1_136_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨104, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 104 (by decide)))

theorem fz1_136_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨105, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 105 (by decide)))

theorem fz1_136_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨106, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 106 (by decide)))

theorem fz1_136_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨107, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 107 (by decide)))

theorem fz1_136_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨108, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 108 (by decide)))

theorem fz1_136_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨111, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 111 (by decide)))

theorem fz1_136_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨112, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 112 (by decide)))

theorem fz1_136_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨113, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 113 (by decide)))

theorem fz1_136_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨114, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 114 (by decide)))

theorem fz1_136_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨115, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 115 (by decide)))

theorem fz1_136_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨116, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 116 (by decide)))

theorem fz1_136_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨117, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 117 (by decide)))

theorem fz1_136_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨118, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 118 (by decide)))

theorem fz1_136_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨119, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 119 (by decide)))

theorem fz1_136_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨120, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 120 (by decide)))

theorem fz1_136_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨121, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 121 (by decide)))

theorem fz1_136_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨122, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 122 (by decide)))

theorem fz1_136_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨123, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 123 (by decide)))

theorem fz1_136_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨124, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 124 (by decide)))

theorem fz1_136_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨125, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 125 (by decide)))

theorem fz1_136_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨126, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 126 (by decide)))

theorem fz1_136_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨127, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 127 (by decide)))

theorem fz1_136_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨128, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 128 (by decide)))

theorem fz1_136_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨129, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 129 (by decide)))

theorem fz1_136_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨130, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 130 (by decide)))

theorem fz1_136_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨131, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 131 (by decide)))

theorem fz1_136_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨132, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 132 (by decide)))

theorem fz1_136_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨133, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 133 (by decide)))

theorem fz1_136_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨134, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 134 (by decide)))

theorem fz1_136_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨135, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 135 (by decide)))

theorem fz1_136_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨137, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 137 (by decide)))

theorem fz1_136_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨138, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 138 (by decide)))

theorem fz1_136_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨139, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 139 (by decide)))

theorem fz1_136_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨140, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 140 (by decide)))

theorem fz1_136_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨141, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 141 (by decide)))

theorem fz1_136_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨142, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 142 (by decide)))

theorem fz1_136_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨143, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 143 (by decide)))

theorem fz1_136_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨144, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 144 (by decide)))

theorem fz1_136_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨145, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 145 (by decide)))

theorem fz1_136_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK136)) = 0 :=
  repsFixedCard rK136 ⟨146, by decide⟩ R136 hpxR136 hcardq136
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_136) 146 (by decide)))

theorem fixz2_136 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 37, 38, 39, 41, 42, 43, 44, 45, 46, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 92, 93, 94, 95, 96, 97, 99, 100, 101, 103, 104, 105, 106, 107, 108, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK136) (retConj 2 (Q2.R136_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_136_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨1, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 1 (by decide)))

theorem fz2_136_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨2, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 2 (by decide)))

theorem fz2_136_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨3, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 3 (by decide)))

theorem fz2_136_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨4, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 4 (by decide)))

theorem fz2_136_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨6, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 6 (by decide)))

theorem fz2_136_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨7, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 7 (by decide)))

theorem fz2_136_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨8, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 8 (by decide)))

theorem fz2_136_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨9, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 9 (by decide)))

theorem fz2_136_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨11, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 11 (by decide)))

theorem fz2_136_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨13, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 13 (by decide)))

theorem fz2_136_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨14, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 14 (by decide)))

theorem fz2_136_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨15, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 15 (by decide)))

theorem fz2_136_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨16, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 16 (by decide)))

theorem fz2_136_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨17, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 17 (by decide)))

theorem fz2_136_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨18, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 18 (by decide)))

theorem fz2_136_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨19, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 19 (by decide)))

theorem fz2_136_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨20, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 20 (by decide)))

theorem fz2_136_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨21, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 21 (by decide)))

theorem fz2_136_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨22, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 22 (by decide)))

theorem fz2_136_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨24, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 24 (by decide)))

theorem fz2_136_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨25, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 25 (by decide)))

theorem fz2_136_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨26, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 26 (by decide)))

theorem fz2_136_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨27, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 27 (by decide)))

theorem fz2_136_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨28, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 28 (by decide)))

theorem fz2_136_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨30, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 30 (by decide)))

theorem fz2_136_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨31, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 31 (by decide)))

theorem fz2_136_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨32, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 32 (by decide)))

theorem fz2_136_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨33, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 33 (by decide)))

theorem fz2_136_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨34, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 34 (by decide)))

theorem fz2_136_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨35, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 35 (by decide)))

theorem fz2_136_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨37, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 37 (by decide)))

theorem fz2_136_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨38, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 38 (by decide)))

theorem fz2_136_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨39, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 39 (by decide)))

theorem fz2_136_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨41, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 41 (by decide)))

theorem fz2_136_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨42, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 42 (by decide)))

theorem fz2_136_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨43, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 43 (by decide)))

theorem fz2_136_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨44, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 44 (by decide)))

theorem fz2_136_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨45, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 45 (by decide)))

theorem fz2_136_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨46, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 46 (by decide)))

theorem fz2_136_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨49, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 49 (by decide)))

theorem fz2_136_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨50, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 50 (by decide)))

theorem fz2_136_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨51, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 51 (by decide)))

theorem fz2_136_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨52, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 52 (by decide)))

theorem fz2_136_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨54, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 54 (by decide)))

theorem fz2_136_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨55, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 55 (by decide)))

theorem fz2_136_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨56, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 56 (by decide)))

theorem fz2_136_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨57, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 57 (by decide)))

theorem fz2_136_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨58, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 58 (by decide)))

theorem fz2_136_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨59, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 59 (by decide)))

theorem fz2_136_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨60, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 60 (by decide)))

theorem fz2_136_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨61, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 61 (by decide)))

theorem fz2_136_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨62, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 62 (by decide)))

theorem fz2_136_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨63, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 63 (by decide)))

theorem fz2_136_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨64, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 64 (by decide)))

theorem fz2_136_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨65, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 65 (by decide)))

theorem fz2_136_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨66, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 66 (by decide)))

theorem fz2_136_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨67, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 67 (by decide)))

theorem fz2_136_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨68, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 68 (by decide)))

theorem fz2_136_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨69, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 69 (by decide)))

theorem fz2_136_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨70, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 70 (by decide)))

theorem fz2_136_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨71, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 71 (by decide)))

theorem fz2_136_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨72, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 72 (by decide)))

theorem fz2_136_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨73, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 73 (by decide)))

theorem fz2_136_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨74, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 74 (by decide)))

theorem fz2_136_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨75, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 75 (by decide)))

theorem fz2_136_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨76, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 76 (by decide)))

theorem fz2_136_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨77, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 77 (by decide)))

theorem fz2_136_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨78, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 78 (by decide)))

theorem fz2_136_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨79, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 79 (by decide)))

theorem fz2_136_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨80, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 80 (by decide)))

theorem fz2_136_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨81, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 81 (by decide)))

theorem fz2_136_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨82, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 82 (by decide)))

theorem fz2_136_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨83, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 83 (by decide)))

theorem fz2_136_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨85, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 85 (by decide)))

theorem fz2_136_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨86, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 86 (by decide)))

theorem fz2_136_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨87, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 87 (by decide)))

theorem fz2_136_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨88, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 88 (by decide)))

theorem fz2_136_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨89, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 89 (by decide)))

theorem fz2_136_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨90, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 90 (by decide)))

theorem fz2_136_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨92, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 92 (by decide)))

theorem fz2_136_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨93, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 93 (by decide)))

theorem fz2_136_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨94, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 94 (by decide)))

theorem fz2_136_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨95, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 95 (by decide)))

theorem fz2_136_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨96, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 96 (by decide)))

theorem fz2_136_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨97, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 97 (by decide)))

theorem fz2_136_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨99, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 99 (by decide)))

theorem fz2_136_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨100, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 100 (by decide)))

theorem fz2_136_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨101, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 101 (by decide)))

theorem fz2_136_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨103, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 103 (by decide)))

theorem fz2_136_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨104, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 104 (by decide)))

theorem fz2_136_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨105, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 105 (by decide)))

theorem fz2_136_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨106, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 106 (by decide)))

theorem fz2_136_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨107, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 107 (by decide)))

theorem fz2_136_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨108, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 108 (by decide)))

theorem fz2_136_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨111, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 111 (by decide)))

theorem fz2_136_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨112, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 112 (by decide)))

theorem fz2_136_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨113, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 113 (by decide)))

theorem fz2_136_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨114, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 114 (by decide)))

theorem fz2_136_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨115, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 115 (by decide)))

theorem fz2_136_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨116, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 116 (by decide)))

theorem fz2_136_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨117, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 117 (by decide)))

theorem fz2_136_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨118, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 118 (by decide)))

theorem fz2_136_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨119, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 119 (by decide)))

theorem fz2_136_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨120, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 120 (by decide)))

theorem fz2_136_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨121, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 121 (by decide)))

theorem fz2_136_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨122, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 122 (by decide)))

theorem fz2_136_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨123, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 123 (by decide)))

theorem fz2_136_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨124, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 124 (by decide)))

theorem fz2_136_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨125, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 125 (by decide)))

theorem fz2_136_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨126, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 126 (by decide)))

theorem fz2_136_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨127, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 127 (by decide)))

theorem fz2_136_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨128, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 128 (by decide)))

theorem fz2_136_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨129, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 129 (by decide)))

theorem fz2_136_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨130, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 130 (by decide)))

theorem fz2_136_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨131, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 131 (by decide)))

theorem fz2_136_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨132, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 132 (by decide)))

theorem fz2_136_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨133, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 133 (by decide)))

theorem fz2_136_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨134, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 134 (by decide)))

theorem fz2_136_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨135, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 135 (by decide)))

theorem fz2_136_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨137, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 137 (by decide)))

theorem fz2_136_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨138, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 138 (by decide)))

theorem fz2_136_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨139, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 139 (by decide)))

theorem fz2_136_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨140, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 140 (by decide)))

theorem fz2_136_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨141, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 141 (by decide)))

theorem fz2_136_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨142, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 142 (by decide)))

theorem fz2_136_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨143, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 143 (by decide)))

theorem fz2_136_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨144, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 144 (by decide)))

theorem fz2_136_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨145, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 145 (by decide)))

theorem fz2_136_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK136)) = 0 :=
  Q2.repsFixedCard2 rK136 ⟨146, by decide⟩ Q2.R136_2 Q2.hpxR136_2 Q2.hcardq136_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_136) 146 (by decide)))

theorem fixz1_137 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 47, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 93, 94, 95, 96, 97, 98, 100, 101, 102, 104, 106, 107, 108, 109, 110, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK137) (retConj 1 (R137 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_137_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨1, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 1 (by decide)))

theorem fz1_137_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨2, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 2 (by decide)))

theorem fz1_137_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨3, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 3 (by decide)))

theorem fz1_137_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨4, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 4 (by decide)))

theorem fz1_137_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨6, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 6 (by decide)))

theorem fz1_137_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨7, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 7 (by decide)))

theorem fz1_137_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨8, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 8 (by decide)))

theorem fz1_137_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨9, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 9 (by decide)))

theorem fz1_137_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨11, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 11 (by decide)))

theorem fz1_137_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨13, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 13 (by decide)))

theorem fz1_137_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨14, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 14 (by decide)))

theorem fz1_137_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨15, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 15 (by decide)))

theorem fz1_137_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨16, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 16 (by decide)))

theorem fz1_137_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨17, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 17 (by decide)))

theorem fz1_137_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨18, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 18 (by decide)))

theorem fz1_137_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨19, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 19 (by decide)))

theorem fz1_137_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨20, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 20 (by decide)))

theorem fz1_137_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨21, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 21 (by decide)))

theorem fz1_137_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨22, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 22 (by decide)))

theorem fz1_137_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨24, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 24 (by decide)))

theorem fz1_137_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨25, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 25 (by decide)))

theorem fz1_137_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨26, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 26 (by decide)))

theorem fz1_137_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨27, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 27 (by decide)))

theorem fz1_137_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨28, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 28 (by decide)))

theorem fz1_137_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨29, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 29 (by decide)))

theorem fz1_137_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨31, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 31 (by decide)))

theorem fz1_137_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨32, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 32 (by decide)))

theorem fz1_137_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨33, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 33 (by decide)))

theorem fz1_137_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨34, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 34 (by decide)))

theorem fz1_137_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨35, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 35 (by decide)))

theorem fz1_137_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨36, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 36 (by decide)))

theorem fz1_137_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨38, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 38 (by decide)))

theorem fz1_137_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨39, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 39 (by decide)))

theorem fz1_137_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨40, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 40 (by decide)))

theorem fz1_137_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨42, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 42 (by decide)))

theorem fz1_137_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨44, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 44 (by decide)))

theorem fz1_137_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨45, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 45 (by decide)))

theorem fz1_137_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨46, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 46 (by decide)))

theorem fz1_137_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨47, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 47 (by decide)))

theorem fz1_137_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨48, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 48 (by decide)))

theorem fz1_137_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨50, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 50 (by decide)))

theorem fz1_137_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨51, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 51 (by decide)))

theorem fz1_137_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨52, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 52 (by decide)))

theorem fz1_137_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨54, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 54 (by decide)))

theorem fz1_137_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨55, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 55 (by decide)))

theorem fz1_137_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨56, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 56 (by decide)))

theorem fz1_137_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨57, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 57 (by decide)))

theorem fz1_137_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨58, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 58 (by decide)))

theorem fz1_137_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨59, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 59 (by decide)))

theorem fz1_137_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨60, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 60 (by decide)))

theorem fz1_137_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨61, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 61 (by decide)))

theorem fz1_137_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨62, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 62 (by decide)))

theorem fz1_137_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨63, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 63 (by decide)))

theorem fz1_137_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨64, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 64 (by decide)))

theorem fz1_137_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨65, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 65 (by decide)))

theorem fz1_137_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨66, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 66 (by decide)))

theorem fz1_137_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨67, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 67 (by decide)))

theorem fz1_137_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨68, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 68 (by decide)))

theorem fz1_137_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨69, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 69 (by decide)))

theorem fz1_137_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨70, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 70 (by decide)))

theorem fz1_137_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨71, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 71 (by decide)))

theorem fz1_137_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨72, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 72 (by decide)))

theorem fz1_137_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨73, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 73 (by decide)))

theorem fz1_137_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨74, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 74 (by decide)))

theorem fz1_137_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨75, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 75 (by decide)))

theorem fz1_137_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨76, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 76 (by decide)))

theorem fz1_137_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨77, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 77 (by decide)))

theorem fz1_137_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨78, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 78 (by decide)))

theorem fz1_137_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨79, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 79 (by decide)))

theorem fz1_137_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨80, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 80 (by decide)))

theorem fz1_137_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨81, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 81 (by decide)))

theorem fz1_137_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨82, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 82 (by decide)))

theorem fz1_137_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨83, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 83 (by decide)))

theorem fz1_137_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨85, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 85 (by decide)))

theorem fz1_137_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨86, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 86 (by decide)))

theorem fz1_137_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨87, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 87 (by decide)))

theorem fz1_137_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨88, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 88 (by decide)))

theorem fz1_137_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨89, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 89 (by decide)))

theorem fz1_137_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨90, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 90 (by decide)))

theorem fz1_137_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨91, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 91 (by decide)))

theorem fz1_137_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨93, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 93 (by decide)))

theorem fz1_137_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨94, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 94 (by decide)))

theorem fz1_137_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨95, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 95 (by decide)))

theorem fz1_137_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨96, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 96 (by decide)))

theorem fz1_137_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨97, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 97 (by decide)))

theorem fz1_137_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨98, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 98 (by decide)))

theorem fz1_137_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨100, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 100 (by decide)))

theorem fz1_137_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨101, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 101 (by decide)))

theorem fz1_137_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨102, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 102 (by decide)))

theorem fz1_137_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨104, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 104 (by decide)))

theorem fz1_137_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨106, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 106 (by decide)))

theorem fz1_137_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨107, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 107 (by decide)))

theorem fz1_137_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨108, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 108 (by decide)))

theorem fz1_137_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨109, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 109 (by decide)))

theorem fz1_137_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨110, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 110 (by decide)))

theorem fz1_137_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨112, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 112 (by decide)))

theorem fz1_137_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨113, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 113 (by decide)))

theorem fz1_137_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨114, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 114 (by decide)))

theorem fz1_137_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨115, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 115 (by decide)))

theorem fz1_137_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨116, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 116 (by decide)))

theorem fz1_137_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨117, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 117 (by decide)))

theorem fz1_137_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨118, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 118 (by decide)))

theorem fz1_137_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨119, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 119 (by decide)))

theorem fz1_137_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨120, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 120 (by decide)))

theorem fz1_137_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨121, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 121 (by decide)))

theorem fz1_137_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨122, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 122 (by decide)))

theorem fz1_137_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨123, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 123 (by decide)))

theorem fz1_137_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨124, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 124 (by decide)))

theorem fz1_137_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨125, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 125 (by decide)))

theorem fz1_137_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨126, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 126 (by decide)))

theorem fz1_137_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨127, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 127 (by decide)))

theorem fz1_137_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨128, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 128 (by decide)))

theorem fz1_137_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨129, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 129 (by decide)))

theorem fz1_137_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨130, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 130 (by decide)))

theorem fz1_137_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨131, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 131 (by decide)))

theorem fz1_137_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨132, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 132 (by decide)))

theorem fz1_137_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨133, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 133 (by decide)))

theorem fz1_137_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨134, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 134 (by decide)))

theorem fz1_137_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨135, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 135 (by decide)))

theorem fz1_137_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨136, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 136 (by decide)))

theorem fz1_137_138 : Fintype.card
    (fixedPoints (reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨138, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 138 (by decide)))

theorem fz1_137_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨139, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 139 (by decide)))

theorem fz1_137_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨140, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 140 (by decide)))

theorem fz1_137_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨141, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 141 (by decide)))

theorem fz1_137_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨142, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 142 (by decide)))

theorem fz1_137_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨143, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 143 (by decide)))

theorem fz1_137_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨144, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 144 (by decide)))

theorem fz1_137_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨145, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 145 (by decide)))

theorem fz1_137_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK137)) = 0 :=
  repsFixedCard rK137 ⟨146, by decide⟩ R137 hpxR137 hcardq137
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_137) 146 (by decide)))

theorem fixz2_137 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 35, 36, 38, 39, 40, 42, 44, 45, 46, 47, 48, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 93, 94, 95, 96, 97, 98, 100, 101, 102, 104, 106, 107, 108, 109, 110, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 138, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK137) (retConj 2 (Q2.R137_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_137_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨1, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 1 (by decide)))

theorem fz2_137_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨2, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 2 (by decide)))

theorem fz2_137_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨3, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 3 (by decide)))

theorem fz2_137_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨4, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 4 (by decide)))

theorem fz2_137_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨6, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 6 (by decide)))

theorem fz2_137_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨7, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 7 (by decide)))

theorem fz2_137_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨8, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 8 (by decide)))

theorem fz2_137_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨9, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 9 (by decide)))

theorem fz2_137_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨11, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 11 (by decide)))

theorem fz2_137_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨13, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 13 (by decide)))

theorem fz2_137_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨14, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 14 (by decide)))

theorem fz2_137_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨15, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 15 (by decide)))

theorem fz2_137_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨16, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 16 (by decide)))

theorem fz2_137_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨17, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 17 (by decide)))

theorem fz2_137_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨18, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 18 (by decide)))

theorem fz2_137_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨19, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 19 (by decide)))

theorem fz2_137_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨20, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 20 (by decide)))

theorem fz2_137_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨21, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 21 (by decide)))

theorem fz2_137_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨22, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 22 (by decide)))

theorem fz2_137_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨24, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 24 (by decide)))

theorem fz2_137_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨25, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 25 (by decide)))

theorem fz2_137_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨26, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 26 (by decide)))

theorem fz2_137_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨27, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 27 (by decide)))

theorem fz2_137_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨28, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 28 (by decide)))

theorem fz2_137_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨29, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 29 (by decide)))

theorem fz2_137_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨31, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 31 (by decide)))

theorem fz2_137_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨32, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 32 (by decide)))

theorem fz2_137_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨33, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 33 (by decide)))

theorem fz2_137_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨34, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 34 (by decide)))

theorem fz2_137_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨35, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 35 (by decide)))

theorem fz2_137_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨36, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 36 (by decide)))

theorem fz2_137_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨38, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 38 (by decide)))

theorem fz2_137_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨39, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 39 (by decide)))

theorem fz2_137_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨40, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 40 (by decide)))

theorem fz2_137_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨42, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 42 (by decide)))

theorem fz2_137_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨44, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 44 (by decide)))

theorem fz2_137_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨45, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 45 (by decide)))

theorem fz2_137_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨46, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 46 (by decide)))

theorem fz2_137_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨47, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 47 (by decide)))

theorem fz2_137_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨48, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 48 (by decide)))

theorem fz2_137_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨50, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 50 (by decide)))

theorem fz2_137_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨51, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 51 (by decide)))

theorem fz2_137_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨52, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 52 (by decide)))

theorem fz2_137_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨54, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 54 (by decide)))

theorem fz2_137_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨55, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 55 (by decide)))

theorem fz2_137_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨56, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 56 (by decide)))

theorem fz2_137_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨57, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 57 (by decide)))

theorem fz2_137_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨58, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 58 (by decide)))

theorem fz2_137_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨59, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 59 (by decide)))

theorem fz2_137_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨60, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 60 (by decide)))

theorem fz2_137_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨61, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 61 (by decide)))

theorem fz2_137_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨62, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 62 (by decide)))

theorem fz2_137_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨63, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 63 (by decide)))

theorem fz2_137_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨64, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 64 (by decide)))

theorem fz2_137_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨65, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 65 (by decide)))

theorem fz2_137_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨66, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 66 (by decide)))

theorem fz2_137_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨67, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 67 (by decide)))

theorem fz2_137_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨68, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 68 (by decide)))

theorem fz2_137_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨69, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 69 (by decide)))

theorem fz2_137_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨70, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 70 (by decide)))

theorem fz2_137_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨71, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 71 (by decide)))

theorem fz2_137_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨72, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 72 (by decide)))

theorem fz2_137_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨73, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 73 (by decide)))

theorem fz2_137_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨74, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 74 (by decide)))

theorem fz2_137_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨75, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 75 (by decide)))

theorem fz2_137_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨76, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 76 (by decide)))

theorem fz2_137_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨77, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 77 (by decide)))

theorem fz2_137_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨78, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 78 (by decide)))

theorem fz2_137_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨79, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 79 (by decide)))

theorem fz2_137_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨80, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 80 (by decide)))

theorem fz2_137_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨81, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 81 (by decide)))

theorem fz2_137_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨82, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 82 (by decide)))

theorem fz2_137_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨83, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 83 (by decide)))

theorem fz2_137_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨85, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 85 (by decide)))

theorem fz2_137_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨86, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 86 (by decide)))

theorem fz2_137_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨87, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 87 (by decide)))

theorem fz2_137_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨88, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 88 (by decide)))

theorem fz2_137_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨89, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 89 (by decide)))

theorem fz2_137_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨90, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 90 (by decide)))

theorem fz2_137_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨91, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 91 (by decide)))

theorem fz2_137_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨93, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 93 (by decide)))

theorem fz2_137_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨94, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 94 (by decide)))

theorem fz2_137_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨95, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 95 (by decide)))

theorem fz2_137_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨96, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 96 (by decide)))

theorem fz2_137_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨97, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 97 (by decide)))

theorem fz2_137_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨98, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 98 (by decide)))

theorem fz2_137_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨100, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 100 (by decide)))

theorem fz2_137_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨101, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 101 (by decide)))

theorem fz2_137_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨102, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 102 (by decide)))

theorem fz2_137_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨104, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 104 (by decide)))

theorem fz2_137_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨106, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 106 (by decide)))

theorem fz2_137_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨107, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 107 (by decide)))

theorem fz2_137_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨108, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 108 (by decide)))

theorem fz2_137_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨109, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 109 (by decide)))

theorem fz2_137_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨110, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 110 (by decide)))

theorem fz2_137_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨112, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 112 (by decide)))

theorem fz2_137_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨113, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 113 (by decide)))

theorem fz2_137_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨114, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 114 (by decide)))

theorem fz2_137_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨115, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 115 (by decide)))

theorem fz2_137_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨116, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 116 (by decide)))

theorem fz2_137_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨117, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 117 (by decide)))

theorem fz2_137_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨118, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 118 (by decide)))

theorem fz2_137_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨119, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 119 (by decide)))

theorem fz2_137_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨120, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 120 (by decide)))

theorem fz2_137_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨121, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 121 (by decide)))

theorem fz2_137_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨122, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 122 (by decide)))

theorem fz2_137_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨123, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 123 (by decide)))

theorem fz2_137_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨124, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 124 (by decide)))

theorem fz2_137_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨125, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 125 (by decide)))

theorem fz2_137_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨126, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 126 (by decide)))

theorem fz2_137_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨127, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 127 (by decide)))

theorem fz2_137_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨128, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 128 (by decide)))

theorem fz2_137_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨129, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 129 (by decide)))

theorem fz2_137_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨130, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 130 (by decide)))

theorem fz2_137_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨131, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 131 (by decide)))

theorem fz2_137_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨132, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 132 (by decide)))

theorem fz2_137_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨133, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 133 (by decide)))

theorem fz2_137_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨134, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 134 (by decide)))

theorem fz2_137_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨135, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 135 (by decide)))

theorem fz2_137_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨136, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 136 (by decide)))

theorem fz2_137_138 : Fintype.card
    (fixedPoints (Q2.reps (⟨138, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨138, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 138 (by decide)))

theorem fz2_137_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨139, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 139 (by decide)))

theorem fz2_137_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨140, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 140 (by decide)))

theorem fz2_137_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨141, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 141 (by decide)))

theorem fz2_137_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨142, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 142 (by decide)))

theorem fz2_137_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨143, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 143 (by decide)))

theorem fz2_137_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨144, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 144 (by decide)))

theorem fz2_137_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨145, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 145 (by decide)))

theorem fz2_137_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK137)) = 0 :=
  Q2.repsFixedCard2 rK137 ⟨146, by decide⟩ Q2.R137_2 Q2.hpxR137_2 Q2.hcardq137_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_137) 146 (by decide)))

theorem fixz1_138 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 34, 35, 36, 37, 38, 39, 40, 41, 43, 45, 46, 47, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92, 94, 96, 97, 98, 99, 100, 101, 102, 103, 105, 107, 108, 109, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK138) (retConj 1 (R138 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_138_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨1, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 1 (by decide)))

theorem fz1_138_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨2, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 2 (by decide)))

theorem fz1_138_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨3, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 3 (by decide)))

theorem fz1_138_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨4, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 4 (by decide)))

theorem fz1_138_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨6, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 6 (by decide)))

theorem fz1_138_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨7, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 7 (by decide)))

theorem fz1_138_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨8, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 8 (by decide)))

theorem fz1_138_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨9, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 9 (by decide)))

theorem fz1_138_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨11, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 11 (by decide)))

theorem fz1_138_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨13, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 13 (by decide)))

theorem fz1_138_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨14, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 14 (by decide)))

theorem fz1_138_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨15, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 15 (by decide)))

theorem fz1_138_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨16, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 16 (by decide)))

theorem fz1_138_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨17, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 17 (by decide)))

theorem fz1_138_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨18, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 18 (by decide)))

theorem fz1_138_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨19, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 19 (by decide)))

theorem fz1_138_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨20, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 20 (by decide)))

theorem fz1_138_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨21, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 21 (by decide)))

theorem fz1_138_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨22, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 22 (by decide)))

theorem fz1_138_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨24, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 24 (by decide)))

theorem fz1_138_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨25, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 25 (by decide)))

theorem fz1_138_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨26, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 26 (by decide)))

theorem fz1_138_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨27, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 27 (by decide)))

theorem fz1_138_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨28, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 28 (by decide)))

theorem fz1_138_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨29, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 29 (by decide)))

theorem fz1_138_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨30, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 30 (by decide)))

theorem fz1_138_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨32, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 32 (by decide)))

theorem fz1_138_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨34, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 34 (by decide)))

theorem fz1_138_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨35, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 35 (by decide)))

theorem fz1_138_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨36, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 36 (by decide)))

theorem fz1_138_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨37, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 37 (by decide)))

theorem fz1_138_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨38, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 38 (by decide)))

theorem fz1_138_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨39, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 39 (by decide)))

theorem fz1_138_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨40, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 40 (by decide)))

theorem fz1_138_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨41, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 41 (by decide)))

theorem fz1_138_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨43, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 43 (by decide)))

theorem fz1_138_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨45, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 45 (by decide)))

theorem fz1_138_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨46, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 46 (by decide)))

theorem fz1_138_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨47, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 47 (by decide)))

theorem fz1_138_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨48, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 48 (by decide)))

theorem fz1_138_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨49, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 49 (by decide)))

theorem fz1_138_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨51, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 51 (by decide)))

theorem fz1_138_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨52, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 52 (by decide)))

theorem fz1_138_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨54, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 54 (by decide)))

theorem fz1_138_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨55, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 55 (by decide)))

theorem fz1_138_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨56, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 56 (by decide)))

theorem fz1_138_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨57, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 57 (by decide)))

theorem fz1_138_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨58, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 58 (by decide)))

theorem fz1_138_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨59, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 59 (by decide)))

theorem fz1_138_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨60, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 60 (by decide)))

theorem fz1_138_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨61, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 61 (by decide)))

theorem fz1_138_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨62, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 62 (by decide)))

theorem fz1_138_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨63, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 63 (by decide)))

theorem fz1_138_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨64, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 64 (by decide)))

theorem fz1_138_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨65, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 65 (by decide)))

theorem fz1_138_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨66, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 66 (by decide)))

theorem fz1_138_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨67, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 67 (by decide)))

theorem fz1_138_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨68, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 68 (by decide)))

theorem fz1_138_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨69, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 69 (by decide)))

theorem fz1_138_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨70, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 70 (by decide)))

theorem fz1_138_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨71, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 71 (by decide)))

theorem fz1_138_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨72, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 72 (by decide)))

theorem fz1_138_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨73, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 73 (by decide)))

theorem fz1_138_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨74, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 74 (by decide)))

theorem fz1_138_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨75, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 75 (by decide)))

theorem fz1_138_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨76, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 76 (by decide)))

theorem fz1_138_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨77, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 77 (by decide)))

theorem fz1_138_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨78, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 78 (by decide)))

theorem fz1_138_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨79, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 79 (by decide)))

theorem fz1_138_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨80, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 80 (by decide)))

theorem fz1_138_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨81, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 81 (by decide)))

theorem fz1_138_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨82, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 82 (by decide)))

theorem fz1_138_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨83, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 83 (by decide)))

theorem fz1_138_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨85, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 85 (by decide)))

theorem fz1_138_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨86, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 86 (by decide)))

theorem fz1_138_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨87, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 87 (by decide)))

theorem fz1_138_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨88, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 88 (by decide)))

theorem fz1_138_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨89, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 89 (by decide)))

theorem fz1_138_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨90, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 90 (by decide)))

theorem fz1_138_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨91, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 91 (by decide)))

theorem fz1_138_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨92, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 92 (by decide)))

theorem fz1_138_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨94, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 94 (by decide)))

theorem fz1_138_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨96, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 96 (by decide)))

theorem fz1_138_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨97, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 97 (by decide)))

theorem fz1_138_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨98, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 98 (by decide)))

theorem fz1_138_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨99, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 99 (by decide)))

theorem fz1_138_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨100, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 100 (by decide)))

theorem fz1_138_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨101, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 101 (by decide)))

theorem fz1_138_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨102, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 102 (by decide)))

theorem fz1_138_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨103, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 103 (by decide)))

theorem fz1_138_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨105, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 105 (by decide)))

theorem fz1_138_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨107, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 107 (by decide)))

theorem fz1_138_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨108, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 108 (by decide)))

theorem fz1_138_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨109, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 109 (by decide)))

theorem fz1_138_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨110, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 110 (by decide)))

theorem fz1_138_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨111, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 111 (by decide)))

theorem fz1_138_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨113, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 113 (by decide)))

theorem fz1_138_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨114, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 114 (by decide)))

theorem fz1_138_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨115, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 115 (by decide)))

theorem fz1_138_116 : Fintype.card
    (fixedPoints (reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨116, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 116 (by decide)))

theorem fz1_138_117 : Fintype.card
    (fixedPoints (reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨117, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 117 (by decide)))

theorem fz1_138_118 : Fintype.card
    (fixedPoints (reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨118, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 118 (by decide)))

theorem fz1_138_119 : Fintype.card
    (fixedPoints (reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨119, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 119 (by decide)))

theorem fz1_138_120 : Fintype.card
    (fixedPoints (reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨120, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 120 (by decide)))

theorem fz1_138_121 : Fintype.card
    (fixedPoints (reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨121, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 121 (by decide)))

theorem fz1_138_122 : Fintype.card
    (fixedPoints (reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨122, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 122 (by decide)))

theorem fz1_138_123 : Fintype.card
    (fixedPoints (reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨123, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 123 (by decide)))

theorem fz1_138_124 : Fintype.card
    (fixedPoints (reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨124, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 124 (by decide)))

theorem fz1_138_125 : Fintype.card
    (fixedPoints (reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨125, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 125 (by decide)))

theorem fz1_138_126 : Fintype.card
    (fixedPoints (reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨126, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 126 (by decide)))

theorem fz1_138_127 : Fintype.card
    (fixedPoints (reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨127, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 127 (by decide)))

theorem fz1_138_128 : Fintype.card
    (fixedPoints (reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨128, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 128 (by decide)))

theorem fz1_138_129 : Fintype.card
    (fixedPoints (reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨129, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 129 (by decide)))

theorem fz1_138_130 : Fintype.card
    (fixedPoints (reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨130, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 130 (by decide)))

theorem fz1_138_131 : Fintype.card
    (fixedPoints (reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨131, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 131 (by decide)))

theorem fz1_138_132 : Fintype.card
    (fixedPoints (reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨132, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 132 (by decide)))

theorem fz1_138_133 : Fintype.card
    (fixedPoints (reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨133, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 133 (by decide)))

theorem fz1_138_134 : Fintype.card
    (fixedPoints (reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨134, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 134 (by decide)))

theorem fz1_138_135 : Fintype.card
    (fixedPoints (reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨135, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 135 (by decide)))

theorem fz1_138_136 : Fintype.card
    (fixedPoints (reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨136, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 136 (by decide)))

theorem fz1_138_137 : Fintype.card
    (fixedPoints (reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨137, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 137 (by decide)))

theorem fz1_138_139 : Fintype.card
    (fixedPoints (reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨139, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 139 (by decide)))

theorem fz1_138_140 : Fintype.card
    (fixedPoints (reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨140, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 140 (by decide)))

theorem fz1_138_141 : Fintype.card
    (fixedPoints (reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨141, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 141 (by decide)))

theorem fz1_138_142 : Fintype.card
    (fixedPoints (reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨142, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 142 (by decide)))

theorem fz1_138_143 : Fintype.card
    (fixedPoints (reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨143, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 143 (by decide)))

theorem fz1_138_144 : Fintype.card
    (fixedPoints (reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨144, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 144 (by decide)))

theorem fz1_138_145 : Fintype.card
    (fixedPoints (reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨145, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 145 (by decide)))

theorem fz1_138_146 : Fintype.card
    (fixedPoints (reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK138)) = 0 :=
  repsFixedCard rK138 ⟨146, by decide⟩ R138 hpxR138 hcardq138
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_138) 146 (by decide)))

theorem fixz2_138 : ([1, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 32, 34, 35, 36, 37, 38, 39, 40, 41, 43, 45, 46, 47, 48, 49, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 85, 86, 87, 88, 89, 90, 91, 92, 94, 96, 97, 98, 99, 100, 101, 102, 103, 105, 107, 108, 109, 110, 111, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 139, 140, 141, 142, 143, 144, 145, 146] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 5 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK138) (retConj 2 (Q2.R138_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_138_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨1, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 1 (by decide)))

theorem fz2_138_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨2, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 2 (by decide)))

theorem fz2_138_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨3, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 3 (by decide)))

theorem fz2_138_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨4, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 4 (by decide)))

theorem fz2_138_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨6, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 6 (by decide)))

theorem fz2_138_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨7, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 7 (by decide)))

theorem fz2_138_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨8, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 8 (by decide)))

theorem fz2_138_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨9, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 9 (by decide)))

theorem fz2_138_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨11, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 11 (by decide)))

theorem fz2_138_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨13, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 13 (by decide)))

theorem fz2_138_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨14, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 14 (by decide)))

theorem fz2_138_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨15, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 15 (by decide)))

theorem fz2_138_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨16, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 16 (by decide)))

theorem fz2_138_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨17, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 17 (by decide)))

theorem fz2_138_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨18, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 18 (by decide)))

theorem fz2_138_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨19, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 19 (by decide)))

theorem fz2_138_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨20, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 20 (by decide)))

theorem fz2_138_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨21, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 21 (by decide)))

theorem fz2_138_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨22, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 22 (by decide)))

theorem fz2_138_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨24, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 24 (by decide)))

theorem fz2_138_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨25, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 25 (by decide)))

theorem fz2_138_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨26, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 26 (by decide)))

theorem fz2_138_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨27, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 27 (by decide)))

theorem fz2_138_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨28, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 28 (by decide)))

theorem fz2_138_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨29, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 29 (by decide)))

theorem fz2_138_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨30, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 30 (by decide)))

theorem fz2_138_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨32, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 32 (by decide)))

theorem fz2_138_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨34, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 34 (by decide)))

theorem fz2_138_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨35, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 35 (by decide)))

theorem fz2_138_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨36, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 36 (by decide)))

theorem fz2_138_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨37, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 37 (by decide)))

theorem fz2_138_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨38, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 38 (by decide)))

theorem fz2_138_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨39, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 39 (by decide)))

theorem fz2_138_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨40, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 40 (by decide)))

theorem fz2_138_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨41, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 41 (by decide)))

theorem fz2_138_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨43, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 43 (by decide)))

theorem fz2_138_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨45, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 45 (by decide)))

theorem fz2_138_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨46, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 46 (by decide)))

theorem fz2_138_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨47, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 47 (by decide)))

theorem fz2_138_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨48, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 48 (by decide)))

theorem fz2_138_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨49, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 49 (by decide)))

theorem fz2_138_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨51, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 51 (by decide)))

theorem fz2_138_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨52, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 52 (by decide)))

theorem fz2_138_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨54, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 54 (by decide)))

theorem fz2_138_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨55, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 55 (by decide)))

theorem fz2_138_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨56, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 56 (by decide)))

theorem fz2_138_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨57, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 57 (by decide)))

theorem fz2_138_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨58, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 58 (by decide)))

theorem fz2_138_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨59, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 59 (by decide)))

theorem fz2_138_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨60, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 60 (by decide)))

theorem fz2_138_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨61, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 61 (by decide)))

theorem fz2_138_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨62, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 62 (by decide)))

theorem fz2_138_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨63, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 63 (by decide)))

theorem fz2_138_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨64, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 64 (by decide)))

theorem fz2_138_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨65, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 65 (by decide)))

theorem fz2_138_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨66, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 66 (by decide)))

theorem fz2_138_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨67, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 67 (by decide)))

theorem fz2_138_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨68, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 68 (by decide)))

theorem fz2_138_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨69, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 69 (by decide)))

theorem fz2_138_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨70, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 70 (by decide)))

theorem fz2_138_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨71, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 71 (by decide)))

theorem fz2_138_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨72, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 72 (by decide)))

theorem fz2_138_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨73, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 73 (by decide)))

theorem fz2_138_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨74, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 74 (by decide)))

theorem fz2_138_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨75, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 75 (by decide)))

theorem fz2_138_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨76, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 76 (by decide)))

theorem fz2_138_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨77, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 77 (by decide)))

theorem fz2_138_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨78, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 78 (by decide)))

theorem fz2_138_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨79, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 79 (by decide)))

theorem fz2_138_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨80, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 80 (by decide)))

theorem fz2_138_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨81, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 81 (by decide)))

theorem fz2_138_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨82, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 82 (by decide)))

theorem fz2_138_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨83, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 83 (by decide)))

theorem fz2_138_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨85, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 85 (by decide)))

theorem fz2_138_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨86, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 86 (by decide)))

theorem fz2_138_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨87, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 87 (by decide)))

theorem fz2_138_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨88, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 88 (by decide)))

theorem fz2_138_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨89, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 89 (by decide)))

theorem fz2_138_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨90, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 90 (by decide)))

theorem fz2_138_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨91, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 91 (by decide)))

theorem fz2_138_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨92, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 92 (by decide)))

theorem fz2_138_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨94, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 94 (by decide)))

theorem fz2_138_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨96, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 96 (by decide)))

theorem fz2_138_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨97, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 97 (by decide)))

theorem fz2_138_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨98, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 98 (by decide)))

theorem fz2_138_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨99, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 99 (by decide)))

theorem fz2_138_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨100, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 100 (by decide)))

theorem fz2_138_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨101, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 101 (by decide)))

theorem fz2_138_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨102, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 102 (by decide)))

theorem fz2_138_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨103, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 103 (by decide)))

theorem fz2_138_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨105, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 105 (by decide)))

theorem fz2_138_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨107, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 107 (by decide)))

theorem fz2_138_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨108, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 108 (by decide)))

theorem fz2_138_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨109, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 109 (by decide)))

theorem fz2_138_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨110, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 110 (by decide)))

theorem fz2_138_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨111, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 111 (by decide)))

theorem fz2_138_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨113, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 113 (by decide)))

theorem fz2_138_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨114, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 114 (by decide)))

theorem fz2_138_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨115, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 115 (by decide)))

theorem fz2_138_116 : Fintype.card
    (fixedPoints (Q2.reps (⟨116, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨116, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 116 (by decide)))

theorem fz2_138_117 : Fintype.card
    (fixedPoints (Q2.reps (⟨117, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨117, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 117 (by decide)))

theorem fz2_138_118 : Fintype.card
    (fixedPoints (Q2.reps (⟨118, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨118, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 118 (by decide)))

theorem fz2_138_119 : Fintype.card
    (fixedPoints (Q2.reps (⟨119, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨119, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 119 (by decide)))

theorem fz2_138_120 : Fintype.card
    (fixedPoints (Q2.reps (⟨120, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨120, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 120 (by decide)))

theorem fz2_138_121 : Fintype.card
    (fixedPoints (Q2.reps (⟨121, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨121, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 121 (by decide)))

theorem fz2_138_122 : Fintype.card
    (fixedPoints (Q2.reps (⟨122, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨122, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 122 (by decide)))

theorem fz2_138_123 : Fintype.card
    (fixedPoints (Q2.reps (⟨123, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨123, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 123 (by decide)))

theorem fz2_138_124 : Fintype.card
    (fixedPoints (Q2.reps (⟨124, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨124, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 124 (by decide)))

theorem fz2_138_125 : Fintype.card
    (fixedPoints (Q2.reps (⟨125, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨125, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 125 (by decide)))

theorem fz2_138_126 : Fintype.card
    (fixedPoints (Q2.reps (⟨126, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨126, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 126 (by decide)))

theorem fz2_138_127 : Fintype.card
    (fixedPoints (Q2.reps (⟨127, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨127, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 127 (by decide)))

theorem fz2_138_128 : Fintype.card
    (fixedPoints (Q2.reps (⟨128, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨128, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 128 (by decide)))

theorem fz2_138_129 : Fintype.card
    (fixedPoints (Q2.reps (⟨129, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨129, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 129 (by decide)))

theorem fz2_138_130 : Fintype.card
    (fixedPoints (Q2.reps (⟨130, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨130, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 130 (by decide)))

theorem fz2_138_131 : Fintype.card
    (fixedPoints (Q2.reps (⟨131, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨131, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 131 (by decide)))

theorem fz2_138_132 : Fintype.card
    (fixedPoints (Q2.reps (⟨132, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨132, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 132 (by decide)))

theorem fz2_138_133 : Fintype.card
    (fixedPoints (Q2.reps (⟨133, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨133, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 133 (by decide)))

theorem fz2_138_134 : Fintype.card
    (fixedPoints (Q2.reps (⟨134, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨134, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 134 (by decide)))

theorem fz2_138_135 : Fintype.card
    (fixedPoints (Q2.reps (⟨135, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨135, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 135 (by decide)))

theorem fz2_138_136 : Fintype.card
    (fixedPoints (Q2.reps (⟨136, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨136, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 136 (by decide)))

theorem fz2_138_137 : Fintype.card
    (fixedPoints (Q2.reps (⟨137, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨137, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 137 (by decide)))

theorem fz2_138_139 : Fintype.card
    (fixedPoints (Q2.reps (⟨139, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨139, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 139 (by decide)))

theorem fz2_138_140 : Fintype.card
    (fixedPoints (Q2.reps (⟨140, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨140, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 140 (by decide)))

theorem fz2_138_141 : Fintype.card
    (fixedPoints (Q2.reps (⟨141, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨141, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 141 (by decide)))

theorem fz2_138_142 : Fintype.card
    (fixedPoints (Q2.reps (⟨142, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨142, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 142 (by decide)))

theorem fz2_138_143 : Fintype.card
    (fixedPoints (Q2.reps (⟨143, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨143, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 143 (by decide)))

theorem fz2_138_144 : Fintype.card
    (fixedPoints (Q2.reps (⟨144, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨144, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 144 (by decide)))

theorem fz2_138_145 : Fintype.card
    (fixedPoints (Q2.reps (⟨145, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨145, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 145 (by decide)))

theorem fz2_138_146 : Fintype.card
    (fixedPoints (Q2.reps (⟨146, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK138)) = 0 :=
  Q2.repsFixedCard2 rK138 ⟨146, by decide⟩ Q2.R138_2 Q2.hpxR138_2 Q2.hcardq138_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_138) 146 (by decide)))

end LeanDring.P5Presentation
