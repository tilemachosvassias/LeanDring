/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C023

/-!
# Species-table cells, off-support emptiness certificates, chunk 78

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

theorem fixz1_103 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK103) (retConj 1 (R103 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_103_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨1, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 1 (by decide)))

theorem fz1_103_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨2, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 2 (by decide)))

theorem fz1_103_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨3, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 3 (by decide)))

theorem fz1_103_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨4, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 4 (by decide)))

theorem fz1_103_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨5, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 5 (by decide)))

theorem fz1_103_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨6, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 6 (by decide)))

theorem fz1_103_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨7, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 7 (by decide)))

theorem fz1_103_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨8, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 8 (by decide)))

theorem fz1_103_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨9, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 9 (by decide)))

theorem fz1_103_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨11, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 11 (by decide)))

theorem fz1_103_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨13, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 13 (by decide)))

theorem fz1_103_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨14, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 14 (by decide)))

theorem fz1_103_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨15, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 15 (by decide)))

theorem fz1_103_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨16, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 16 (by decide)))

theorem fz1_103_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨17, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 17 (by decide)))

theorem fz1_103_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨18, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 18 (by decide)))

theorem fz1_103_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨19, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 19 (by decide)))

theorem fz1_103_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨20, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 20 (by decide)))

theorem fz1_103_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨21, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 21 (by decide)))

theorem fz1_103_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨22, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 22 (by decide)))

theorem fz1_103_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨23, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 23 (by decide)))

theorem fz1_103_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨24, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 24 (by decide)))

theorem fz1_103_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨25, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 25 (by decide)))

theorem fz1_103_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨26, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 26 (by decide)))

theorem fz1_103_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨27, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 27 (by decide)))

theorem fz1_103_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨28, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 28 (by decide)))

theorem fz1_103_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨29, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 29 (by decide)))

theorem fz1_103_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨30, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 30 (by decide)))

theorem fz1_103_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨31, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 31 (by decide)))

theorem fz1_103_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨32, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 32 (by decide)))

theorem fz1_103_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨33, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 33 (by decide)))

theorem fz1_103_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨34, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 34 (by decide)))

theorem fz1_103_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨35, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 35 (by decide)))

theorem fz1_103_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨36, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 36 (by decide)))

theorem fz1_103_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨37, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 37 (by decide)))

theorem fz1_103_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨38, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 38 (by decide)))

theorem fz1_103_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨39, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 39 (by decide)))

theorem fz1_103_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨40, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 40 (by decide)))

theorem fz1_103_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨42, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 42 (by decide)))

theorem fz1_103_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨43, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 43 (by decide)))

theorem fz1_103_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨44, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 44 (by decide)))

theorem fz1_103_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨45, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 45 (by decide)))

theorem fz1_103_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨46, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 46 (by decide)))

theorem fz1_103_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨47, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 47 (by decide)))

theorem fz1_103_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨48, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 48 (by decide)))

theorem fz1_103_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨49, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 49 (by decide)))

theorem fz1_103_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨50, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 50 (by decide)))

theorem fz1_103_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨51, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 51 (by decide)))

theorem fz1_103_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨52, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 52 (by decide)))

theorem fz1_103_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨54, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 54 (by decide)))

theorem fz1_103_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨55, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 55 (by decide)))

theorem fz1_103_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨56, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 56 (by decide)))

theorem fz1_103_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨57, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 57 (by decide)))

theorem fz1_103_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨58, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 58 (by decide)))

theorem fz1_103_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨59, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 59 (by decide)))

theorem fz1_103_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨60, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 60 (by decide)))

theorem fz1_103_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨61, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 61 (by decide)))

theorem fz1_103_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨62, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 62 (by decide)))

theorem fz1_103_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨63, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 63 (by decide)))

theorem fz1_103_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨64, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 64 (by decide)))

theorem fz1_103_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨65, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 65 (by decide)))

theorem fz1_103_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨66, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 66 (by decide)))

theorem fz1_103_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨67, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 67 (by decide)))

theorem fz1_103_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨68, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 68 (by decide)))

theorem fz1_103_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨69, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 69 (by decide)))

theorem fz1_103_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨70, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 70 (by decide)))

theorem fz1_103_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨71, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 71 (by decide)))

theorem fz1_103_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨72, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 72 (by decide)))

theorem fz1_103_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨73, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 73 (by decide)))

theorem fz1_103_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨74, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 74 (by decide)))

theorem fz1_103_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨75, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 75 (by decide)))

theorem fz1_103_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨76, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 76 (by decide)))

theorem fz1_103_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨77, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 77 (by decide)))

theorem fz1_103_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨78, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 78 (by decide)))

theorem fz1_103_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨79, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 79 (by decide)))

theorem fz1_103_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨80, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 80 (by decide)))

theorem fz1_103_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨81, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 81 (by decide)))

theorem fz1_103_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨82, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 82 (by decide)))

theorem fz1_103_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨83, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 83 (by decide)))

theorem fz1_103_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨84, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 84 (by decide)))

theorem fz1_103_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨85, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 85 (by decide)))

theorem fz1_103_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨86, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 86 (by decide)))

theorem fz1_103_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨87, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 87 (by decide)))

theorem fz1_103_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨88, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 88 (by decide)))

theorem fz1_103_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨89, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 89 (by decide)))

theorem fz1_103_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨90, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 90 (by decide)))

theorem fz1_103_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨91, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 91 (by decide)))

theorem fz1_103_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨92, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 92 (by decide)))

theorem fz1_103_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨93, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 93 (by decide)))

theorem fz1_103_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨94, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 94 (by decide)))

theorem fz1_103_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨95, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 95 (by decide)))

theorem fz1_103_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨96, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 96 (by decide)))

theorem fz1_103_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨97, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 97 (by decide)))

theorem fz1_103_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨98, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 98 (by decide)))

theorem fz1_103_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨99, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 99 (by decide)))

theorem fz1_103_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨100, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 100 (by decide)))

theorem fz1_103_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨101, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 101 (by decide)))

theorem fz1_103_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨102, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 102 (by decide)))

theorem fz1_103_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨104, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 104 (by decide)))

theorem fz1_103_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨105, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 105 (by decide)))

theorem fz1_103_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨106, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 106 (by decide)))

theorem fz1_103_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨107, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 107 (by decide)))

theorem fz1_103_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨108, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 108 (by decide)))

theorem fz1_103_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨109, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 109 (by decide)))

theorem fz1_103_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨110, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 110 (by decide)))

theorem fz1_103_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨111, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 111 (by decide)))

theorem fz1_103_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨112, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 112 (by decide)))

theorem fz1_103_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨113, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 113 (by decide)))

theorem fz1_103_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨114, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 114 (by decide)))

theorem fz1_103_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK103)) = 0 :=
  repsFixedCard rK103 ⟨115, by decide⟩ R103 hpxR103 hcardq103
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_103) 115 (by decide)))

theorem fixz2_103 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK103) (retConj 2 (Q2.R103_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_103_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨1, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 1 (by decide)))

theorem fz2_103_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨2, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 2 (by decide)))

theorem fz2_103_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨3, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 3 (by decide)))

theorem fz2_103_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨4, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 4 (by decide)))

theorem fz2_103_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨5, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 5 (by decide)))

theorem fz2_103_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨6, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 6 (by decide)))

theorem fz2_103_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨7, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 7 (by decide)))

theorem fz2_103_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨8, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 8 (by decide)))

theorem fz2_103_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨9, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 9 (by decide)))

theorem fz2_103_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨11, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 11 (by decide)))

theorem fz2_103_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨13, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 13 (by decide)))

theorem fz2_103_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨14, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 14 (by decide)))

theorem fz2_103_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨15, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 15 (by decide)))

theorem fz2_103_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨16, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 16 (by decide)))

theorem fz2_103_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨17, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 17 (by decide)))

theorem fz2_103_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨18, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 18 (by decide)))

theorem fz2_103_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨19, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 19 (by decide)))

theorem fz2_103_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨20, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 20 (by decide)))

theorem fz2_103_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨21, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 21 (by decide)))

theorem fz2_103_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨22, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 22 (by decide)))

theorem fz2_103_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨23, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 23 (by decide)))

theorem fz2_103_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨24, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 24 (by decide)))

theorem fz2_103_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨25, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 25 (by decide)))

theorem fz2_103_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨26, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 26 (by decide)))

theorem fz2_103_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨27, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 27 (by decide)))

theorem fz2_103_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨28, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 28 (by decide)))

theorem fz2_103_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨29, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 29 (by decide)))

theorem fz2_103_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨30, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 30 (by decide)))

theorem fz2_103_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨31, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 31 (by decide)))

theorem fz2_103_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨32, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 32 (by decide)))

theorem fz2_103_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨33, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 33 (by decide)))

theorem fz2_103_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨34, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 34 (by decide)))

theorem fz2_103_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨35, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 35 (by decide)))

theorem fz2_103_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨36, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 36 (by decide)))

theorem fz2_103_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨37, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 37 (by decide)))

theorem fz2_103_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨38, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 38 (by decide)))

theorem fz2_103_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨39, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 39 (by decide)))

theorem fz2_103_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨40, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 40 (by decide)))

theorem fz2_103_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨42, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 42 (by decide)))

theorem fz2_103_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨43, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 43 (by decide)))

theorem fz2_103_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨44, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 44 (by decide)))

theorem fz2_103_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨45, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 45 (by decide)))

theorem fz2_103_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨46, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 46 (by decide)))

theorem fz2_103_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨47, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 47 (by decide)))

theorem fz2_103_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨48, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 48 (by decide)))

theorem fz2_103_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨49, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 49 (by decide)))

theorem fz2_103_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨50, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 50 (by decide)))

theorem fz2_103_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨51, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 51 (by decide)))

theorem fz2_103_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨52, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 52 (by decide)))

theorem fz2_103_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨54, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 54 (by decide)))

theorem fz2_103_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨55, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 55 (by decide)))

theorem fz2_103_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨56, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 56 (by decide)))

theorem fz2_103_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨57, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 57 (by decide)))

theorem fz2_103_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨58, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 58 (by decide)))

theorem fz2_103_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨59, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 59 (by decide)))

theorem fz2_103_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨60, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 60 (by decide)))

theorem fz2_103_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨61, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 61 (by decide)))

theorem fz2_103_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨62, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 62 (by decide)))

theorem fz2_103_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨63, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 63 (by decide)))

theorem fz2_103_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨64, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 64 (by decide)))

theorem fz2_103_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨65, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 65 (by decide)))

theorem fz2_103_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨66, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 66 (by decide)))

theorem fz2_103_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨67, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 67 (by decide)))

theorem fz2_103_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨68, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 68 (by decide)))

theorem fz2_103_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨69, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 69 (by decide)))

theorem fz2_103_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨70, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 70 (by decide)))

theorem fz2_103_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨71, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 71 (by decide)))

theorem fz2_103_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨72, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 72 (by decide)))

theorem fz2_103_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨73, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 73 (by decide)))

theorem fz2_103_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨74, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 74 (by decide)))

theorem fz2_103_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨75, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 75 (by decide)))

theorem fz2_103_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨76, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 76 (by decide)))

theorem fz2_103_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨77, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 77 (by decide)))

theorem fz2_103_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨78, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 78 (by decide)))

theorem fz2_103_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨79, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 79 (by decide)))

theorem fz2_103_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨80, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 80 (by decide)))

theorem fz2_103_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨81, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 81 (by decide)))

theorem fz2_103_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨82, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 82 (by decide)))

theorem fz2_103_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨83, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 83 (by decide)))

theorem fz2_103_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨84, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 84 (by decide)))

theorem fz2_103_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨85, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 85 (by decide)))

theorem fz2_103_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨86, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 86 (by decide)))

theorem fz2_103_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨87, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 87 (by decide)))

theorem fz2_103_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨88, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 88 (by decide)))

theorem fz2_103_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨89, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 89 (by decide)))

theorem fz2_103_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨90, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 90 (by decide)))

theorem fz2_103_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨91, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 91 (by decide)))

theorem fz2_103_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨92, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 92 (by decide)))

theorem fz2_103_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨93, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 93 (by decide)))

theorem fz2_103_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨94, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 94 (by decide)))

theorem fz2_103_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨95, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 95 (by decide)))

theorem fz2_103_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨96, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 96 (by decide)))

theorem fz2_103_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨97, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 97 (by decide)))

theorem fz2_103_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨98, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 98 (by decide)))

theorem fz2_103_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨99, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 99 (by decide)))

theorem fz2_103_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨100, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 100 (by decide)))

theorem fz2_103_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨101, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 101 (by decide)))

theorem fz2_103_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨102, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 102 (by decide)))

theorem fz2_103_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨104, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 104 (by decide)))

theorem fz2_103_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨105, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 105 (by decide)))

theorem fz2_103_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨106, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 106 (by decide)))

theorem fz2_103_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨107, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 107 (by decide)))

theorem fz2_103_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨108, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 108 (by decide)))

theorem fz2_103_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨109, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 109 (by decide)))

theorem fz2_103_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨110, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 110 (by decide)))

theorem fz2_103_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨111, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 111 (by decide)))

theorem fz2_103_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨112, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 112 (by decide)))

theorem fz2_103_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨113, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 113 (by decide)))

theorem fz2_103_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨114, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 114 (by decide)))

theorem fz2_103_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK103)) = 0 :=
  Q2.repsFixedCard2 rK103 ⟨115, by decide⟩ Q2.R103_2 Q2.hpxR103_2 Q2.hcardq103_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_103) 115 (by decide)))

theorem fixz1_104 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK104) (retConj 1 (R104 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_104_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨1, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 1 (by decide)))

theorem fz1_104_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨2, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 2 (by decide)))

theorem fz1_104_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨3, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 3 (by decide)))

theorem fz1_104_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨4, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 4 (by decide)))

theorem fz1_104_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨5, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 5 (by decide)))

theorem fz1_104_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨6, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 6 (by decide)))

theorem fz1_104_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨7, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 7 (by decide)))

theorem fz1_104_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨8, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 8 (by decide)))

theorem fz1_104_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨9, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 9 (by decide)))

theorem fz1_104_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨11, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 11 (by decide)))

theorem fz1_104_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨13, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 13 (by decide)))

theorem fz1_104_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨14, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 14 (by decide)))

theorem fz1_104_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨15, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 15 (by decide)))

theorem fz1_104_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨16, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 16 (by decide)))

theorem fz1_104_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨17, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 17 (by decide)))

theorem fz1_104_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨18, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 18 (by decide)))

theorem fz1_104_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨19, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 19 (by decide)))

theorem fz1_104_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨20, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 20 (by decide)))

theorem fz1_104_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨21, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 21 (by decide)))

theorem fz1_104_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨22, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 22 (by decide)))

theorem fz1_104_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨23, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 23 (by decide)))

theorem fz1_104_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨24, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 24 (by decide)))

theorem fz1_104_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨25, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 25 (by decide)))

theorem fz1_104_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨26, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 26 (by decide)))

theorem fz1_104_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨27, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 27 (by decide)))

theorem fz1_104_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨28, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 28 (by decide)))

theorem fz1_104_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨29, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 29 (by decide)))

theorem fz1_104_30 : Fintype.card
    (fixedPoints (reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨30, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 30 (by decide)))

theorem fz1_104_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨31, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 31 (by decide)))

theorem fz1_104_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨32, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 32 (by decide)))

theorem fz1_104_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨33, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 33 (by decide)))

theorem fz1_104_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨34, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 34 (by decide)))

theorem fz1_104_35 : Fintype.card
    (fixedPoints (reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨35, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 35 (by decide)))

theorem fz1_104_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨36, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 36 (by decide)))

theorem fz1_104_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨37, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 37 (by decide)))

theorem fz1_104_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨38, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 38 (by decide)))

theorem fz1_104_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨39, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 39 (by decide)))

theorem fz1_104_40 : Fintype.card
    (fixedPoints (reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨40, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 40 (by decide)))

theorem fz1_104_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨41, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 41 (by decide)))

theorem fz1_104_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨43, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 43 (by decide)))

theorem fz1_104_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨44, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 44 (by decide)))

theorem fz1_104_45 : Fintype.card
    (fixedPoints (reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨45, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 45 (by decide)))

theorem fz1_104_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨46, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 46 (by decide)))

theorem fz1_104_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨47, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 47 (by decide)))

theorem fz1_104_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨48, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 48 (by decide)))

theorem fz1_104_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨49, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 49 (by decide)))

theorem fz1_104_50 : Fintype.card
    (fixedPoints (reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨50, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 50 (by decide)))

theorem fz1_104_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨51, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 51 (by decide)))

theorem fz1_104_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨52, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 52 (by decide)))

theorem fz1_104_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨54, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 54 (by decide)))

theorem fz1_104_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨55, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 55 (by decide)))

theorem fz1_104_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨56, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 56 (by decide)))

theorem fz1_104_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨57, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 57 (by decide)))

theorem fz1_104_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨58, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 58 (by decide)))

theorem fz1_104_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨59, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 59 (by decide)))

theorem fz1_104_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨60, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 60 (by decide)))

theorem fz1_104_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨61, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 61 (by decide)))

theorem fz1_104_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨62, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 62 (by decide)))

theorem fz1_104_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨63, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 63 (by decide)))

theorem fz1_104_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨64, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 64 (by decide)))

theorem fz1_104_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨65, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 65 (by decide)))

theorem fz1_104_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨66, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 66 (by decide)))

theorem fz1_104_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨67, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 67 (by decide)))

theorem fz1_104_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨68, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 68 (by decide)))

theorem fz1_104_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨69, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 69 (by decide)))

theorem fz1_104_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨70, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 70 (by decide)))

theorem fz1_104_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨71, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 71 (by decide)))

theorem fz1_104_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨72, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 72 (by decide)))

theorem fz1_104_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨73, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 73 (by decide)))

theorem fz1_104_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨74, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 74 (by decide)))

theorem fz1_104_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨75, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 75 (by decide)))

theorem fz1_104_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨76, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 76 (by decide)))

theorem fz1_104_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨77, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 77 (by decide)))

theorem fz1_104_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨78, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 78 (by decide)))

theorem fz1_104_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨79, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 79 (by decide)))

theorem fz1_104_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨80, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 80 (by decide)))

theorem fz1_104_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨81, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 81 (by decide)))

theorem fz1_104_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨82, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 82 (by decide)))

theorem fz1_104_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨83, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 83 (by decide)))

theorem fz1_104_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨84, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 84 (by decide)))

theorem fz1_104_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨85, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 85 (by decide)))

theorem fz1_104_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨86, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 86 (by decide)))

theorem fz1_104_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨87, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 87 (by decide)))

theorem fz1_104_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨88, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 88 (by decide)))

theorem fz1_104_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨89, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 89 (by decide)))

theorem fz1_104_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨90, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 90 (by decide)))

theorem fz1_104_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨91, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 91 (by decide)))

theorem fz1_104_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨92, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 92 (by decide)))

theorem fz1_104_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨93, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 93 (by decide)))

theorem fz1_104_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨94, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 94 (by decide)))

theorem fz1_104_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨95, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 95 (by decide)))

theorem fz1_104_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨96, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 96 (by decide)))

theorem fz1_104_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨97, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 97 (by decide)))

theorem fz1_104_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨98, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 98 (by decide)))

theorem fz1_104_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨99, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 99 (by decide)))

theorem fz1_104_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨100, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 100 (by decide)))

theorem fz1_104_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨101, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 101 (by decide)))

theorem fz1_104_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨102, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 102 (by decide)))

theorem fz1_104_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨103, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 103 (by decide)))

theorem fz1_104_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨105, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 105 (by decide)))

theorem fz1_104_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨106, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 106 (by decide)))

theorem fz1_104_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨107, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 107 (by decide)))

theorem fz1_104_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨108, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 108 (by decide)))

theorem fz1_104_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨109, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 109 (by decide)))

theorem fz1_104_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨110, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 110 (by decide)))

theorem fz1_104_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨111, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 111 (by decide)))

theorem fz1_104_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨112, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 112 (by decide)))

theorem fz1_104_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨113, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 113 (by decide)))

theorem fz1_104_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨114, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 114 (by decide)))

theorem fz1_104_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK104)) = 0 :=
  repsFixedCard rK104 ⟨115, by decide⟩ R104 hpxR104 hcardq104
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_104) 115 (by decide)))

theorem fixz2_104 : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK104) (retConj 2 (Q2.R104_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_104_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨1, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 1 (by decide)))

theorem fz2_104_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨2, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 2 (by decide)))

theorem fz2_104_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨3, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 3 (by decide)))

theorem fz2_104_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨4, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 4 (by decide)))

theorem fz2_104_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨5, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 5 (by decide)))

theorem fz2_104_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨6, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 6 (by decide)))

theorem fz2_104_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨7, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 7 (by decide)))

theorem fz2_104_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨8, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 8 (by decide)))

theorem fz2_104_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨9, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 9 (by decide)))

theorem fz2_104_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨11, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 11 (by decide)))

theorem fz2_104_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨13, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 13 (by decide)))

theorem fz2_104_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨14, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 14 (by decide)))

theorem fz2_104_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨15, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 15 (by decide)))

theorem fz2_104_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨16, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 16 (by decide)))

theorem fz2_104_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨17, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 17 (by decide)))

theorem fz2_104_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨18, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 18 (by decide)))

theorem fz2_104_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨19, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 19 (by decide)))

theorem fz2_104_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨20, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 20 (by decide)))

theorem fz2_104_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨21, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 21 (by decide)))

theorem fz2_104_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨22, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 22 (by decide)))

theorem fz2_104_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨23, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 23 (by decide)))

theorem fz2_104_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨24, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 24 (by decide)))

theorem fz2_104_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨25, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 25 (by decide)))

theorem fz2_104_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨26, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 26 (by decide)))

theorem fz2_104_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨27, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 27 (by decide)))

theorem fz2_104_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨28, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 28 (by decide)))

theorem fz2_104_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨29, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 29 (by decide)))

theorem fz2_104_30 : Fintype.card
    (fixedPoints (Q2.reps (⟨30, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨30, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 30 (by decide)))

theorem fz2_104_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨31, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 31 (by decide)))

theorem fz2_104_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨32, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 32 (by decide)))

theorem fz2_104_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨33, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 33 (by decide)))

theorem fz2_104_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨34, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 34 (by decide)))

theorem fz2_104_35 : Fintype.card
    (fixedPoints (Q2.reps (⟨35, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨35, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 35 (by decide)))

theorem fz2_104_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨36, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 36 (by decide)))

theorem fz2_104_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨37, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 37 (by decide)))

theorem fz2_104_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨38, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 38 (by decide)))

theorem fz2_104_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨39, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 39 (by decide)))

theorem fz2_104_40 : Fintype.card
    (fixedPoints (Q2.reps (⟨40, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨40, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 40 (by decide)))

theorem fz2_104_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨41, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 41 (by decide)))

theorem fz2_104_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨43, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 43 (by decide)))

theorem fz2_104_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨44, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 44 (by decide)))

theorem fz2_104_45 : Fintype.card
    (fixedPoints (Q2.reps (⟨45, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨45, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 45 (by decide)))

theorem fz2_104_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨46, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 46 (by decide)))

theorem fz2_104_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨47, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 47 (by decide)))

theorem fz2_104_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨48, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 48 (by decide)))

theorem fz2_104_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨49, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 49 (by decide)))

theorem fz2_104_50 : Fintype.card
    (fixedPoints (Q2.reps (⟨50, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨50, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 50 (by decide)))

theorem fz2_104_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨51, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 51 (by decide)))

theorem fz2_104_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨52, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 52 (by decide)))

theorem fz2_104_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨54, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 54 (by decide)))

theorem fz2_104_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨55, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 55 (by decide)))

theorem fz2_104_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨56, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 56 (by decide)))

theorem fz2_104_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨57, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 57 (by decide)))

theorem fz2_104_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨58, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 58 (by decide)))

theorem fz2_104_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨59, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 59 (by decide)))

theorem fz2_104_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨60, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 60 (by decide)))

theorem fz2_104_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨61, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 61 (by decide)))

theorem fz2_104_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨62, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 62 (by decide)))

theorem fz2_104_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨63, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 63 (by decide)))

theorem fz2_104_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨64, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 64 (by decide)))

theorem fz2_104_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨65, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 65 (by decide)))

theorem fz2_104_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨66, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 66 (by decide)))

theorem fz2_104_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨67, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 67 (by decide)))

theorem fz2_104_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨68, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 68 (by decide)))

theorem fz2_104_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨69, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 69 (by decide)))

theorem fz2_104_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨70, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 70 (by decide)))

theorem fz2_104_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨71, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 71 (by decide)))

theorem fz2_104_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨72, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 72 (by decide)))

theorem fz2_104_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨73, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 73 (by decide)))

theorem fz2_104_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨74, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 74 (by decide)))

theorem fz2_104_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨75, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 75 (by decide)))

theorem fz2_104_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨76, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 76 (by decide)))

theorem fz2_104_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨77, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 77 (by decide)))

theorem fz2_104_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨78, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 78 (by decide)))

theorem fz2_104_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨79, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 79 (by decide)))

theorem fz2_104_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨80, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 80 (by decide)))

theorem fz2_104_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨81, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 81 (by decide)))

theorem fz2_104_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨82, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 82 (by decide)))

theorem fz2_104_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨83, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 83 (by decide)))

theorem fz2_104_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨84, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 84 (by decide)))

theorem fz2_104_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨85, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 85 (by decide)))

theorem fz2_104_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨86, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 86 (by decide)))

theorem fz2_104_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨87, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 87 (by decide)))

theorem fz2_104_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨88, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 88 (by decide)))

theorem fz2_104_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨89, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 89 (by decide)))

theorem fz2_104_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨90, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 90 (by decide)))

theorem fz2_104_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨91, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 91 (by decide)))

theorem fz2_104_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨92, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 92 (by decide)))

theorem fz2_104_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨93, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 93 (by decide)))

theorem fz2_104_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨94, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 94 (by decide)))

theorem fz2_104_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨95, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 95 (by decide)))

theorem fz2_104_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨96, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 96 (by decide)))

theorem fz2_104_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨97, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 97 (by decide)))

theorem fz2_104_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨98, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 98 (by decide)))

theorem fz2_104_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨99, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 99 (by decide)))

theorem fz2_104_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨100, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 100 (by decide)))

theorem fz2_104_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨101, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 101 (by decide)))

theorem fz2_104_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨102, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 102 (by decide)))

theorem fz2_104_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨103, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 103 (by decide)))

theorem fz2_104_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨105, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 105 (by decide)))

theorem fz2_104_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨106, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 106 (by decide)))

theorem fz2_104_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨107, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 107 (by decide)))

theorem fz2_104_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨108, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 108 (by decide)))

theorem fz2_104_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨109, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 109 (by decide)))

theorem fz2_104_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨110, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 110 (by decide)))

theorem fz2_104_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨111, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 111 (by decide)))

theorem fz2_104_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨112, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 112 (by decide)))

theorem fz2_104_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨113, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 113 (by decide)))

theorem fz2_104_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨114, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 114 (by decide)))

theorem fz2_104_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK104)) = 0 :=
  Q2.repsFixedCard2 rK104 ⟨115, by decide⟩ Q2.R104_2 Q2.hpxR104_2 Q2.hcardq104_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_104) 115 (by decide)))

end LeanDring.P5Presentation
