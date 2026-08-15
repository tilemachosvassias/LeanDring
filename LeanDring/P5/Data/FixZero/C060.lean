/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Data.EntryK.C016

/-!
# Species-table cells, off-support emptiness certificates, chunk 59

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

theorem fixz1_65 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK65) (retConj 1 (R65 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_65_1 : Fintype.card
    (fixedPoints (reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨1, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 1 (by decide)))

theorem fz1_65_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨2, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 2 (by decide)))

theorem fz1_65_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨3, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 3 (by decide)))

theorem fz1_65_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨4, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 4 (by decide)))

theorem fz1_65_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨5, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 5 (by decide)))

theorem fz1_65_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨6, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 6 (by decide)))

theorem fz1_65_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨7, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 7 (by decide)))

theorem fz1_65_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨8, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 8 (by decide)))

theorem fz1_65_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨10, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 10 (by decide)))

theorem fz1_65_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨11, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 11 (by decide)))

theorem fz1_65_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨13, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 13 (by decide)))

theorem fz1_65_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨14, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 14 (by decide)))

theorem fz1_65_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨15, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 15 (by decide)))

theorem fz1_65_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨16, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 16 (by decide)))

theorem fz1_65_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨17, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 17 (by decide)))

theorem fz1_65_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨18, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 18 (by decide)))

theorem fz1_65_19 : Fintype.card
    (fixedPoints (reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨19, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 19 (by decide)))

theorem fz1_65_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨20, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 20 (by decide)))

theorem fz1_65_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨21, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 21 (by decide)))

theorem fz1_65_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨22, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 22 (by decide)))

theorem fz1_65_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨23, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 23 (by decide)))

theorem fz1_65_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨24, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 24 (by decide)))

theorem fz1_65_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨25, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 25 (by decide)))

theorem fz1_65_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨26, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 26 (by decide)))

theorem fz1_65_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨28, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 28 (by decide)))

theorem fz1_65_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨29, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 29 (by decide)))

theorem fz1_65_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨31, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 31 (by decide)))

theorem fz1_65_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨32, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 32 (by decide)))

theorem fz1_65_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨33, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 33 (by decide)))

theorem fz1_65_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨34, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 34 (by decide)))

theorem fz1_65_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨36, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 36 (by decide)))

theorem fz1_65_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨37, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 37 (by decide)))

theorem fz1_65_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨38, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 38 (by decide)))

theorem fz1_65_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨39, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 39 (by decide)))

theorem fz1_65_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨41, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 41 (by decide)))

theorem fz1_65_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨42, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 42 (by decide)))

theorem fz1_65_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨43, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 43 (by decide)))

theorem fz1_65_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨44, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 44 (by decide)))

theorem fz1_65_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨46, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 46 (by decide)))

theorem fz1_65_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨47, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 47 (by decide)))

theorem fz1_65_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨48, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 48 (by decide)))

theorem fz1_65_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨49, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 49 (by decide)))

theorem fz1_65_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨51, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 51 (by decide)))

theorem fz1_65_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨52, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 52 (by decide)))

theorem fz1_65_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨53, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 53 (by decide)))

theorem fz1_65_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨54, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 54 (by decide)))

theorem fz1_65_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨55, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 55 (by decide)))

theorem fz1_65_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨56, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 56 (by decide)))

theorem fz1_65_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨57, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 57 (by decide)))

theorem fz1_65_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨58, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 58 (by decide)))

theorem fz1_65_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨59, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 59 (by decide)))

theorem fz1_65_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨60, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 60 (by decide)))

theorem fz1_65_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨61, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 61 (by decide)))

theorem fz1_65_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨62, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 62 (by decide)))

theorem fz1_65_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨63, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 63 (by decide)))

theorem fz1_65_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨64, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 64 (by decide)))

theorem fz1_65_66 : Fintype.card
    (fixedPoints (reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨66, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 66 (by decide)))

theorem fz1_65_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨67, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 67 (by decide)))

theorem fz1_65_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨68, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 68 (by decide)))

theorem fz1_65_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨69, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 69 (by decide)))

theorem fz1_65_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨70, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 70 (by decide)))

theorem fz1_65_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨71, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 71 (by decide)))

theorem fz1_65_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨72, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 72 (by decide)))

theorem fz1_65_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨73, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 73 (by decide)))

theorem fz1_65_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨74, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 74 (by decide)))

theorem fz1_65_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨75, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 75 (by decide)))

theorem fz1_65_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨76, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 76 (by decide)))

theorem fz1_65_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨77, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 77 (by decide)))

theorem fz1_65_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨78, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 78 (by decide)))

theorem fz1_65_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨79, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 79 (by decide)))

theorem fz1_65_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨80, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 80 (by decide)))

theorem fz1_65_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨81, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 81 (by decide)))

theorem fz1_65_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨82, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 82 (by decide)))

theorem fz1_65_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨83, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 83 (by decide)))

theorem fz1_65_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨84, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 84 (by decide)))

theorem fz1_65_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨85, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 85 (by decide)))

theorem fz1_65_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨86, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 86 (by decide)))

theorem fz1_65_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨87, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 87 (by decide)))

theorem fz1_65_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨88, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 88 (by decide)))

theorem fz1_65_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨89, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 89 (by decide)))

theorem fz1_65_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨90, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 90 (by decide)))

theorem fz1_65_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨91, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 91 (by decide)))

theorem fz1_65_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨92, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 92 (by decide)))

theorem fz1_65_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨93, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 93 (by decide)))

theorem fz1_65_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨94, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 94 (by decide)))

theorem fz1_65_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨95, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 95 (by decide)))

theorem fz1_65_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨96, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 96 (by decide)))

theorem fz1_65_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨97, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 97 (by decide)))

theorem fz1_65_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨98, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 98 (by decide)))

theorem fz1_65_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨99, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 99 (by decide)))

theorem fz1_65_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨100, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 100 (by decide)))

theorem fz1_65_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨101, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 101 (by decide)))

theorem fz1_65_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨102, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 102 (by decide)))

theorem fz1_65_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨103, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 103 (by decide)))

theorem fz1_65_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨104, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 104 (by decide)))

theorem fz1_65_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨105, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 105 (by decide)))

theorem fz1_65_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨106, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 106 (by decide)))

theorem fz1_65_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨107, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 107 (by decide)))

theorem fz1_65_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨108, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 108 (by decide)))

theorem fz1_65_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨109, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 109 (by decide)))

theorem fz1_65_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨110, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 110 (by decide)))

theorem fz1_65_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨111, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 111 (by decide)))

theorem fz1_65_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨112, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 112 (by decide)))

theorem fz1_65_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨113, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 113 (by decide)))

theorem fz1_65_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨114, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 114 (by decide)))

theorem fz1_65_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK65)) = 0 :=
  repsFixedCard rK65 ⟨115, by decide⟩ R65 hpxR65 hcardq65
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_65) 115 (by decide)))

theorem fixz2_65 : ([1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK65) (retConj 2 (Q2.R65_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_65_1 : Fintype.card
    (fixedPoints (Q2.reps (⟨1, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨1, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 1 (by decide)))

theorem fz2_65_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨2, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 2 (by decide)))

theorem fz2_65_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨3, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 3 (by decide)))

theorem fz2_65_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨4, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 4 (by decide)))

theorem fz2_65_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨5, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 5 (by decide)))

theorem fz2_65_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨6, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 6 (by decide)))

theorem fz2_65_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨7, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 7 (by decide)))

theorem fz2_65_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨8, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 8 (by decide)))

theorem fz2_65_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨10, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 10 (by decide)))

theorem fz2_65_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨11, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 11 (by decide)))

theorem fz2_65_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨13, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 13 (by decide)))

theorem fz2_65_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨14, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 14 (by decide)))

theorem fz2_65_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨15, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 15 (by decide)))

theorem fz2_65_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨16, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 16 (by decide)))

theorem fz2_65_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨17, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 17 (by decide)))

theorem fz2_65_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨18, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 18 (by decide)))

theorem fz2_65_19 : Fintype.card
    (fixedPoints (Q2.reps (⟨19, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨19, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 19 (by decide)))

theorem fz2_65_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨20, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 20 (by decide)))

theorem fz2_65_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨21, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 21 (by decide)))

theorem fz2_65_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨22, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 22 (by decide)))

theorem fz2_65_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨23, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 23 (by decide)))

theorem fz2_65_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨24, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 24 (by decide)))

theorem fz2_65_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨25, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 25 (by decide)))

theorem fz2_65_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨26, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 26 (by decide)))

theorem fz2_65_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨28, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 28 (by decide)))

theorem fz2_65_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨29, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 29 (by decide)))

theorem fz2_65_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨31, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 31 (by decide)))

theorem fz2_65_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨32, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 32 (by decide)))

theorem fz2_65_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨33, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 33 (by decide)))

theorem fz2_65_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨34, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 34 (by decide)))

theorem fz2_65_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨36, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 36 (by decide)))

theorem fz2_65_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨37, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 37 (by decide)))

theorem fz2_65_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨38, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 38 (by decide)))

theorem fz2_65_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨39, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 39 (by decide)))

theorem fz2_65_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨41, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 41 (by decide)))

theorem fz2_65_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨42, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 42 (by decide)))

theorem fz2_65_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨43, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 43 (by decide)))

theorem fz2_65_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨44, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 44 (by decide)))

theorem fz2_65_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨46, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 46 (by decide)))

theorem fz2_65_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨47, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 47 (by decide)))

theorem fz2_65_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨48, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 48 (by decide)))

theorem fz2_65_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨49, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 49 (by decide)))

theorem fz2_65_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨51, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 51 (by decide)))

theorem fz2_65_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨52, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 52 (by decide)))

theorem fz2_65_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨53, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 53 (by decide)))

theorem fz2_65_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨54, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 54 (by decide)))

theorem fz2_65_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨55, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 55 (by decide)))

theorem fz2_65_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨56, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 56 (by decide)))

theorem fz2_65_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨57, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 57 (by decide)))

theorem fz2_65_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨58, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 58 (by decide)))

theorem fz2_65_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨59, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 59 (by decide)))

theorem fz2_65_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨60, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 60 (by decide)))

theorem fz2_65_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨61, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 61 (by decide)))

theorem fz2_65_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨62, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 62 (by decide)))

theorem fz2_65_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨63, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 63 (by decide)))

theorem fz2_65_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨64, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 64 (by decide)))

theorem fz2_65_66 : Fintype.card
    (fixedPoints (Q2.reps (⟨66, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨66, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 66 (by decide)))

theorem fz2_65_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨67, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 67 (by decide)))

theorem fz2_65_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨68, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 68 (by decide)))

theorem fz2_65_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨69, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 69 (by decide)))

theorem fz2_65_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨70, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 70 (by decide)))

theorem fz2_65_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨71, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 71 (by decide)))

theorem fz2_65_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨72, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 72 (by decide)))

theorem fz2_65_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨73, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 73 (by decide)))

theorem fz2_65_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨74, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 74 (by decide)))

theorem fz2_65_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨75, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 75 (by decide)))

theorem fz2_65_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨76, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 76 (by decide)))

theorem fz2_65_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨77, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 77 (by decide)))

theorem fz2_65_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨78, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 78 (by decide)))

theorem fz2_65_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨79, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 79 (by decide)))

theorem fz2_65_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨80, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 80 (by decide)))

theorem fz2_65_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨81, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 81 (by decide)))

theorem fz2_65_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨82, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 82 (by decide)))

theorem fz2_65_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨83, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 83 (by decide)))

theorem fz2_65_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨84, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 84 (by decide)))

theorem fz2_65_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨85, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 85 (by decide)))

theorem fz2_65_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨86, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 86 (by decide)))

theorem fz2_65_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨87, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 87 (by decide)))

theorem fz2_65_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨88, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 88 (by decide)))

theorem fz2_65_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨89, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 89 (by decide)))

theorem fz2_65_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨90, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 90 (by decide)))

theorem fz2_65_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨91, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 91 (by decide)))

theorem fz2_65_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨92, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 92 (by decide)))

theorem fz2_65_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨93, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 93 (by decide)))

theorem fz2_65_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨94, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 94 (by decide)))

theorem fz2_65_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨95, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 95 (by decide)))

theorem fz2_65_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨96, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 96 (by decide)))

theorem fz2_65_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨97, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 97 (by decide)))

theorem fz2_65_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨98, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 98 (by decide)))

theorem fz2_65_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨99, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 99 (by decide)))

theorem fz2_65_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨100, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 100 (by decide)))

theorem fz2_65_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨101, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 101 (by decide)))

theorem fz2_65_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨102, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 102 (by decide)))

theorem fz2_65_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨103, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 103 (by decide)))

theorem fz2_65_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨104, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 104 (by decide)))

theorem fz2_65_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨105, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 105 (by decide)))

theorem fz2_65_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨106, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 106 (by decide)))

theorem fz2_65_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨107, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 107 (by decide)))

theorem fz2_65_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨108, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 108 (by decide)))

theorem fz2_65_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨109, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 109 (by decide)))

theorem fz2_65_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨110, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 110 (by decide)))

theorem fz2_65_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨111, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 111 (by decide)))

theorem fz2_65_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨112, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 112 (by decide)))

theorem fz2_65_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨113, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 113 (by decide)))

theorem fz2_65_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨114, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 114 (by decide)))

theorem fz2_65_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK65)) = 0 :=
  Q2.repsFixedCard2 rK65 ⟨115, by decide⟩ Q2.R65_2 Q2.hpxR65_2 Q2.hcardq65_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_65) 115 (by decide)))

theorem fixz1_66 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (repBases.getD rH []).all
      (fun g => siftB 1 (basisAt rK66) (retConj 1 (R66 i) g)) = true)).card = 0)) = true := by decide

theorem fz1_66_2 : Fintype.card
    (fixedPoints (reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨2, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 2 (by decide)))

theorem fz1_66_3 : Fintype.card
    (fixedPoints (reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨3, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 3 (by decide)))

theorem fz1_66_4 : Fintype.card
    (fixedPoints (reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨4, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 4 (by decide)))

theorem fz1_66_5 : Fintype.card
    (fixedPoints (reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨5, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 5 (by decide)))

theorem fz1_66_6 : Fintype.card
    (fixedPoints (reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨6, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 6 (by decide)))

theorem fz1_66_7 : Fintype.card
    (fixedPoints (reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨7, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 7 (by decide)))

theorem fz1_66_8 : Fintype.card
    (fixedPoints (reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨8, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 8 (by decide)))

theorem fz1_66_9 : Fintype.card
    (fixedPoints (reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨9, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 9 (by decide)))

theorem fz1_66_10 : Fintype.card
    (fixedPoints (reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨10, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 10 (by decide)))

theorem fz1_66_11 : Fintype.card
    (fixedPoints (reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨11, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 11 (by decide)))

theorem fz1_66_13 : Fintype.card
    (fixedPoints (reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨13, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 13 (by decide)))

theorem fz1_66_14 : Fintype.card
    (fixedPoints (reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨14, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 14 (by decide)))

theorem fz1_66_15 : Fintype.card
    (fixedPoints (reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨15, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 15 (by decide)))

theorem fz1_66_16 : Fintype.card
    (fixedPoints (reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨16, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 16 (by decide)))

theorem fz1_66_17 : Fintype.card
    (fixedPoints (reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨17, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 17 (by decide)))

theorem fz1_66_18 : Fintype.card
    (fixedPoints (reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨18, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 18 (by decide)))

theorem fz1_66_20 : Fintype.card
    (fixedPoints (reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨20, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 20 (by decide)))

theorem fz1_66_21 : Fintype.card
    (fixedPoints (reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨21, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 21 (by decide)))

theorem fz1_66_22 : Fintype.card
    (fixedPoints (reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨22, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 22 (by decide)))

theorem fz1_66_23 : Fintype.card
    (fixedPoints (reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨23, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 23 (by decide)))

theorem fz1_66_24 : Fintype.card
    (fixedPoints (reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨24, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 24 (by decide)))

theorem fz1_66_25 : Fintype.card
    (fixedPoints (reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨25, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 25 (by decide)))

theorem fz1_66_26 : Fintype.card
    (fixedPoints (reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨26, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 26 (by decide)))

theorem fz1_66_27 : Fintype.card
    (fixedPoints (reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨27, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 27 (by decide)))

theorem fz1_66_28 : Fintype.card
    (fixedPoints (reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨28, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 28 (by decide)))

theorem fz1_66_29 : Fintype.card
    (fixedPoints (reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨29, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 29 (by decide)))

theorem fz1_66_31 : Fintype.card
    (fixedPoints (reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨31, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 31 (by decide)))

theorem fz1_66_32 : Fintype.card
    (fixedPoints (reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨32, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 32 (by decide)))

theorem fz1_66_33 : Fintype.card
    (fixedPoints (reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨33, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 33 (by decide)))

theorem fz1_66_34 : Fintype.card
    (fixedPoints (reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨34, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 34 (by decide)))

theorem fz1_66_36 : Fintype.card
    (fixedPoints (reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨36, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 36 (by decide)))

theorem fz1_66_37 : Fintype.card
    (fixedPoints (reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨37, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 37 (by decide)))

theorem fz1_66_38 : Fintype.card
    (fixedPoints (reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨38, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 38 (by decide)))

theorem fz1_66_39 : Fintype.card
    (fixedPoints (reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨39, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 39 (by decide)))

theorem fz1_66_41 : Fintype.card
    (fixedPoints (reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨41, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 41 (by decide)))

theorem fz1_66_42 : Fintype.card
    (fixedPoints (reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨42, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 42 (by decide)))

theorem fz1_66_43 : Fintype.card
    (fixedPoints (reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨43, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 43 (by decide)))

theorem fz1_66_44 : Fintype.card
    (fixedPoints (reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨44, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 44 (by decide)))

theorem fz1_66_46 : Fintype.card
    (fixedPoints (reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨46, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 46 (by decide)))

theorem fz1_66_47 : Fintype.card
    (fixedPoints (reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨47, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 47 (by decide)))

theorem fz1_66_48 : Fintype.card
    (fixedPoints (reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨48, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 48 (by decide)))

theorem fz1_66_49 : Fintype.card
    (fixedPoints (reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨49, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 49 (by decide)))

theorem fz1_66_51 : Fintype.card
    (fixedPoints (reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨51, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 51 (by decide)))

theorem fz1_66_52 : Fintype.card
    (fixedPoints (reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨52, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 52 (by decide)))

theorem fz1_66_53 : Fintype.card
    (fixedPoints (reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨53, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 53 (by decide)))

theorem fz1_66_54 : Fintype.card
    (fixedPoints (reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨54, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 54 (by decide)))

theorem fz1_66_55 : Fintype.card
    (fixedPoints (reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨55, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 55 (by decide)))

theorem fz1_66_56 : Fintype.card
    (fixedPoints (reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨56, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 56 (by decide)))

theorem fz1_66_57 : Fintype.card
    (fixedPoints (reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨57, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 57 (by decide)))

theorem fz1_66_58 : Fintype.card
    (fixedPoints (reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨58, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 58 (by decide)))

theorem fz1_66_59 : Fintype.card
    (fixedPoints (reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨59, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 59 (by decide)))

theorem fz1_66_60 : Fintype.card
    (fixedPoints (reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨60, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 60 (by decide)))

theorem fz1_66_61 : Fintype.card
    (fixedPoints (reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨61, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 61 (by decide)))

theorem fz1_66_62 : Fintype.card
    (fixedPoints (reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨62, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 62 (by decide)))

theorem fz1_66_63 : Fintype.card
    (fixedPoints (reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨63, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 63 (by decide)))

theorem fz1_66_64 : Fintype.card
    (fixedPoints (reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨64, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 64 (by decide)))

theorem fz1_66_65 : Fintype.card
    (fixedPoints (reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨65, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 65 (by decide)))

theorem fz1_66_67 : Fintype.card
    (fixedPoints (reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨67, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 67 (by decide)))

theorem fz1_66_68 : Fintype.card
    (fixedPoints (reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨68, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 68 (by decide)))

theorem fz1_66_69 : Fintype.card
    (fixedPoints (reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨69, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 69 (by decide)))

theorem fz1_66_70 : Fintype.card
    (fixedPoints (reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨70, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 70 (by decide)))

theorem fz1_66_71 : Fintype.card
    (fixedPoints (reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨71, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 71 (by decide)))

theorem fz1_66_72 : Fintype.card
    (fixedPoints (reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨72, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 72 (by decide)))

theorem fz1_66_73 : Fintype.card
    (fixedPoints (reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨73, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 73 (by decide)))

theorem fz1_66_74 : Fintype.card
    (fixedPoints (reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨74, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 74 (by decide)))

theorem fz1_66_75 : Fintype.card
    (fixedPoints (reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨75, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 75 (by decide)))

theorem fz1_66_76 : Fintype.card
    (fixedPoints (reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨76, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 76 (by decide)))

theorem fz1_66_77 : Fintype.card
    (fixedPoints (reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨77, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 77 (by decide)))

theorem fz1_66_78 : Fintype.card
    (fixedPoints (reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨78, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 78 (by decide)))

theorem fz1_66_79 : Fintype.card
    (fixedPoints (reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨79, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 79 (by decide)))

theorem fz1_66_80 : Fintype.card
    (fixedPoints (reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨80, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 80 (by decide)))

theorem fz1_66_81 : Fintype.card
    (fixedPoints (reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨81, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 81 (by decide)))

theorem fz1_66_82 : Fintype.card
    (fixedPoints (reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨82, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 82 (by decide)))

theorem fz1_66_83 : Fintype.card
    (fixedPoints (reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨83, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 83 (by decide)))

theorem fz1_66_84 : Fintype.card
    (fixedPoints (reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨84, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 84 (by decide)))

theorem fz1_66_85 : Fintype.card
    (fixedPoints (reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨85, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 85 (by decide)))

theorem fz1_66_86 : Fintype.card
    (fixedPoints (reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨86, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 86 (by decide)))

theorem fz1_66_87 : Fintype.card
    (fixedPoints (reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨87, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 87 (by decide)))

theorem fz1_66_88 : Fintype.card
    (fixedPoints (reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨88, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 88 (by decide)))

theorem fz1_66_89 : Fintype.card
    (fixedPoints (reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨89, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 89 (by decide)))

theorem fz1_66_90 : Fintype.card
    (fixedPoints (reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨90, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 90 (by decide)))

theorem fz1_66_91 : Fintype.card
    (fixedPoints (reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨91, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 91 (by decide)))

theorem fz1_66_92 : Fintype.card
    (fixedPoints (reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨92, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 92 (by decide)))

theorem fz1_66_93 : Fintype.card
    (fixedPoints (reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨93, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 93 (by decide)))

theorem fz1_66_94 : Fintype.card
    (fixedPoints (reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨94, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 94 (by decide)))

theorem fz1_66_95 : Fintype.card
    (fixedPoints (reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨95, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 95 (by decide)))

theorem fz1_66_96 : Fintype.card
    (fixedPoints (reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨96, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 96 (by decide)))

theorem fz1_66_97 : Fintype.card
    (fixedPoints (reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨97, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 97 (by decide)))

theorem fz1_66_98 : Fintype.card
    (fixedPoints (reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨98, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 98 (by decide)))

theorem fz1_66_99 : Fintype.card
    (fixedPoints (reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨99, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 99 (by decide)))

theorem fz1_66_100 : Fintype.card
    (fixedPoints (reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨100, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 100 (by decide)))

theorem fz1_66_101 : Fintype.card
    (fixedPoints (reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨101, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 101 (by decide)))

theorem fz1_66_102 : Fintype.card
    (fixedPoints (reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨102, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 102 (by decide)))

theorem fz1_66_103 : Fintype.card
    (fixedPoints (reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨103, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 103 (by decide)))

theorem fz1_66_104 : Fintype.card
    (fixedPoints (reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨104, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 104 (by decide)))

theorem fz1_66_105 : Fintype.card
    (fixedPoints (reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨105, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 105 (by decide)))

theorem fz1_66_106 : Fintype.card
    (fixedPoints (reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨106, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 106 (by decide)))

theorem fz1_66_107 : Fintype.card
    (fixedPoints (reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨107, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 107 (by decide)))

theorem fz1_66_108 : Fintype.card
    (fixedPoints (reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨108, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 108 (by decide)))

theorem fz1_66_109 : Fintype.card
    (fixedPoints (reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨109, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 109 (by decide)))

theorem fz1_66_110 : Fintype.card
    (fixedPoints (reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨110, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 110 (by decide)))

theorem fz1_66_111 : Fintype.card
    (fixedPoints (reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨111, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 111 (by decide)))

theorem fz1_66_112 : Fintype.card
    (fixedPoints (reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨112, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 112 (by decide)))

theorem fz1_66_113 : Fintype.card
    (fixedPoints (reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨113, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 113 (by decide)))

theorem fz1_66_114 : Fintype.card
    (fixedPoints (reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨114, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 114 (by decide)))

theorem fz1_66_115 : Fintype.card
    (fixedPoints (reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 1 ⧸ reps rK66)) = 0 :=
  repsFixedCard rK66 ⟨115, by decide⟩ R66 hpxR66 hcardq66
    (of_decide_eq_true ((List.all_eq_true.mp fixz1_66) 115 (by decide)))

theorem fixz2_66 : ([2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115] : List Nat).all (fun rH =>
    decide ((Finset.univ.filter (fun i : Fin 25 => (Q2.repBases2.getD rH []).all
      (fun g => siftB 2 (Q2.basisAt2 rK66) (retConj 2 (Q2.R66_2 i) g)) = true)).card = 0)) = true := by decide

theorem fz2_66_2 : Fintype.card
    (fixedPoints (Q2.reps (⟨2, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨2, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 2 (by decide)))

theorem fz2_66_3 : Fintype.card
    (fixedPoints (Q2.reps (⟨3, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨3, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 3 (by decide)))

theorem fz2_66_4 : Fintype.card
    (fixedPoints (Q2.reps (⟨4, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨4, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 4 (by decide)))

theorem fz2_66_5 : Fintype.card
    (fixedPoints (Q2.reps (⟨5, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨5, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 5 (by decide)))

theorem fz2_66_6 : Fintype.card
    (fixedPoints (Q2.reps (⟨6, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨6, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 6 (by decide)))

theorem fz2_66_7 : Fintype.card
    (fixedPoints (Q2.reps (⟨7, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨7, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 7 (by decide)))

theorem fz2_66_8 : Fintype.card
    (fixedPoints (Q2.reps (⟨8, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨8, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 8 (by decide)))

theorem fz2_66_9 : Fintype.card
    (fixedPoints (Q2.reps (⟨9, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨9, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 9 (by decide)))

theorem fz2_66_10 : Fintype.card
    (fixedPoints (Q2.reps (⟨10, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨10, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 10 (by decide)))

theorem fz2_66_11 : Fintype.card
    (fixedPoints (Q2.reps (⟨11, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨11, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 11 (by decide)))

theorem fz2_66_13 : Fintype.card
    (fixedPoints (Q2.reps (⟨13, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨13, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 13 (by decide)))

theorem fz2_66_14 : Fintype.card
    (fixedPoints (Q2.reps (⟨14, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨14, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 14 (by decide)))

theorem fz2_66_15 : Fintype.card
    (fixedPoints (Q2.reps (⟨15, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨15, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 15 (by decide)))

theorem fz2_66_16 : Fintype.card
    (fixedPoints (Q2.reps (⟨16, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨16, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 16 (by decide)))

theorem fz2_66_17 : Fintype.card
    (fixedPoints (Q2.reps (⟨17, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨17, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 17 (by decide)))

theorem fz2_66_18 : Fintype.card
    (fixedPoints (Q2.reps (⟨18, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨18, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 18 (by decide)))

theorem fz2_66_20 : Fintype.card
    (fixedPoints (Q2.reps (⟨20, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨20, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 20 (by decide)))

theorem fz2_66_21 : Fintype.card
    (fixedPoints (Q2.reps (⟨21, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨21, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 21 (by decide)))

theorem fz2_66_22 : Fintype.card
    (fixedPoints (Q2.reps (⟨22, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨22, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 22 (by decide)))

theorem fz2_66_23 : Fintype.card
    (fixedPoints (Q2.reps (⟨23, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨23, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 23 (by decide)))

theorem fz2_66_24 : Fintype.card
    (fixedPoints (Q2.reps (⟨24, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨24, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 24 (by decide)))

theorem fz2_66_25 : Fintype.card
    (fixedPoints (Q2.reps (⟨25, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨25, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 25 (by decide)))

theorem fz2_66_26 : Fintype.card
    (fixedPoints (Q2.reps (⟨26, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨26, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 26 (by decide)))

theorem fz2_66_27 : Fintype.card
    (fixedPoints (Q2.reps (⟨27, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨27, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 27 (by decide)))

theorem fz2_66_28 : Fintype.card
    (fixedPoints (Q2.reps (⟨28, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨28, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 28 (by decide)))

theorem fz2_66_29 : Fintype.card
    (fixedPoints (Q2.reps (⟨29, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨29, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 29 (by decide)))

theorem fz2_66_31 : Fintype.card
    (fixedPoints (Q2.reps (⟨31, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨31, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 31 (by decide)))

theorem fz2_66_32 : Fintype.card
    (fixedPoints (Q2.reps (⟨32, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨32, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 32 (by decide)))

theorem fz2_66_33 : Fintype.card
    (fixedPoints (Q2.reps (⟨33, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨33, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 33 (by decide)))

theorem fz2_66_34 : Fintype.card
    (fixedPoints (Q2.reps (⟨34, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨34, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 34 (by decide)))

theorem fz2_66_36 : Fintype.card
    (fixedPoints (Q2.reps (⟨36, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨36, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 36 (by decide)))

theorem fz2_66_37 : Fintype.card
    (fixedPoints (Q2.reps (⟨37, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨37, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 37 (by decide)))

theorem fz2_66_38 : Fintype.card
    (fixedPoints (Q2.reps (⟨38, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨38, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 38 (by decide)))

theorem fz2_66_39 : Fintype.card
    (fixedPoints (Q2.reps (⟨39, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨39, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 39 (by decide)))

theorem fz2_66_41 : Fintype.card
    (fixedPoints (Q2.reps (⟨41, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨41, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 41 (by decide)))

theorem fz2_66_42 : Fintype.card
    (fixedPoints (Q2.reps (⟨42, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨42, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 42 (by decide)))

theorem fz2_66_43 : Fintype.card
    (fixedPoints (Q2.reps (⟨43, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨43, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 43 (by decide)))

theorem fz2_66_44 : Fintype.card
    (fixedPoints (Q2.reps (⟨44, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨44, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 44 (by decide)))

theorem fz2_66_46 : Fintype.card
    (fixedPoints (Q2.reps (⟨46, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨46, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 46 (by decide)))

theorem fz2_66_47 : Fintype.card
    (fixedPoints (Q2.reps (⟨47, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨47, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 47 (by decide)))

theorem fz2_66_48 : Fintype.card
    (fixedPoints (Q2.reps (⟨48, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨48, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 48 (by decide)))

theorem fz2_66_49 : Fintype.card
    (fixedPoints (Q2.reps (⟨49, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨49, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 49 (by decide)))

theorem fz2_66_51 : Fintype.card
    (fixedPoints (Q2.reps (⟨51, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨51, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 51 (by decide)))

theorem fz2_66_52 : Fintype.card
    (fixedPoints (Q2.reps (⟨52, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨52, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 52 (by decide)))

theorem fz2_66_53 : Fintype.card
    (fixedPoints (Q2.reps (⟨53, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨53, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 53 (by decide)))

theorem fz2_66_54 : Fintype.card
    (fixedPoints (Q2.reps (⟨54, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨54, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 54 (by decide)))

theorem fz2_66_55 : Fintype.card
    (fixedPoints (Q2.reps (⟨55, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨55, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 55 (by decide)))

theorem fz2_66_56 : Fintype.card
    (fixedPoints (Q2.reps (⟨56, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨56, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 56 (by decide)))

theorem fz2_66_57 : Fintype.card
    (fixedPoints (Q2.reps (⟨57, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨57, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 57 (by decide)))

theorem fz2_66_58 : Fintype.card
    (fixedPoints (Q2.reps (⟨58, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨58, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 58 (by decide)))

theorem fz2_66_59 : Fintype.card
    (fixedPoints (Q2.reps (⟨59, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨59, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 59 (by decide)))

theorem fz2_66_60 : Fintype.card
    (fixedPoints (Q2.reps (⟨60, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨60, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 60 (by decide)))

theorem fz2_66_61 : Fintype.card
    (fixedPoints (Q2.reps (⟨61, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨61, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 61 (by decide)))

theorem fz2_66_62 : Fintype.card
    (fixedPoints (Q2.reps (⟨62, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨62, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 62 (by decide)))

theorem fz2_66_63 : Fintype.card
    (fixedPoints (Q2.reps (⟨63, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨63, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 63 (by decide)))

theorem fz2_66_64 : Fintype.card
    (fixedPoints (Q2.reps (⟨64, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨64, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 64 (by decide)))

theorem fz2_66_65 : Fintype.card
    (fixedPoints (Q2.reps (⟨65, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨65, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 65 (by decide)))

theorem fz2_66_67 : Fintype.card
    (fixedPoints (Q2.reps (⟨67, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨67, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 67 (by decide)))

theorem fz2_66_68 : Fintype.card
    (fixedPoints (Q2.reps (⟨68, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨68, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 68 (by decide)))

theorem fz2_66_69 : Fintype.card
    (fixedPoints (Q2.reps (⟨69, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨69, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 69 (by decide)))

theorem fz2_66_70 : Fintype.card
    (fixedPoints (Q2.reps (⟨70, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨70, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 70 (by decide)))

theorem fz2_66_71 : Fintype.card
    (fixedPoints (Q2.reps (⟨71, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨71, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 71 (by decide)))

theorem fz2_66_72 : Fintype.card
    (fixedPoints (Q2.reps (⟨72, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨72, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 72 (by decide)))

theorem fz2_66_73 : Fintype.card
    (fixedPoints (Q2.reps (⟨73, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨73, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 73 (by decide)))

theorem fz2_66_74 : Fintype.card
    (fixedPoints (Q2.reps (⟨74, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨74, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 74 (by decide)))

theorem fz2_66_75 : Fintype.card
    (fixedPoints (Q2.reps (⟨75, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨75, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 75 (by decide)))

theorem fz2_66_76 : Fintype.card
    (fixedPoints (Q2.reps (⟨76, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨76, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 76 (by decide)))

theorem fz2_66_77 : Fintype.card
    (fixedPoints (Q2.reps (⟨77, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨77, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 77 (by decide)))

theorem fz2_66_78 : Fintype.card
    (fixedPoints (Q2.reps (⟨78, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨78, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 78 (by decide)))

theorem fz2_66_79 : Fintype.card
    (fixedPoints (Q2.reps (⟨79, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨79, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 79 (by decide)))

theorem fz2_66_80 : Fintype.card
    (fixedPoints (Q2.reps (⟨80, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨80, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 80 (by decide)))

theorem fz2_66_81 : Fintype.card
    (fixedPoints (Q2.reps (⟨81, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨81, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 81 (by decide)))

theorem fz2_66_82 : Fintype.card
    (fixedPoints (Q2.reps (⟨82, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨82, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 82 (by decide)))

theorem fz2_66_83 : Fintype.card
    (fixedPoints (Q2.reps (⟨83, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨83, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 83 (by decide)))

theorem fz2_66_84 : Fintype.card
    (fixedPoints (Q2.reps (⟨84, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨84, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 84 (by decide)))

theorem fz2_66_85 : Fintype.card
    (fixedPoints (Q2.reps (⟨85, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨85, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 85 (by decide)))

theorem fz2_66_86 : Fintype.card
    (fixedPoints (Q2.reps (⟨86, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨86, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 86 (by decide)))

theorem fz2_66_87 : Fintype.card
    (fixedPoints (Q2.reps (⟨87, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨87, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 87 (by decide)))

theorem fz2_66_88 : Fintype.card
    (fixedPoints (Q2.reps (⟨88, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨88, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 88 (by decide)))

theorem fz2_66_89 : Fintype.card
    (fixedPoints (Q2.reps (⟨89, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨89, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 89 (by decide)))

theorem fz2_66_90 : Fintype.card
    (fixedPoints (Q2.reps (⟨90, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨90, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 90 (by decide)))

theorem fz2_66_91 : Fintype.card
    (fixedPoints (Q2.reps (⟨91, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨91, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 91 (by decide)))

theorem fz2_66_92 : Fintype.card
    (fixedPoints (Q2.reps (⟨92, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨92, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 92 (by decide)))

theorem fz2_66_93 : Fintype.card
    (fixedPoints (Q2.reps (⟨93, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨93, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 93 (by decide)))

theorem fz2_66_94 : Fintype.card
    (fixedPoints (Q2.reps (⟨94, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨94, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 94 (by decide)))

theorem fz2_66_95 : Fintype.card
    (fixedPoints (Q2.reps (⟨95, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨95, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 95 (by decide)))

theorem fz2_66_96 : Fintype.card
    (fixedPoints (Q2.reps (⟨96, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨96, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 96 (by decide)))

theorem fz2_66_97 : Fintype.card
    (fixedPoints (Q2.reps (⟨97, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨97, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 97 (by decide)))

theorem fz2_66_98 : Fintype.card
    (fixedPoints (Q2.reps (⟨98, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨98, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 98 (by decide)))

theorem fz2_66_99 : Fintype.card
    (fixedPoints (Q2.reps (⟨99, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨99, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 99 (by decide)))

theorem fz2_66_100 : Fintype.card
    (fixedPoints (Q2.reps (⟨100, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨100, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 100 (by decide)))

theorem fz2_66_101 : Fintype.card
    (fixedPoints (Q2.reps (⟨101, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨101, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 101 (by decide)))

theorem fz2_66_102 : Fintype.card
    (fixedPoints (Q2.reps (⟨102, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨102, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 102 (by decide)))

theorem fz2_66_103 : Fintype.card
    (fixedPoints (Q2.reps (⟨103, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨103, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 103 (by decide)))

theorem fz2_66_104 : Fintype.card
    (fixedPoints (Q2.reps (⟨104, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨104, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 104 (by decide)))

theorem fz2_66_105 : Fintype.card
    (fixedPoints (Q2.reps (⟨105, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨105, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 105 (by decide)))

theorem fz2_66_106 : Fintype.card
    (fixedPoints (Q2.reps (⟨106, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨106, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 106 (by decide)))

theorem fz2_66_107 : Fintype.card
    (fixedPoints (Q2.reps (⟨107, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨107, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 107 (by decide)))

theorem fz2_66_108 : Fintype.card
    (fixedPoints (Q2.reps (⟨108, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨108, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 108 (by decide)))

theorem fz2_66_109 : Fintype.card
    (fixedPoints (Q2.reps (⟨109, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨109, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 109 (by decide)))

theorem fz2_66_110 : Fintype.card
    (fixedPoints (Q2.reps (⟨110, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨110, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 110 (by decide)))

theorem fz2_66_111 : Fintype.card
    (fixedPoints (Q2.reps (⟨111, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨111, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 111 (by decide)))

theorem fz2_66_112 : Fintype.card
    (fixedPoints (Q2.reps (⟨112, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨112, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 112 (by decide)))

theorem fz2_66_113 : Fintype.card
    (fixedPoints (Q2.reps (⟨113, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨113, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 113 (by decide)))

theorem fz2_66_114 : Fintype.card
    (fixedPoints (Q2.reps (⟨114, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨114, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 114 (by decide)))

theorem fz2_66_115 : Fintype.card
    (fixedPoints (Q2.reps (⟨115, by decide⟩ : Fin 148)) (Coordinate 2 ⧸ Q2.reps rK66)) = 0 :=
  Q2.repsFixedCard2 rK66 ⟨115, by decide⟩ Q2.R66_2 Q2.hpxR66_2 Q2.hcardq66_2
    (of_decide_eq_true ((List.all_eq_true.mp fixz2_66) 115 (by decide)))

end LeanDring.P5Presentation
